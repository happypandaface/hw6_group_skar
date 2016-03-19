#! /usr/bin/env python2.7

import sys
logs = sys.stderr
import traceback
#import compiler
#from compiler.ast import *
from ast import *
import copy


def prepend_stmts(ss, s):
    return ss + s

def append_stmts(s1, s2):
    return BranchStmt(prefix=s1, flow=s2)

# lhs : string, rhs : expr
def make_assign(lhs, rhs):
    return Assign(targets=[Name(id=lhs, flags='OP_ASSIGN')], value=rhs)

###############################################################################
# Simplify comparison and logic operators

# New Classes for the Intermediate Representation that
# provide a uniform representation for binary and unary operations

class PrimitiveOp(AST):
    def __init__(self, op, operands):
        self.op = op
        self.operands = operands
        self._fields = ["op", "operands"]

class Let(AST):
    def __init__(self, var, rhs, body):
        self.var = var
        self.rhs = rhs
        self.body = body
        self._fields = ["var", "rhs", "body"]


# the following counter is for generating unique names
counter = 0

def generate_name(x):
    global counter
    name = x + str(counter)
    counter = counter + 1
    return name

class_to_fun = {Add: 'add', Sub: 'sub', Mult: 'mul', Div: 'div',        
                USub: 'unary_sub', Not: 'logic_not',
                And: 'logic_and', Or: 'logic_or',
                Lt: 'less', Gt: 'greater', LtE: 'less_equal', GtE: 'greater_equal', 
                Eq: 'equal', NotEq: 'not_equal', Is: 'identical' } #TODO: add 'in' operator

# context is either 'expr' or 'lhs'
def simplify_ops(n, context='expr'):
    if isinstance(n, Module):
        return Module(body=map(simplify_ops, n.body))
    elif isinstance(n, Print):
        return Print(dest=n.dest, values=map(simplify_ops, n.values), nl=n.nl)
    elif isinstance(n, Expr):
        return Expr(value=simplify_ops(n.value))
    elif isinstance(n, If):
        return If(test=simplify_ops(n.test), body=[simplify_ops(s) for s in n.body],orelse=[simplify_ops(s) for s in n.orelse])
    elif isinstance(n, While):
        return While(test=simplify_ops(n.test), body=[simplify_ops(s) for s in n.body]) # no orelse
    elif isinstance(n, Assign):
        return Assign(targets=map(simplify_ops, n.targets), value=simplify_ops(n.value))
    elif n.__class__ in [Num, Name]:
        return n
    elif isinstance(n, UnaryOp): # - or Not
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, [n.operand]))
    elif isinstance(n, BinOp): # +, -, *
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, [n.left, n.right]))
    elif isinstance(n, BoolOp): # And, Or
        return PrimitiveOp(class_to_fun[n.op.__class__], map(simplify_ops, n.values))
    elif isinstance(n, IfExp):
        return IfExp(test=simplify_ops(n.test), body=simplify_ops(n.body), orelse=simplify_ops(n.orelse))
    elif isinstance(n, Compare):
        operands = map(simplify_ops, [n.left] + n.comparators) # left is the first operand!
        ops = map(lambda x: class_to_fun[x.__class__], n.ops)
        if len(ops) == 1:
            return PrimitiveOp(ops[0], operands)
        else: # 3<5>4 => 3<5 and 5>4
            return PrimitiveOp('logic_and', 
                               [PrimitiveOp(op, [x, y]) for op, x, y in zip(ops, operands, operands[1:])])
    elif isinstance(n, List):
        ls_name = generate_name('list')
        def gen_list(nodes, i):
            if len(nodes) == 0:
                return Name(id=ls_name)
            else:
                return Let('_', PrimitiveOp('assign',\
                                            [PrimitiveOp('deref',\
                                                         [PrimitiveOp('subscript',\
                                                                      [Name(id=ls_name), Num(n=i)])\
                                                          ]),\
                                             simplify_ops(nodes[0])]),\
                           gen_list(nodes[1:], i + 1))
        return Let(ls_name, PrimitiveOp('make_list', [Num(n=len(n.elts))]),\
                   gen_list(n.elts, 0))
    elif isinstance(n, Subscript): # Subscript(value=List(elts=[...]), slice=Index(value=Num(n=0)), ctx=Load()))
        return PrimitiveOp('deref', [PrimitiveOp('subscript', \
                                                 [simplify_ops(n.value), simplify_ops(n.slice.value)])])
    else:
        raise Exception('Error in simplify_ops: unrecognized AST node ' + repr(n))


###############################################################################
# Convert to static single-assignment form (SSA)

def union(a,b):
    return a | b

def assigned_vars(n):
    #if isinstance(n, Stmt):
        #return reduce(union, [assigned_vars(s) for s in n.nodes], set([]))
    if isinstance(n, Print):
        return set([])
    elif isinstance(n, Pass):
        return set([])
    elif isinstance(n, If):
        return (
            reduce(union, [assigned_vars(b) for b in n.body], set([]))
            | assigned_vars(n.orelse)
            | (
                reduce(union, [assigned_vars(s) for s in n.phis], set([]))
                if hasattr(n, 'phis') else set([])
            )
        )
    elif n == None:
        return set([])
    elif isinstance(n, Assign):
        return reduce(union, [assigned_vars(s) for s in n.targets], set([]))
    elif isinstance(n, Name):
        return set([n.id])
    elif isinstance(n, While):
        return reduce(union, [assigned_vars(s) for s in n.body], set([])) | (
            reduce(union, [assigned_vars(s) for s in n.phis], set([]))
            if hasattr(n, 'phis') else set([])
        )
    #elif isinstance(n, Discard):
    #    return set([])
    else:
        return set([])

highest_version = {}

def get_high(x):
    if x in highest_version:
        v = highest_version[x] + 1
        highest_version[x] = v
        return v
    else:
        highest_version[x] = 0
        return 0

def get_current(current_version, x):
    if x in current_version:
        return current_version[x]
    else:
        return 0

def convert_to_ssa(ast, current_version={}):
    if False:
        print >> logs, 'convert to ssa: ' + repr(ast)
    if isinstance(ast, Module):
        return Module(body=[convert_to_ssa(s, current_version) for s in ast.body])

    #elif isinstance(ast, Function):
    #    ast.code = convert_to_ssa(ast.code)
    #    return ast

    #elif isinstance(ast, CallFunc):
    #    return ast

    #elif isinstance(ast, Stmt):
    #    return Stmt([convert_to_ssa(s, current_version) for s in ast.nodes])

    elif isinstance(ast, Print):
        return Print(
            ast.dest,[convert_to_ssa(e, current_version) for e in ast.values], ast.nl
        )
       
    elif isinstance(ast, Expr):
        return ast
    elif isinstance(ast, Pass):
        return ast

    #elif isinstance(ast, Discard):
    #    return Discard(convert_to_ssa(ast.expr, current_version))
    
    elif isinstance(ast, If):
        new_test = convert_to_ssa(ast.test, current_version)
        new_body = []
        for s in ast.body:
            body_cv = copy.deepcopy(current_version)
            temp_body = convert_to_ssa(s,body_cv)
            new_body.append((temp_body, body_cv))
        orelse_cv = copy.deepcopy(current_version)
        new_orelse = [convert_to_ssa(s, orelse_cv) for s in ast.orelse]

        assigned = (
            reduce(union, [assigned_vars(b) for b in ast.body], set([]))
            | assigned_vars(ast.orelse)
        )

        phis = []
        for x in assigned:
            current_version[x] = get_high(x)
            phi_rhs = [
                Name(id=(x + '_' + str(get_current(cv, x)))) for _,cv in new_body
            ]
            phi_rhs.append(Name(id=(x + '_' + str(get_current(orelse_cv, x)))))
            phi = make_assign(
                x + '_' + str(get_current(current_version, x)),
                PrimitiveOp('phi', phi_rhs)
            )
            phis.append(phi)

        ret = If(test=new_test,body=[b for b,_ in new_body], orelse=new_orelse)
        ret.phis = phis
        return ret

    elif isinstance(ast, While):
        pre_cv = copy.deepcopy(current_version)
        #pre = Stmt(nodes=[])

        if debug:
            print >> logs, 'convert to ssa While ', dump(ast.test)
        assigned = []
        for s in ast.body:
            assigned += assigned_vars(s)
        if debug:
            print >> logs, 'assigned = ', assigned
        for x in assigned:
            current_version[x] = get_high(x)

        body_cv = copy.deepcopy(current_version)
        new_body = [convert_to_ssa(s, body_cv) for s in ast.body]

        new_test = convert_to_ssa(ast.test, current_version)

        phis = []
        for x in assigned:
            body_var = Name(id=(x + '_' + str(get_current(body_cv, x))),ctx=Store())
            pre_var = Name(id=(x + '_' + str(get_current(pre_cv, x))),ctx=Store())
            phi = make_assign(x + '_' + str(get_current(current_version, x)),\
                              PrimitiveOp('phi', [pre_var,body_var]))
            phis.append(phi)


        ret = While(test=new_test, body=new_body, else_=None)
        ret.phis = phis
        return ret

    elif isinstance(ast, Assign):
        new_rhs = convert_to_ssa(ast.value, current_version)
        new_nodes = []
        for n in ast.targets:
            if isinstance(n, Name):
                x = n.id
                x_v = get_high(x)
                current_version[x] = x_v
                new_nodes.append(
                    Name(id=(x + '_' + str(x_v)), ctx=n.ctx)
                )
            else:
                new_nodes.append(convert_to_ssa(n, current_version))

        return Assign(targets=new_nodes, value=new_rhs)

    elif ast == None:
        return None

    elif isinstance(ast, Num):
        return ast

    elif isinstance(ast, Name):
        if ast.id == 'True' or ast.id == 'False':
            return ast
        else:
            return Name(
                id=ast.id + '_' + str(get_current(current_version, ast.id))
            )

    elif isinstance(ast, PrimitiveOp):
        nodes = [convert_to_ssa(e, current_version) for e in ast.operands]
        return PrimitiveOp(ast.op, nodes)

    elif isinstance(ast, IfExp):
        new_test = convert_to_ssa(ast.test, current_version)
        new_orelse = convert_to_ssa(ast.orelse, current_version)
        new_body = convert_to_ssa(ast.body, current_version)
        return IfExp(test=new_test, orelse=new_orelse, body=new_body)

    elif isinstance(ast, Let):
        rhs = convert_to_ssa(ast.rhs, current_version)
        v = get_high(ast.var)
        current_version[ast.var] = v
        body = convert_to_ssa(ast.body, current_version)
        return Let(ast.var + '_' + str(v), rhs, body)

    else:
        raise Exception(
            'Error in convert_to_ssa: unrecognized AST node ' + repr(ast)
        )


###############################################################################
# Insert variable declarations

class VarDecl(AST):
    def __init__(self, name, type, lineno=None):
        self.name = name
        self.type = type
        self.lineno = lineno
        self._fields = ["name", "type","lineno"]

def insert_var_decls(n):
    if isinstance(n, Module):
        decls = []
        for s in n.body:
            decls += [VarDecl(x,'undefined') for x in assigned_vars(s)]
        return Module(body=prepend_stmts(decls, n.body))
    else:
        raise Exception('Error in insert_var_decls: unhandled AST ' + repr(n))

###############################################################################
# Type analysis, this pass annotates the IR in-place with types in the 'type'
# attribute

def join(t1,t2):
    if t1 == 'pyobj':
        return 'pyobj'
    elif t2 == 'pyobj':
        return 'pyobj'
    elif t1 == 'undefined':
        return t2
    elif t2 == 'undefined':
        return t1
    elif t1 == t2:
        return t1
    else:
        return 'pyobj'

arith_returns = {
    'int' : 'int',
    'float' : 'float',
    'pyobj' : 'pyobj',
    'undefined' : 'undefined'
    }


arith_op = {
        ('int',   'int')   : 'int' ,
        ('int',   'float') : 'float' ,
        ('int',   'bool')  : 'int' ,
        ('int',   'pyobj')  : 'pyobj' ,
        ('int',   'undefined')  : 'undefined' ,
        ('float', 'int')   : 'float' ,
        ('float', 'float') : 'float' ,
        ('float', 'bool')  : 'float' ,
        ('float', 'pyobj')  : 'pyobj' ,
        ('float', 'undefined')  : 'undefined' ,
        ('bool',  'int')   : 'int' ,
        ('bool',  'float') : 'float' ,
        ('bool',  'bool')  : 'int',
        ('bool',  'pyobj')  : 'pyobj',
        ('bool',  'undefined')  : 'undefined',
        ('pyobj',   'int')   : 'pyobj' ,
        ('pyobj',   'float') : 'pyobj' ,
        ('pyobj',   'bool')  : 'pyobj' ,
        ('pyobj',   'pyobj')  : 'pyobj',
        ('pyobj',   'undefined')  : 'undefined',
        ('undefined',   'int')   : 'undefined' ,
        ('undefined',   'float') : 'undefined' ,
        ('undefined',   'bool')  : 'undefined' ,
        ('undefined',   'pyobj')  : 'undefined' ,
        ('undefined',   'undefined')  : 'undefined',
        ('pyobj',)  : 'pyobj',
        ('undefined',)  : 'undefined',
        ('int',)  : 'int',
        ('float',)  : 'float',
        ('bool',)  : 'int'
        }

bool_returns = {
    'int' : 'bool',
    'float' : 'bool',
    'pyobj' : 'bool',
    'bool' : 'bool',
    'undefined' : 'bool'
}

bool_op = {
        ('int',   'int')   : 'int' ,
        ('int',   'float') : 'float' ,
        ('int',   'bool')  : 'int' ,
        ('int',   'pyobj')  : 'pyobj' ,
        ('int',   'undefined')  : 'undefined' ,
        ('float', 'int')   : 'float' ,
        ('float', 'float') : 'float' ,
        ('float', 'bool')  : 'float' ,
        ('float', 'pyobj')  : 'pyobj' ,
        ('float', 'undefined')  : 'undefined' ,
        ('bool',  'int')   : 'int' ,
        ('bool',  'float') : 'float' ,
        ('bool',  'bool')  : 'bool',
        ('bool',  'pyobj')  : 'pyobj',
        ('bool',  'undefined')  : 'undefined',
        ('pyobj',   'int')   : 'pyobj' ,
        ('pyobj',   'float') : 'pyobj' ,
        ('pyobj',   'bool')  : 'pyobj' ,
        ('pyobj',   'undefined')  : 'undefined',
        ('pyobj',   'pyobj')  : 'pyobj',
        ('undefined',   'int')   : 'undefined' ,
        ('undefined',   'float') : 'undefined' ,
        ('undefined',   'bool')  : 'undefined' ,
        ('undefined',   'pyobj')  : 'undefined',
        ('undefined',   'undefined')  : 'undefined',
        ('undefined',)  : 'undefined',
        ('pyobj',)  : 'pyobj',
        ('int',)  : 'int',
        ('float',)  : 'float',
        ('bool',)  : 'bool'
        }

arithop = (lambda ts: arith_op[ts])
boolop = (lambda ts: bool_op[ts])
def idop(ts):
    if ts[0] == ts[1]:
        return ts[0]
    else:
        return 'pyobj'

find_op_tag = {
    'add' : arithop,
    'sub' : arithop,
    'mul' : arithop,
    'div' : arithop,
    'unary_add' : arithop,
    'unary_sub' : arithop,
    'logic_not' : boolop,
    'logic_and' : boolop,
    'logic_or' : boolop,
    'equal' : boolop,
    'not_equal' : boolop,
    'less' : boolop,
    'less_equal' : boolop,
    'greater' : boolop,
    'greater_equal' : boolop,
    'identical' : idop,
    'deref' : (lambda ts: ''),
    'subscript' : (lambda ts: 'pyobj'),
    'make_list' : (lambda ts: ''),
    'assign' : (lambda ts: reduce(join, ts, 'undefined')),
    'phi' : (lambda ts: reduce(join, ts, 'undefined')),
		'in_comp' : boolop
}

arith_ret = (lambda ts: arith_returns[arith_op[ts]])
bool_ret = (lambda ts: bool_returns[bool_op[ts]])

op_returns = {
    'add' : arith_ret,
    'sub' : arith_ret,
    'mul' : arith_ret,
    'div' : arith_ret,
    'unary_add' : arith_ret,
    'unary_sub' : arith_ret,
    'logic_not' : bool_ret,
    'logic_and' : bool_ret,
    'logic_or' : bool_ret,
    'equal' : bool_ret,
    'not_equal' : bool_ret,
    'less' : bool_ret,
    'less_equal' : bool_ret,
    'greater' : bool_ret,
    'greater_equal' : bool_ret,
    'identical' : bool_ret,
    'deref' : (lambda ts: 'pyobj'),
    'subscript' : (lambda ts: 'pyobj'),
    'make_list' : (lambda ts: 'pyobj'),
    'assign' : (lambda ts: reduce(join, ts, 'undefined')),
    'phi' : (lambda ts: reduce(join, ts, 'undefined')),
		'in_comp' : bool_ret
    }

type_changed = False

def get_var_type(env, x):
    if x in env:
        return env[x]
    else:
        return 'undefined'

# Don't need to do a join in update_var_type because the program
# is in SSA form. There is only one assignment to each variable.
def update_var_type(env, x, t):
    if x in env:
        if t == env[x]:
            return False
        else:
            env[x] = t
            return True
    else:
        env[x] = t
        return True

def predict_type(n, env):
    global type_changed
    
    if isinstance(n, Module):
        type_changed = True
        while type_changed:
            type_changed = False
            for s in n.body:
                predict_type(s, env)

    #elif isinstance(n, Function):
    #    predict_type(n.code,env)

    #elif isinstance(n, CallFunc):
    #    pass#predict_type(n.code,env)

    #elif isinstance(n, Stmt):
    #    for s in n.nodes:
    #        predict_type(s, env)

    elif isinstance(n, Print):
        for e in n.values:
            predict_type(e, env)

    #elif isinstance(n, Discard):
    #    predict_type(n.expr, env)

    elif isinstance(n, If):
        predict_type(n.test,env)
        for s in n.body:
            predict_type(s,env)
        for s in n.orelse:
            predict_type(s,env)
        for s in n.phis:
            predict_type(s,env)

    elif n == None:
        pass

    elif isinstance(n, While):
        predict_type(n.test,env)
        for s in n.body:
            predict_type(s,env)
        for s in n.phis:
            predict_type(s,env)

    elif isinstance(n, Pass):
        pass

    elif isinstance(n, Assign):
        predict_type(n.value, env)
        for a in n.targets:
            if isinstance(a, Name):
                type_changed += update_var_type(env, a.id, n.value.type)
                a.type = get_var_type(env, a.id)
            else:
                predict_type(a, env)

    elif isinstance(n, VarDecl):
        n.type = get_var_type(env, n.name)

    elif isinstance(n, Num):
        if isinstance(n.n, float):
            n.type = 'float'
        elif isinstance(n.n, int):
            n.type = 'int'
        else:
            raise Exception(
                'Error in predict_type: unhandled constant ' + repr(n)
            )

    elif isinstance(n, Name):
        if n.id == 'True' or n.id == 'False':
            n.type = 'bool'
        else:
            n.type = get_var_type(env, n.id)

    elif isinstance(n, PrimitiveOp):
        for e in n.operands:
            predict_type(e, env)
        typerun = e.type
        for e in n.operands[1:]:
            typerun = op_returns[n.op](tuple([typerun,e.type]))
        n.type = typerun

    elif isinstance(n, IfExp):
        predict_type(n.test, env)
        predict_type(n.body, env)
        predict_type(n.orelse, env)
        if n.body.type == n.orelse.type:
            n.type = n.body.type
        else:
            n.type = 'pyobj'

    elif isinstance(n, Let):
        predict_type(n.rhs, env)
        body_env = copy.deepcopy(env)
        update_var_type(body_env, n.var, n.rhs.type)
        predict_type(n.body, body_env)
        n.type = n.body.type

    else:
        raise Exception(
            'Error in predict_type: unrecognized AST node ' + repr(n)
        )

###############################################################################
# Type specialization
#   select specialized primitive operations
#   insert calls to is_true and make_* where appropriate

def convert_to_pyobj(e):
    if e.type != 'pyobj' and e.type != 'undefined':
        new_e = PrimitiveOp(e.type + '_to_pyobj', [e])
        new_e.type = 'pyobj'
        return new_e
    else:
        return e

def test_is_true(e):
    if e.type == 'pyobj':
        ret = PrimitiveOp('pyobj_to_bool', [e])
        ret.type = 'bool'
        return ret
    else:
        return e

def type_specialize(n):
    #print >> logs, 'type specialize ' + repr(n)
    if isinstance(n, Module):
        return Module(body=[type_specialize(s) for s in n.body])
    #elif isinstance(n, Function):
    #    n.code=type_specialize(n.code)
    #    return n
    #elif isinstance(n, CallFunc):
    #    return n
    #elif isinstance(n, Stmt):
    #    return Stmt([type_specialize(s) for s in n.nodes])
    elif isinstance(n, Print):
        # would be nice to specialize print, but not a high priority
        return Print(
            n.dest,
            [convert_to_pyobj(type_specialize(e)) for e in n.values],
            n.nl
        )
    #elif isinstance(n, Discard):
    #    return Discard(type_specialize(n.expr))
    elif isinstance(n, If):
        test = test_is_true(type_specialize(n.test))
        body = [type_specialize(s) for s in n.body]
        orelse = [type_specialize(s) for s in n.orelse]
        phis = [type_specialize(s) for s in n.phis]
        ret = If(test,body,orelse)
        ret.phis = phis
        return ret
    elif n == None:
        return None
    elif isinstance(n, While):
        test = test_is_true(type_specialize(n.test))
        body = [type_specialize(s) for s in n.body]
        phis = [type_specialize(s) for s in n.phis]
        ret = While(test, body, None)
        ret.phis = phis
        return ret
    elif isinstance(n, Pass):
        return n
    elif isinstance(n, Assign):
        value = type_specialize(n.value)
        targets = [type_specialize(a) for a in n.targets]
        if any([a.type == 'pyobj' for a in targets]):
            value = convert_to_pyobj(value)
        return Assign(targets, value)

    elif isinstance(n, Name):
        return n

    elif isinstance(n, VarDecl):
        return n

    elif isinstance(n, Num):
        return n
    elif isinstance(n, Name):
        return n
    elif isinstance(n, PrimitiveOp):
        operands = [type_specialize(e) for e in n.operands]
        tag = find_op_tag[n.op](tuple([e.type for e in n.operands[:2]]))
        #if any([e.type == 'pyobj' for e in nodes]):
        if tag == 'pyobj':
            operands = [convert_to_pyobj(e) for e in operands]
        op= n.op if tag == '' else n.op + '_' + tag
        r = PrimitiveOp(op, operands)
        r.type = n.type
        return r
    elif isinstance(n, IfExp):
        test = type_specialize(n.test)
        body = type_specialize(n.body)
        orelse = type_specialize(n.orelse)
        test = test_is_true(test)
        if any([e.type == 'pyobj' for e in [n,body,orelse]]):
            body = convert_to_pyobj(body)
            orelse = convert_to_pyobj(orelse)
        r = IfExp(test, body, orelse)
        r.type = n.type
        return r
    elif isinstance(n, Let):
        rhs = type_specialize(n.rhs)
        body = type_specialize(n.body)
        r = Let(n.var, rhs, body)
        r.type = n.type
        return r
    else:
        raise Exception(
            'Error in type_specialize: unrecognized AST node ' + repr(n)
        )


###############################################################################
# Remove SSA

class BranchStmt(AST):
    def __init__(self, prefix, flow):
        self.prefix = prefix
        self.flow = flow
        self._fields = ["prefix", "flow"]

def split_phis(phis):
    branch_dict = {}
    for phi in phis:
        lhs = phi.targets[0].id
        i = 0
        for rhs in phi.value.operands:
            if i in branch_dict:
                branch_dict[i].append(make_assign(lhs, rhs))
            else:
                branch_dict[i] = [make_assign(lhs, rhs)]
            i = i + 1
    return branch_dict

def remove_ssa(n):
    if isinstance(n, Module):
        return Module(body=[remove_ssa(s) for s in n.body])
    #elif isinstance(n, Function):
    #    n.code=remove_ssa(n.code)
    #    return n
    #elif isinstance(n, Stmt):
    #    return Stmt([remove_ssa(s) for s in n.nodes])
    elif isinstance(n, Print):
        return n
    #elif isinstance(n, Discard):
    #    return n
    elif isinstance(n, If):
        body = [remove_ssa(s) for s in n.body]
        orelse = [remove_ssa(s) for s in n.orelse]
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa If '
            print >> logs, 'branch dict: ', branch_dict
        b = 0
        new_body = []
        for s in body:
            new_body += [s]
            if 0 < len(branch_dict):
                new_body += branch_dict[b]
            b = b + 1
        new_orelse = orelse
        if 0 < len(branch_dict):
            new_orelse += branch_dict[b]
        ret = If(n.test, new_body, new_orelse)
        return ret
    elif n == None:
        return None
    elif isinstance(n, While):
        test = n.test
        body = [remove_ssa(s) for s in n.body]
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa While ', map(dump,phis), dump(branch_dict[0][0]), dump(branch_dict[1][0])
        if 0 < len(branch_dict):
            ret = BranchStmt(prefix=branch_dict[0], flow=While(test, body + branch_dict[1], None))
        else:
            ret = While(test, body, None)
        return ret
    elif isinstance(n, Pass):
        return n
    elif isinstance(n, Assign):
        return Assign(n.targets, n.value)
    elif isinstance(n, VarDecl):
        return n
    else:
        raise Exception(
            'Error in remove_ssa: unrecognized AST node ' + repr(n)
        )


###############################################################################
# Generate C output

python_type_to_c = {
    'int' : 'int', 'bool' : 'char', 'float' : 'double', 'pyobj' : 'pyobj',
    'undefined' : 'pyobj'
}

skeleton = open("skeleton.c").readlines()

functions=[] # added so that we can define functions before main

def generate_c(n):
    global functions
    if isinstance(n, Module):
        # all the support functions
        # the functions we found
        # int main() {
        # main body 
        # return 0;}
        return \
            "".join(skeleton[:-3]) +\
            "\n".join(functions) +\
            "".join(skeleton[-3:-2]) +\
            "\n".join([generate_c(s) for s in n.body])+\
            "".join(skeleton[-2:])
    #elif isinstance(n, Function):
    #   functions.append("void "+n.name+"(){\n"+generate_c(n.code)+"\n}")
    #    return ""
    #elif isinstance(n, CallFunc):
    #    return n.node.name+"()"
    #elif isinstance(n, Stmt):
    #    return '{' + '\n'.join([generate_c(e) for e in n.nodes]) + '}'
    elif isinstance(n, Print):
        space = 'printf(\" \");'
        newline = 'printf(\"\\n\");'
        nodes_in_c = [
            'print_%s(%s);' % (x.type, generate_c(x)) for x in n.values
        ]
        return space.join(nodes_in_c) + newline
    #elif isinstance(n, Discard):
    #    return generate_c(n.expr) + ';'
    elif isinstance(n, If):
        if n.orelse == None:
            orelse = ''
        else:
            orelse = 'else{\n' + '\n'.join(['%s' % generate_c(s) for s in n.orelse]) + '}'
            body = '\n'.join(['%s' % generate_c(s) for s in n.body])
        return 'if ' + '(%s){\n' % generate_c(n.test) + body + '}' + \
            '\n' + orelse + '\n'
    elif isinstance(n, While):
        return 'while (%s){\n%s}' % (generate_c(n.test), '\n'.join([generate_c(s) for s in n.body]))
    elif isinstance(n, Pass):
        return ';'
    elif isinstance(n, Assign):
        return '='.join([generate_c(v) for v in n.targets]) \
               + ' = ' + generate_c(n.value) + ';'
    elif isinstance(n, VarDecl):
        return '%s %s;' % (python_type_to_c[n.type], n.name)

    elif isinstance(n, Num):
        return repr(n.n)
    elif isinstance(n, Name):
        if n.id == 'True':
            return '1'
        elif n.id == 'False':
            return '0'
        else:
            return n.id
    elif isinstance(n, PrimitiveOp):
        if n.op == 'deref':
            return '*' + generate_c(n.operands[0])
        elif n.op in (
                'assign_pyobj', 'assign_int', 'assign_bool', 'assign_float'):
            return (
                '('
                + generate_c(n.operands[0]) + '=' + generate_c(n.operands[1])
                + ')'
            )
        elif n.op[-9:] == '_to_pyobj' or n.op in(
                'unary_sub_int','unary_add_op','logic_not_bool'):
            return (
                n.op + '('
                + ', '.join([generate_c(e) for e in n.operands])
                + ')'
            )
        else:
            nest = ''
            opencount = 0
            for e in n.operands[:-1]:
                nest += n.op + '(' + generate_c(e) + ','
                opencount += 1
            nest += generate_c(n.operands[-1]) + opencount*')'
            return nest
    elif isinstance(n, IfExp):
        return '(' + generate_c(n.test) + ' ? ' \
               + generate_c(n.body) + ':' + generate_c(n.orelse) + ')'
    elif isinstance(n, Let):
        t = python_type_to_c[n.rhs.type]
        rhs = generate_c(n.rhs)
        return (
            '({ '
            + t + ' ' + n.var + ' = ' + rhs + '; ' + generate_c(n.body)
            + ';})'
        )
    elif isinstance(n, BranchStmt):
        return "\n".join([generate_c(s) for s in n.prefix]) +"\n" + generate_c(n.flow)
    elif n == None:
        return ''
    else:
        raise Exception(
            'Error in generate_c: unrecognized AST node ' + repr(n)
        )

######################### MAIN ##################################

if __name__ == "__main__":
    
    debug = not any(arg == '-q' for arg in sys.argv[1:])

    try:
        ast = parse("".join(sys.stdin.readlines()))
        if debug:
            print >> logs, dump(ast)
            print >> logs, 'simplifying ops --------------'
        ir = simplify_ops(ast)
        if debug:
            print >> logs, dump(ir)
            print >> logs, 'converting to ssa -----------'
        ir = convert_to_ssa(ir)
        if debug:
            print >> logs, dump(ir)
            print >> logs, 'inserting var decls ---------'
        ir = insert_var_decls(ir)
        if debug:
            print >> logs, dump(ir)
            print >> logs, 'predicting types -----------'
        predict_type(ir, {})
        if debug:
            print >> logs, dump(ir)
            print >> logs, 'type specialization -------'
            print >> logs, dump(ir)
        ir = type_specialize(ir)
        if debug:
            print >> logs, 'remove ssa ----------------'
            print >> logs, dump(ir)
        ir = remove_ssa(ir)
        if debug:
            print >> logs, 'finished remove ssa ------'
            print >> logs, dump(ir)
            print >> logs, 'generating C'
        print generate_c(ir)
    except EOFError:
        print "Could not open file %s." % sys.argv[1]
