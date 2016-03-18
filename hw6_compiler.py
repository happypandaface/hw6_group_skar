#! /usr/bin/env python

import ast
import sys
import traceback
import copy
from ast import *
from sys import stderr as logs

# lhs : string, rhs : expr
def make_assign(lhs, rhs):
    return Assign(nodes=[Name(name=lhs, flags='OP_ASSIGN')], expr=rhs)

###############################################################################
# Simplify comparison and logic operators

# New Classes for the Intermediate Representation that
# provide a uniform representation for binary and unary operations

class PrimitiveOp(AST):
    def __init__(self, name, nodes, lineno=None):
        self.name = name
        self.nodes = nodes
        self.lineno = lineno

    def getChildren(self):
        return self.nodes

    def getChildNodes(self):
        return self.nodes

    def __repr__(self):
        return ("PrimitiveOp(%s, %s)"
            % (self.name, ', '.join([repr(e) for e in self.nodes])))

class Let(AST):
    def __init__(self, var, rhs, body, lineno=None):
        self.var = var
        self.rhs = rhs
        self.body = body
        self.lineno = lineno

    def getChildren(self):
        return self.rhs, self.body

    def getChildNodes(self):
        return self.rhs, self.body

    def __repr__(self):
        return ("Let(%s, %s, %s)"
            % (repr(self.var), repr(self.rhs), repr(self.body)))


# the following counter is for generating unique names
counter = 0

def generate_name(x):
    global counter
    name = x + str(counter)
    counter = counter + 1
    return name

binary_op_classes = [Add, Sub, Mult, Div]
unary_op_classes = [UAdd, USub, Not]

class_to_fun = {
    Add: 'add', Sub: 'sub', Mult: 'mul', Div: 'div', UAdd: 'unary_add',
    USub: 'unary_sub', Not: 'logic_not'
}

compare_to_fun = {
    '<': 'less', '>': 'greater', '<=': 'less_equal', '>=': 'greater_equal',
    '==': 'equal', '!=': 'not_equal', 'is': 'identical', 'in':'in_comp'
}

# context is either 'expr' or 'lhs'
def simplify_ops(n, context='expr'):
    if isinstance(n, Module):
        node = simplify_ops(n.body)
        return Module(node)
    elif isinstance(n, FunctionDef):
        n.code = simplify_ops(n.code)
        return n
    elif isinstance(n, Call):
        return n
    elif isinstance(n, list):
        return [simplify_ops(s) for s in n]
    elif isinstance(n, Print):
        return Print(n.dest, [simplify_ops(e) for e in n.values], True)
    elif isinstance(n, If):
        tests = [
            (simplify_ops(cond), simplify_ops(body)) for (cond,body) in n.tests
        ]
        else_ = simplify_ops(n.else_)
        return If(tests, else_)
    elif n == None: # to handle when an If's else_ clause is not there
        return None

    elif isinstance(n, While):
        test = simplify_ops(n.test)
        body = simplify_ops(n.body)
        if n.else_ == None:
            return While(test, body, None)
        else:
            else_ = simplify_ops(n.else_)
            tmp = generate_name('tmp')
            return Stmt([make_sssign(tmp, test),
                         If(Name(tmp), While(Name(tmp), body, None), else_)])
    elif isinstance(n, Pass):
        return n
    elif isinstance(n, Assign):
        expr = simplify_ops(n.value, 'lhs')
        return Assign([simplify_ops(a) for a in n.targets], expr)

    elif isinstance(n, Name):
        return n
    elif isinstance(n, Num):
        return n
    elif isinstance(n, Name):
        return n
    elif n.__class__ in binary_op_classes:
        name = class_to_fun[n.__class__]
        left = simplify_ops(n.left)
        l_name = generate_name('left')
        right = simplify_ops(n.right)
        return Let(l_name, left, PrimitiveOp(name, [Name(l_name), right]))

    elif n.__class__ in unary_op_classes:
        return PrimitiveOp(class_to_fun[n.__class__], [simplify_ops(n.expr)])

    elif isinstance(n, And):
        nodes = [simplify_ops(e) for e in n.nodes]
        r = nodes[len(nodes)-1]
        for child in reversed(nodes[0:len(nodes)-1]):
            var = Name(generate_name('tmp'))
            r = Let(var.name, child, IfExp(var, r, var))
        return r

    elif isinstance(n, Or):
        nodes = [simplify_ops(e) for e in n.nodes]
        r = nodes[len(nodes)-1]
        for child in reversed(nodes[0:len(nodes)-1]):
            var = Name(generate_name('tmp'))
            r = Let(var.name, child, IfExp(var, var, r))
        return r

    elif isinstance(n, IfExp):
        return IfExp(
            simplify_ops(n.test), simplify_ops(n.then), simplify_ops(n.else_))

    elif isinstance(n, Compare):
        def gen_compare(lhs, ops, comps):
            if len(ops) == 1:
                op, rhs = ops[0], comps[0]
                return PrimitiveOp(
                    compare_to_fun[op], [lhs, simplify_ops(rhs)]
                )
            elif len(ops) > 1:
                op, rhs = ops[0], comps[0]
                rhs_var = Name(generate_name('tmp'))
                return Let(
                    rhs_var.name, simplify_ops(rhs),
                    PrimitiveOp(
                        'logic_and',
                        [
                            PrimitiveOp(compare_to_fun[op], [lhs, rhs_var]),
                            gen_compare(rhs_var, ops[1:], comps[1:])
                        ]
                    )
                )
            else:
                print >> logs, "error in gen_compare: zero length ops"

        lhs_var = Name(generate_name('tmp'), Load())
        return Let(
            lhs_var.id, simplify_ops(n.left),
            gen_compare(lhs_var, n.ops, n.comparators)
        )

    elif isinstance(n, List):
        ls_name = generate_name('list')
        def gen_list(nodes, i):
            if len(nodes) == 0:
                return Name(ls_name, Load())
            else:
                return Let(
                    '_',
                    PrimitiveOp('assign', [
                        PrimitiveOp('deref', [
                            PrimitiveOp('subscript', [
                                Name(ls_name, Load()), Num(i)
                            ])
                        ]),
                        simplify_ops(nodes[0])
                    ]),
                    gen_list(nodes[1:], i + 1)
                )
        return Let(ls_name, PrimitiveOp('make_list', [Num(len(n.elts))]),
                   gen_list(n.elts, 0))

    elif isinstance(n, Subscript):
        return PrimitiveOp('deref', [
            PrimitiveOp('subscript', [
                simplify_ops(n.expr), simplify_ops(n.subs[0])
            ])
        ])
    else:
        raise Exception(
            'Error in simplify_ops: unrecognized AST node ' + repr(n)
        )


###############################################################################
# Convert to static single-assignment form (SSA)

def union(a,b):
    return a | b

def assigned_vars(n):
    if isinstance(n, list):
        return reduce(union, [assigned_vars(s) for s in n], set([]))
    elif isinstance(n, Print):
        return set([])
    elif isinstance(n, Pass):
        return set([])
    elif isinstance(n, If):
        return (
            reduce(union, [assigned_vars(b) for (c,b) in n.tests], set([]))
            | assigned_vars(n.else_)
            | (
                reduce(union, [assigned_vars(s) for s in n.phis], set([]))
                if hasattr(n, 'phis') else set([])
            )
        )
    elif n == None:
        return set([])
    elif isinstance(n, Assign):
        return reduce(union, [assigned_vars(n) for n in n.nodes], set([]))
    elif isinstance(n, Name):
        return set([n.id])
    elif isinstance(n, While):
        return assigned_vars(n.body) | (
            reduce(union, [assigned_vars(s) for s in n.phis], set([]))
            if hasattr(n, 'phis') else set([])
        )
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
        return Module(node=convert_to_ssa(ast.body, {}))

    elif isinstance(ast, FunctionDef):
        ast.code = convert_to_ssa(ast.code)
        return ast

    elif isinstance(ast, Call):
        return ast

    elif isinstance(ast, list):
        return [convert_to_ssa(s, current_version) for s in ast]

    elif isinstance(ast, Print):
        return Print(
            ast.dest,
            [convert_to_ssa(e, current_version) for e in ast.values],
            True
        )

    elif isinstance(ast, Pass):
        return ast

    elif isinstance(ast, If):
        new_tests = []
        for (cond,body) in ast.tests:
            new_cond = convert_to_ssa(cond, current_version)
            body_cv = copy.deepcopy(current_version)
            new_body = convert_to_ssa(body, body_cv)
            new_tests.append((new_cond, new_body, body_cv))

        else_cv = copy.deepcopy(current_version)
        new_else = convert_to_ssa(ast.else_, else_cv)

        assigned = (
            reduce(union, [assigned_vars(b) for (c,b) in ast.tests], set([]))
            | assigned_vars(ast.else_)
        )

        phis = []
        for x in assigned:
            current_version[x] = get_high(x)
            phi_rhs = [
                Name(x + '_' + str(get_current(cv, x))) for _,_,cv in new_tests
            ]
            phi_rhs.append(Name(x + '_' + str(get_current(else_cv, x))))
            phi = make_assign(
                x + '_' + str(get_current(current_version, x)),
                PrimitiveOp('phi', phi_rhs)
            )
            phis.append(phi)

        ret = If(tests=[(c,b) for (c,b,_) in new_tests], else_=new_else)
        ret.phis = phis
        return ret

    elif isinstance(ast, While):
        pre_cv = copy.deepcopy(current_version)
        pre = []

        if debug:
            print >> logs, 'convert to ssa While ', ast.test
        assigned = assigned_vars(ast.body)
        if debug:
            print >> logs, 'assigned = ', assigned
        for x in assigned:
            current_version[x] = get_high(x)

        body_cv = copy.deepcopy(current_version)
        new_body = convert_to_ssa(ast.body, body_cv)

        new_test = convert_to_ssa(ast.test, current_version)

        phis = []
        for x in assigned:
            body_var = Name(x + '_' + str(get_current(body_cv, x)))
            pre_var = Name(x + '_' + str(get_current(pre_cv, x)))
            phi = make_assign(x + '_' + str(get_current(current_version, x)),
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

        return Assign(expr=new_rhs, nodes=new_nodes)

    elif ast == None:
        return None

    elif isinstance(ast, Num):
        return ast

    elif isinstance(ast, Name):
        if ast.id == 'True' or ast.id == 'False':
            return ast
        else:
            return Name(
                ast.id + '_' + str(get_current(current_version, ast.id)),
                Load()  # XXX: Is this correct?
            )

    elif isinstance(ast, PrimitiveOp):
        nodes = [convert_to_ssa(e, current_version) for e in ast.nodes]
        return PrimitiveOp(ast.name, nodes)

    elif isinstance(ast, IfExp):
        new_test = convert_to_ssa(ast.test, current_version)
        new_else = convert_to_ssa(ast.else_, current_version)
        new_then = convert_to_ssa(ast.then, current_version)
        return IfExp(test=new_test, else_=new_else, then=new_then)

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

    def getChildren(self):
        return self.name, self.type

    def getChildNodes(self):
        return ()

    def __repr__(self):
        return "VarDecl(%s, %s)" % (self.name, self.type)

def insert_var_decls(n):
    if isinstance(n, Module):
        decls = [VarDecl(x,'undefined') for x in assigned_vars(n.node)]
        return Module(decls + [n.node])
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
            predict_type(n.body, env)

    elif isinstance(n, FunctionDef):
        predict_type(n.code,env)

    elif isinstance(n, Call):
        pass#predict_type(n.code,env)

    elif isinstance(n, list):
        for s in n:
            predict_type(s, env)

    elif isinstance(n, Print):
        for e in n.values:
            predict_type(e, env)

    elif isinstance(n, If):
        for (cond,body) in n.tests:
            predict_type(cond,env)
            predict_type(body,env)
        predict_type(n.else_,env)
        for s in n.phis:
            predict_type(s,env)

    elif n == None:
        pass

    elif isinstance(n, While):
        predict_type(n.test,env)
        predict_type(n.body,env)
        for s in n.phis:
            predict_type(s,env)

    elif isinstance(n, Pass):
        pass

    elif isinstance(n, Assign):
        predict_type(n.expr, env)
        for a in n.nodes:
            if isinstance(a, Name):
                type_changed += update_var_type(env, a.id, n.expr.type)
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
        for e in n.nodes:
            predict_type(e, env)
        n.type = op_returns[n.name](tuple([e.type for e in n.nodes]))

    elif isinstance(n, IfExp):
        predict_type(n.test, env)
        predict_type(n.then, env)
        predict_type(n.else_, env)
        if n.then.type == n.else_.type:
            n.type = n.then.type
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
        return Module(type_specialize(n.body))
    elif isinstance(n, FunctionDef):
        n.code=type_specialize(n.code)
        return n
    elif isinstance(n, Call):
        return n
    elif isinstance(n, list):
        return [type_specialize(s) for s in n]
    elif isinstance(n, Print):
        # would be nice to specialize print, but not a high priority
        return Print(
            n.dest,
            [convert_to_pyobj(type_specialize(e)) for e in n.values],
            True
        )
    elif isinstance(n, If):
        tests = [(test_is_true(type_specialize(cond)), type_specialize(body)) \
                 for (cond,body) in n.tests]
        else_ = type_specialize(n.else_)
        phis = [type_specialize(s) for s in n.phis]
        ret = If(tests,else_)
        ret.phis = phis
        return ret
    elif n == None:
        return None
    elif isinstance(n, While):
        test = test_is_true(type_specialize(n.test))
        body = type_specialize(n.body)
        phis = [type_specialize(s) for s in n.phis]
        ret = While(test, body, None)
        ret.phis = phis
        return ret
    elif isinstance(n, Pass):
        return n
    elif isinstance(n, Assign):
        expr = type_specialize(n.expr)
        nodes = [type_specialize(a) for a in n.nodes]
        if any([a.type == 'pyobj' for a in nodes]):
            expr = convert_to_pyobj(expr)
        return Assign(nodes, expr)

    elif isinstance(n, Name):
        return n

    elif isinstance(n, VarDecl):
        return n

    elif isinstance(n, Num):
        return n
    elif isinstance(n, Name):
        return n
    elif isinstance(n, PrimitiveOp):
        nodes = [type_specialize(e) for e in n.nodes]
        tag = find_op_tag[n.name](tuple([e.type for e in n.nodes]))
        #if any([e.type == 'pyobj' for e in nodes]):
        if tag == 'pyobj':
            nodes = [convert_to_pyobj(e) for e in nodes]
        name = n.name if tag == '' else n.name + '_' + tag
        r = PrimitiveOp(name, nodes)
        r.type = n.type
        return r
    elif isinstance(n, IfExp):
        test = type_specialize(n.test)
        then = type_specialize(n.then)
        else_ = type_specialize(n.else_)
        test = test_is_true(test)
        if any([e.type == 'pyobj' for e in [n,then,else_]]):
            then = convert_to_pyobj(then)
            else_ = convert_to_pyobj(else_)
        r = IfExp(test, then, else_)
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

def split_phis(phis):
    branch_dict = {}
    for phi in phis:
        lhs = phi.nodes[0].name
        i = 0
        for rhs in phi.expr.nodes:
            if i in branch_dict:
                branch_dict[i].append(make_assign(lhs, rhs))
            else:
                branch_dict[i] = [make_assign(lhs, rhs)]
            i = i + 1
    return branch_dict

def remove_ssa(n):
    if isinstance(n, Module):
        return Module(remove_ssa(n.body))
    elif isinstance(n, FunctionDef):
        n.code=remove_ssa(n.code)
        return n
    elif isinstance(n, list):
        return [remove_ssa(s) for s in n]
    elif isinstance(n, Print):
        return n
    elif isinstance(n, If):
        tests = [(cond, remove_ssa(body)) for (cond,body) in n.tests]
        else_ = remove_ssa(n.else_)
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa If '
            print >> logs, 'branch dict: ', branch_dict
        b = 0
        new_tests = []
        for (cond,body) in tests:
            if 0 < len(branch_dict):
                new_body = body + [branch_dict[b]]
            else:
                new_body = body
            new_tests.append((cond,new_body))
            b = b + 1
        if 0 < len(branch_dict):
            new_else = else_ + [branch_dict[b]]
        else:
            new_else = else_
        ret = If(new_tests, new_else)
        return ret
    elif n == None:
        return None
    elif isinstance(n, While):
        test = n.test
        body = remove_ssa(n.body)
        phis = [remove_ssa(s) for s in n.phis]
        branch_dict = split_phis(phis)
        if debug:
            print >> logs, 'remove ssa While ', phis, branch_dict
        if 0 < len(branch_dict):
            ret = Stmt(
                branch_dict[0] + [
                    While(test, body, [branch_dict[1]], None)
                ]
            )
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
        main = generate_c(n.body)
        # all the support functions
        # the functions we found
        # int main() {
        # main body
        # return 0;}
        return \
            "".join(skeleton[:-3]) +\
            "\n".join(functions) +\
            "".join(skeleton[-3:-2]) +\
            generate_c(n.body) +\
            "".join(skeleton[-2:])
    elif isinstance(n, FunctionDef):
        functions.append("void "+n.name+"(){\n"+generate_c(n.code)+"\n}")
        return ""
    elif isinstance(n, Call):
        return n.node.name+"()"
    elif isinstance(n, list):
        return '{' + '\n'.join([generate_c(e) for e in n]) + '}'
    elif isinstance(n, Print):
        space = 'printf(\" \");'
        newline = 'printf(\"\\n\");'
        nodes_in_c = [
            'print_%s(%s);' % (x.type, generate_c(x)) for x in n.values
        ]
        return space.join(nodes_in_c) + newline
    elif isinstance(n, If):
        if n.else_ == None:
            else_ = ''
        else:
            else_ = 'else\n' + generate_c(n.else_)
        return 'if ' + '\n else if '.join([
            '(%s)\n%s' % (generate_c(cond), generate_c(body))
            for cond,body in n.tests
        ]) + else_
    elif isinstance(n, While):
        return 'while (%s)\n%s' % (generate_c(n.test), generate_c(n.body))
    elif isinstance(n, Pass):
        return ';'
    elif isinstance(n, Assign):
        return '='.join([generate_c(v) for v in n.targets]) \
               + ' = ' + generate_c(n.value) + ';'
    elif isinstance(n, Name):
        return n.id
    elif isinstance(n, VarDecl):
        return '%s %s;' % (python_type_to_c[n.type], n.name)

    elif isinstance(n, Num):
        return repr(n.n)
    elif isinstance(n, Name):
        if n.name == 'True':
            return '1'
        elif n.name == 'False':
            return '0'
        else:
            return n.name
    elif isinstance(n, PrimitiveOp):
        if n.name == 'deref':
            return '*' + generate_c(n.nodes[0])
        elif n.name in (
                'assign_pyobj', 'assign_int', 'assign_bool', 'assign_float'):
            return (
                '('
                + generate_c(n.nodes[0]) + '=' + generate_c(n.nodes[1])
                + ')'
            )
        else:
            return (
                n.name + '('
                + ', '.join([generate_c(e) for e in n.nodes])
                + ')'
            )
    elif isinstance(n, IfExp):
        return '(' + generate_c(n.test) + ' ? ' \
               + generate_c(n.then) + ':' + generate_c(n.else_) + ')'
    elif isinstance(n, Let):
        t = python_type_to_c[n.rhs.type]
        rhs = generate_c(n.rhs)
        return (
            '({ '
            + t + ' ' + n.var + ' = ' + rhs + '; ' + generate_c(n.body)
            + ';})'
        )
    elif n == None:
        return ''
    else:
        raise Exception(
            'Error in generate_c: unrecognized AST node ' + repr(n)
        )

######################### MAIN ##################################

if __name__ == "__main__":
    global debug

    argnum = 1
    debug = True
    infile = sys.stdin
    if len(sys.argv) >= argnum + 1 and sys.argv[argnum] == '-q':
        debug = False
        argnum += 1
    if len(sys.argv) >= argnum + 1:
        infile = open(sys.argv[argnum])
        argnum += 1
    if len(sys.argv) >= argnum + 1:
        raise Exception("Trailing arguments")

    ast = ast.parse("".join(infile.readlines()))
    if debug:
        print >> logs, ast
        print >> logs, 'simplifying ops --------------'
    ir = simplify_ops(ast)
    if debug:
        print >> logs, ir
        print >> logs, 'converting to ssa -----------'
    ir = convert_to_ssa(ir)
    if debug:
        print >> logs, ir
        print >> logs, 'inserting var decls ---------'
    ir = insert_var_decls(ir)
    if debug:
        print >> logs, ir
        print >> logs, 'predicting types -----------'
    predict_type(ir, {})
    if debug:
        print >> logs, ir
        print >> logs, 'type specialization -------'
        print >> logs, ir
    ir = type_specialize(ir)
    if debug:
        print >> logs, 'remove ssa ----------------'
        print >> logs, ir
    ir = remove_ssa(ir)
    if debug:
        print >> logs, 'finished remove ssa ------'
        print >> logs, ir
        print >> logs, 'generating C'
    print generate_c(ir)
