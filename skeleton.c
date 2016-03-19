#include <ctype.h>
#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define SIGN_OF(a) (((a) < 0) ? -1 : 1)
#define pyobj_to_bool(v) (!is_false(v))
#define logic_and(A, B) bool_to_pyobj(pyobj_to_bool(A) && pyobj_to_bool(B))
#define logic_or(A, B) bool_to_pyobj(pyobj_to_bool(A) || pyobj_to_bool(B))

#define logic_and_int(A, B) (A && B)
#define logic_and_bool(A, B) (A && B)

#define logic_or_int(A, B) (A || B)
#define logic_or_bool(A, B) (A || B)

#define add(a, b) add_pyobj(a, b)
#define add_int(a, b) (a + b)
#define add_bool(a, b) (a + b)
#define add_float(a, b) (a + b)

#define sub_int(a, b) (a - b)
#define sub_bool(a, b) (a - b)
#define sub_float(a, b) (a - b)

#define mul_int(a, b) (a * b)
#define mul_bool(a, b) (a * b)
#define mul_float(a, b) (a * b)

#define div_int(a, b) (a / b)
#define div_bool(a, b) (a / b)
#define div_float(a, b) (a / b)

#define unary_add_int(a) (+a)
#define unary_add_bool(a) (+a)
#define unary_add_float(a) (+a)

#define unary_sub_int(a) (-a)
#define unary_sub_bool(a) (-a)
#define unary_sub_float(a) (-a)

#define logic_not_int(a) (!a)
#define logic_not_bool(a) (!a)
#define logic_not_float(a) (!a)

#define less_int(a,b) (a < b)
#define less_bool(a,b) (a < b)
#define less_float(a,b) (a < b)

#define greater_int(a,b) (a > b)
#define greater_bool(a,b) (a > b)
#define greater_float(a,b) (a > b)

#define less_equal_int(a,b) (a <= b)
#define less_equal_bool(a,b) (a <= b)
#define less_equal_float(a,b) (a <= b)

#define greater_equal_int(a,b) (a >= b)
#define greater_equal_bool(a,b) (a >= b)
#define greater_equal_float(a,b) (a >= b)

#define equal_int(a,b) (a == b)
#define equal_bool(a,b) (a == b)
#define equal_float(a,b) (a == b)

#define identical_int(a,b) (a == b)
#define identical_bool(a,b) (a == b)
#define identical_float(a,b) (a == b)

#define not_equal_int(a,b) (a != b)
#define not_equal_bool(a,b) (a != b)
#define not_equal_float(a,b) (a != b)


enum type_tag { INT, FLOAT, BOOL, LIST };

struct pyobj_struct;

struct array_struct {
    struct pyobj_struct* data;
    unsigned int len;
};

typedef struct array_struct array;

struct pyobj_struct {
    enum type_tag tag;
    union {
        int i;                /* int */
        double f;             /* float */
        char b;               /* bool */
        array l;              /* list */
    } u;
};
typedef struct pyobj_struct pyobj;


char less_pyobj(pyobj a, pyobj b);
char less_equal_pyobj(pyobj a, pyobj b);
char greater_pyobj(pyobj a, pyobj b);
char greater_equal_pyobj(pyobj a, pyobj b);
char equal_pyobj(pyobj a, pyobj b);
char not_equal_pyobj(pyobj a, pyobj b);
char identical_pyobj(pyobj lhs, pyobj rhs);
pyobj add_pyobj(pyobj lhs, pyobj rhs);

pyobj make_list(int len);
void print_pyobj(pyobj v);


char printed_0;
char printed_0_neg;
void print_float(double in)
{
    char outstr[128];

    snprintf(outstr, 128, "%.12g", in);

    char *p = outstr;

    if(in == 0.0)
    {
        if(printed_0 == 0)
        {
            printed_0 = 1;
            printed_0_neg = *p == '-'; //see if we incremented for negative
        }
        else
        {
            printf(printed_0_neg ? "-0.0" : "0.0");
            return;
        }
    }

    if(*p == '-')
        p++;


    while(*p && isdigit(*p))
        p++;

    printf( ( (*p)  ? "%s" : "%s.0" ), outstr);
}

void print_int(int i) {
    printf("%d", i);
}

void print_bool(char b) {
    if (b == 0)
        printf("False");
    else
        printf("True");
}

static pyobj *current_list;
void print_list(pyobj pyobj_list)
{
    if(current_list && current_list == pyobj_list.u.l.data)
    {
        printf("[...]");
        return;
    }

    int will_reset = 0;
    if(!current_list)
    {
        current_list = pyobj_list.u.l.data;
        will_reset = 1;
    }

    array l = pyobj_list.u.l;
    printf("[");
    int i;
    for(i = 0; i < l.len; i++)
    {
        if (l.data[i].tag == LIST && l.data[i].u.l.data == l.data)
            printf("[...]");
        else
            print_pyobj(l.data[i]);
        if(i != l.len - 1)
            printf(", ");
    }
    printf("]");

    if(will_reset)
        current_list = NULL;
}


char is_in_list(pyobj a, pyobj b)
{
    char ret = 0;

    int i;
    for(i = 0; i< a.u.l.len; i++)
    {
        if(identical_pyobj(a.u.l.data[i],b))
            return 1;
    }
    return ret;
}

static char inside;
static pyobj printing_list;

void print_pyobj_rec(pyobj v) {
    switch (v.tag) {
    case INT:
        print_int(v.u.i);
        break;
    case FLOAT: {
        print_float(v.u.f);
        break;
    }
    case BOOL:
        print_bool(v.u.b);
        break;
    case LIST: {
        print_list(v);
        break;
    }
    default:
        printf("error, unhandled case in print_pyobj_rec\n");
        exit(1);
    }
}

void print_pyobj(pyobj v) {
    print_pyobj_rec(v);
}

pyobj int_to_pyobj(int x) {
    pyobj v;
    v.tag = INT;
    v.u.i = x;
    return v;
}

pyobj float_to_pyobj(double x) {
    pyobj v;
    v.tag = FLOAT;
    v.u.f = x;
    return v;
}

pyobj bool_to_pyobj(char x) {
    pyobj v;
    v.tag = BOOL;
    v.u.b = x;
    return v;
}

pyobj make_list(int len) {
    pyobj v;
    v.tag = LIST;
    v.u.l.data = (pyobj*)malloc(sizeof(pyobj) * len);
    v.u.l.len = len;
    return v;
}

pyobj* list_nth(pyobj list, pyobj n) {
    switch (list.tag) {
    case LIST: {
        switch (n.tag) {
        case INT: {
            if (n.u.i < list.u.l.len)
                return &(list.u.l.data[n.u.i]);
            else {
                printf("ERROR: list_nth index larger than list");
                exit(1);
            }
        }
        case BOOL: {
            if (n.u.b < list.u.l.len)
                return &(list.u.l.data[n.u.b]);
            else {
                printf("ERROR: list_nth index larger than list");
                exit(1);
            }
        }
        default:
            printf("ERROR: list_nth expected integer index");
            exit(1);
        }
    }
    default:
        printf("ERROR: list_nth applied to non-list");
        exit(1);
    }
}

pyobj list_add(pyobj x, pyobj y) {
    array a = x.u.l;
    array b = y.u.l;
    pyobj v;
    int i;
    v.tag = LIST;
    v.u.l.data = (pyobj*)malloc(sizeof(pyobj) * (a.len + b.len));
    v.u.l.len = a.len + b.len;
    for (i = 0; i != a.len; ++i)
        v.u.l.data[i] = a.data[i];
    for (i = 0; i != b.len; ++i)
        v.u.l.data[a.len + i] = b.data[i];
    return v;
}

pyobj list_sub(pyobj x, pyobj y) {
    printf("error, unsupported operand types");
    exit(1);
}

pyobj list_div(pyobj x, pyobj y) {
    printf("error, unsupported operand types");
    exit(1);
}

pyobj list_mult(pyobj x, int n) {
    int i;
    pyobj r = make_list(0);
    for (i = 0; i != n; ++i)
        r = list_add(x, r);
    return r;
}

pyobj list_mul(pyobj x, pyobj y) {
    switch (x.tag) {
    case INT:
        switch (y.tag) {
        case LIST:
            return list_mult(y, x.u.i);
        default:
            printf("error, unsupported operand types");
            exit(1);
        }
    case BOOL:
        switch (y.tag) {
        case LIST:
            return list_mult(y, x.u.b);
        default:
            printf("error, unsupported operand types");
            exit(1);
        }
    case LIST:
        switch (y.tag) {
        case INT:
            return list_mult(x, y.u.i);
        case BOOL:
            return list_mult(x, y.u.b);
        default:
            printf("error, unsupported operand types");
            exit(1);
        }
    default:
        printf("error, unsupported operand types");
        exit(1);
    }
}

int is_false(pyobj v)
{
    switch (v.tag) {
    case INT:
        return v.u.i == 0;
    case FLOAT:
        return v.u.f == 0;
    case BOOL:
        return v.u.b == 0;
    case LIST:
        return v.u.l.len == 0;
    default:
        printf("error, unhandled case in is_false\n");
        exit(1);
    }
}


static int equal_any(void* a, void* b)
{
    return equal_pyobj(*(pyobj*)a, *(pyobj*)b);
}

pyobj* subscript_pyobj(pyobj c, pyobj key)
{
    switch (c.tag) {
    case LIST:
        return list_nth(c, key);
    default:
        printf("error in subscript, not a list or dictionary\n");
        exit(1);
    }
}

#define gen_unary_op(NAME, OP) \
pyobj NAME##_pyobj(pyobj a) { \
    switch (a.tag) { \
    case INT: \
        return int_to_pyobj(OP a.u.i); \
    case FLOAT: \
        return float_to_pyobj(OP a.u.f); \
    case BOOL: \
        return int_to_pyobj(OP a.u.b); \
    default: \
        printf("error, unhandled case in unary operator\n"); \
        exit(1); \
    } \
}

gen_unary_op(unary_add, +)
gen_unary_op(unary_sub, -)

#define gen_binary_op(NAME, OP) \
    pyobj NAME##_pyobj(pyobj a, pyobj b) { \
        switch (a.tag) { \
        case INT: \
            switch (b.tag) { \
            case INT: \
                return int_to_pyobj(a.u.i OP b.u.i); \
            case FLOAT: \
                return float_to_pyobj(a.u.i OP b.u.f); \
            case BOOL: \
                return int_to_pyobj(a.u.i OP b.u.b); \
            case LIST: \
                return list_##NAME(a, b); \
            default: \
                printf("error, unhandled case in operator\n"); \
                exit(1); \
            } \
        case FLOAT: \
            switch (b.tag) { \
            case INT: \
                return float_to_pyobj(a.u.f OP b.u.i); \
            case FLOAT: \
                return float_to_pyobj(a.u.f OP b.u.f); \
            case BOOL: \
                return float_to_pyobj(a.u.f OP b.u.b); \
            default: \
                printf("error, unhandled case in operator\n"); \
                exit(1); \
            } \
        case BOOL: \
            switch (b.tag) { \
            case INT: \
                return int_to_pyobj(a.u.b OP b.u.i); \
            case FLOAT: \
                return float_to_pyobj(a.u.b OP b.u.f); \
            case BOOL: \
                return int_to_pyobj(a.u.b OP b.u.b); \
            case LIST: \
                return list_##NAME(a, b); \
            default: \
                printf("error, unhandled case in operator\n"); \
                exit(1); \
            } \
        case LIST: \
            switch (b.tag) { \
            case LIST: \
                return list_##NAME(a, b); \
            case INT: \
                return list_##NAME(a, b); \
            case BOOL: \
                return list_##NAME(a, b); \
            default: \
                printf("error, unhandled case in operator\n"); \
                exit(1); \
            } \
        default: \
            printf("error, unhandled case in operator\n"); \
            exit(1); \
        } \
    }

gen_binary_op(add, +)
gen_binary_op(sub, -)
gen_binary_op(mul, *)
gen_binary_op(div, /)


char logic_not_pyobj(pyobj v)
{
    if (is_false(v))
        return 1;
    else
        return 0;
}

int min(int x, int y) { return y < x ? y : x; }

char list_less(array x, array y) {
    int i;
    for (i = 0; i != min(x.len, y.len); ++i) {
        if (less_pyobj(x.data[i], y.data[i]))
            return 1;
        else if (less_pyobj(y.data[i], x.data[i]))
            return 0;
    }
    if (x.len < y.len)
        return 1;
    else
        return 0;
}
char list_equal(array x, array y) {
    char eq = 1;
    int i;
    for (i = 0; i != min(x.len, y.len); ++i)
        eq = eq && equal_pyobj(x.data[i], y.data[i]);
    if (x.len == y.len)
        return eq;
    else
        return 0;
}
char list_not_equal(array x, array y) {
    return !list_equal(x,y);
}
char list_greater(array x, array y) {
    return list_less(y,x);
}
char list_less_equal(array x, array y) {
    return !list_greater(y,x);
}
char list_greater_equal(array x, array y) {
    return !list_less(y,x);
}

#define gen_comparison(NAME, OP) \
char NAME##_pyobj(pyobj a, pyobj b) \
{ \
    switch (a.tag) { \
    case INT: \
        switch (b.tag) { \
        case INT: \
            return a.u.i  OP b.u.i; \
        case FLOAT: \
            return a.u.i OP b.u.f; \
        case BOOL:\
            return a.u.i OP b.u.b; \
        default: \
            return 0; \
        } \
    case FLOAT: \
        switch (b.tag) { \
        case INT: \
            return a.u.f  OP b.u.i; \
        case FLOAT: \
            return a.u.f OP b.u.f; \
        case BOOL: \
            return a.u.f OP b.u.b; \
        default: \
            return 0; \
        } \
    case BOOL: \
        switch (b.tag) { \
        case INT: \
            return a.u.b OP b.u.i; \
        case FLOAT:\
            return a.u.b OP b.u.f; \
        case BOOL: \
            return a.u.b OP b.u.b; \
        default: \
            return 0; \
        } \
    case LIST: \
        switch (b.tag) { \
        case LIST: \
            return list_##NAME(a.u.l, b.u.l); \
        default: \
            return 0; \
        } \
    default: \
        return 0; \
    } \
}

gen_comparison(less, <)
gen_comparison(equal, ==)

    char less_equal_pyobj(pyobj a, pyobj b) {
        return less_pyobj(a,b) || equal_pyobj(a,b);
    }

char greater_pyobj(pyobj a, pyobj b) {
    return !less_equal_pyobj(a,b);
}

char greater_equal_pyobj(pyobj a, pyobj b) {
    return !less_pyobj(a,b);
}

char not_equal_pyobj(pyobj a, pyobj b) {
    return !equal_pyobj(a,b);
}

char in_comp_pyobj(pyobj a, pyobj b) {
    int i=0;
    struct array_struct *as = (struct array_struct*)&b.u;
    for(i=0;i<as->len;++i){
        if (equal_pyobj(a,as->data[i]))
            return 1;
    }
    return 0;
}

char identical_pyobj(pyobj a, pyobj b) {
    if(a.tag != b.tag)
        return 0;
    switch(a.tag) {
    case INT:    return (a.u.i == b.u.i);
    case BOOL:   return (a.u.b == b.u.b);
    case FLOAT:  return (a.u.f == b.u.f);
    case LIST:   return (a.u.l.len == b.u.l.len && a.u.l.data == b.u.l.data);
    }
    return 0;
}

int main() {
    return 0;
}
