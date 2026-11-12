void take_const_ref_int(const int &);

void test_materialize_temp_int()
{
  take_const_ref_int(42); // $ asExpr=42(*42)
}

struct A {};

A get();
void take_const_ref(const A &);

void test1(){
  take_const_ref(get()); // $ asExpr="call to get(*call to get)"
}

void take_ref(A &);

A& get_ref();

void test2() {
  take_ref(get_ref()); // $ asExpr="call to get_ref" asIndirectExpr="call to get_ref"
}

struct S {
  int a;
  int b;
};

void test_aggregate_literal() {
  S s1 = {1, 2}; // $ asExpr=1 asExpr=2 asExpr={...}
  const S s2 = {3, 4}; // $ asExpr=3 asExpr=4 asExpr={...}
  S s3 = (S){5, 6}; // $ asExpr=5 asExpr=6 asExpr={...}
  const S s4 = (S){7, 8}; // $ asExpr=7 asExpr=8 asExpr={...}

  S s5 = {.a = 1, .b = 2}; // $ asExpr=1 asExpr=2 asExpr={...}

  int xs[] = {1, 2, 3}; // $ asExpr=1 asExpr=2 asExpr=3 asExpr={...}
  const int ys[] = {[0] = 4, [1] = 5, [0] = 6}; // $ asExpr=4 asExpr=5 asExpr=6 asExpr={...}
}

void test_postfix_crement(int *p, int q) { // $ asParameter=p asParameter=q parameterNode=p parameterNode=q
  p++; // $ asExpr="... ++" asIndirectExpr="... ++" asExpr=p asIndirectExpr=p
  q++; // $ asExpr="... ++" asExpr=q
  (p++); // $ asExpr="... ++" asIndirectExpr="... ++" asExpr="p(... ++)" asIndirectExpr="p(*... ++)"
  (q++); // $ asExpr="... ++" asExpr="q(... ++)"
  (void)(p++); // $ asExpr="p(... ++)" asIndirectExpr="p(*... ++)"
  (void)(q++); // $ asExpr="q(... ++)"
  (void)p++; // $ asExpr="p(... ++)" asIndirectExpr="p(*... ++)"
  (void)q++; // $ asExpr="q(... ++)"
  int *p1 = p++; // $ asExpr="... ++" asIndirectExpr="... ++" asExpr="p(... ++)" asIndirectExpr="p(*... ++)"
  int q1 = q++; // $ asExpr="... ++" asExpr="q(... ++)"
  (int*)(p++); // $ asExpr="... ++" asIndirectExpr="... ++" asExpr="p(... ++)" asIndirectExpr="p(*... ++)"
  (int)(q++); // $ asExpr="... ++" asExpr="q(... ++)"
  int *p2 = (int*)(p++); // $ asExpr="... ++" asIndirectExpr="... ++" asExpr="p(... ++)" asIndirectExpr="p(*... ++)"
  int q2 = (int)(q++); // $ asExpr="... ++" asExpr="q(... ++)"
}

struct Foo {
  void f();
};

struct Derived : Foo {};

void test_qualifiers(
  Foo x, // $ asParameter=x parameterNode=x
  Foo &r, // $ asParameter=r(*r) parameterNode=r(*r)
  Foo *p, // $ asParameter=p parameterNode=p
  Foo *&rp, // $ asParameter=rp(*rp) parameterNode=rp(*rp)
  Derived d, // $ asParameter=d parameterNode=d
  Derived &rd) { // $ asParameter=rd(*rd) parameterNode=rd(*rd)
  x.f(); // $ asExpr=x
  r.f(); // $ asExpr=r asIndirectExpr=r
  p->f(); // $ asExpr=p asIndirectExpr=p
  (*p).f(); // $ asExpr="* ..." asExpr="p(* ...)" asIndirectExpr="p(* ...)"
  rp->f(); // $ asExpr=rp asIndirectExpr=rp numberOfNodes="rp: 2" numberOfIndirectNodes="rp: 2"
  (*rp).f(); // $ asExpr="* ..." asExpr="rp(* ...)" asIndirectExpr="rp(* ...)" numberOfIndirectNodes="rp: 2" asIndirectExpr=rp
  d.f(); // $ asExpr=d
  rd.f(); // $ asExpr=rd asIndirectExpr=rd
}

void test_inner_glvalue_qualifiers(
  Foo x, // $ asParameter=x parameterNode=x
  Foo &r) { // $ asParameter=r(*r) parameterNode=r(*r)
  Foo arr[2];
  (*&x).f(); // $ asExpr="* ..." asExpr="& ...(* ...)" asIndirectExpr="& ...(* ...)" asExpr="x(* ...)"
  (*&r).f(); // $ asExpr="* ..." asExpr="& ...(* ...)" asIndirectExpr="& ...(* ...)" asExpr="r(* ...)" asIndirectExpr="r(* ...)"
  (*arr).f(); // $ asExpr="* ..." asExpr="arr(* ...)"
}

void take_ptr(char*);
void take_const_ptr(const char*);
void take_ptr_ptr(char**);
void take_foo_ref(Foo&);

struct HasField {
  int field;
};

void test_glvalues(Foo x, HasField h, int* ip) { // $ asParameter=x parameterNode=x asParameter=h parameterNode=h asParameter=ip parameterNode=ip
  char buf[10];
  take_ptr(buf); // $ asExpr=buf(*buf)
  take_const_ptr("abc"); // $ asExpr=abc(*abc)
  char* ptrs[2];
  take_ptr_ptr(ptrs); // $ asExpr=ptrs(*ptrs) asIndirectExpr=ptrs
  int i = h.field; // $ asExpr=h asExpr=field
  take_foo_ref(x); // $ asExpr=x(*x)
  Foo* q = &x; // $ asExpr="& ..." asIndirectExpr="& ..." asExpr="x(*& ...)"
  *ip = 1; // $ asExpr="* ..." asExpr="ip(* ...)" asIndirectExpr="ip(* ...)" asExpr=1
}

struct C {
  C();
};

void test_constructor_calls() {
  C c; // $ asExpr="call to C"
  C *p = new C; // $ asExpr="call to C" asExpr=new asIndirectExpr=new
}
