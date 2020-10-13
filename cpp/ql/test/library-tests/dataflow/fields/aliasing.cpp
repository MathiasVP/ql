int user_input();
void sink(int);

struct S {
  int m1, m2;
};

void pointerSetter(S *s) {
  s->m1 = user_input();
}

void referenceSetter(S &s) {
  s.m1 = user_input();
}

void copySetter(S s) {
  s.m1 = user_input();
}

void callSetters() {
  S s1 = { 0, 0 };
  S s2 = { 0, 0 };
  S s3 = { 0, 0 };

  pointerSetter(&s1);
  referenceSetter(s2);
  copySetter(s3);

  sink(s1.m1); // $ast,ir
  sink(s2.m1); // $ast,ir
  sink(s3.m1); // no flow
}

void assignAfterAlias() {
  S s1 = { 0, 0 };
  S &ref1 = s1;
  ref1.m1 = user_input();
  sink(s1.m1); // $f-:ast $ir

  S s2 = { 0, 0 };
  S &ref2 = s2;
  s2.m1 = user_input();
  sink(ref2.m1); // $f-:ast $ir
}

void assignAfterCopy() {
  S s1 = { 0, 0 };
  S copy1 = s1;
  copy1.m1 = user_input();
  sink(s1.m1); // no flow

  S s2 = { 0, 0 };
  S copy2 = s2;
  s2.m1 = user_input();
  sink(copy2.m1); // no flow
}

void assignBeforeCopy() {
  S s2 = { 0, 0 };
  s2.m1 = user_input();
  S copy2 = s2;
  sink(copy2.m1); // $ast,ir
}

struct Wrapper {
  S s;
};

void copyIntermediate() {
  Wrapper w = { { 0, 0 } };
  S s = w.s;
  s.m1 = user_input();
  sink(w.s.m1); // no flow
}

void pointerIntermediate() {
  Wrapper w = { { 0, 0 } };
  S *s = &w.s;
  s->m1 = user_input();
  sink(w.s.m1); // $f-:ast $ir
}

void referenceIntermediate() {
  Wrapper w = { { 0, 0 } };
  S &s = w.s;
  s.m1 = user_input();
  sink(w.s.m1); // $f-:ast $ir
}

void nestedAssign() {
  Wrapper w = { { 0, 0 } };
  w.s.m1 = user_input();
  sink(w.s.m1); // $ast,ir
}

void addressOfField() {
  S s;
  s.m1 = user_input();

  S s_copy = s;
  int* px = &s_copy.m1;
  sink(*px); // $f-:ast $ir
}

void taint_a_ptr(int* pa) {
  *pa = user_input();
}

void test_field_conflation_array_content() {
  S s;
  taint_a_ptr(&s.m1);
  sink(s.m2);
}

struct S_with_pointer {
  int m1, m2;
  int* data;
};

void pointer_deref(int* xs) {
  taint_a_ptr(xs);
  sink(xs[0]); // $f-:ast $ir
}

void pointer_deref_sub(int* xs) {
  taint_a_ptr(xs - 2);
  sink(*(xs - 2)); // $f-:ast $ir
}

void pointer_many_addrof_and_deref(int* xs) {
  taint_a_ptr(xs);
  sink(*&*&*xs); // $f-:ast $ir
}

void pointer_unary_plus(int* xs) {
  taint_a_ptr(+xs);
  sink(*+xs); // $f-:ast $ir
}

void pointer_member_index(S_with_pointer s) {
  taint_a_ptr(s.data);
  // `s.data` is points to all-aliased-memory
  sink(s.data[0]); // $f-:ast,ir
}

void member_array_different_field(S_with_pointer* s) {
  taint_a_ptr(&s[0].m1);
  sink(s[0].m2);
}

struct S_with_array {
  int m1, m2;
  int data[10];
};

void pointer_member_deref() {
  S_with_array s;
  taint_a_ptr(s.data);
  sink(*s.data); // $ir,ast
}

void array_member_deref() {
  S_with_array s;
  taint_a_ptr(s.data);
  sink(s.data[0]); // $ir,ast
}

struct S2 {
  S s;
  int m3;
};

void deep_member_field_dot() {
  S2 s2;
  taint_a_ptr(&s2.s.m1);
  sink(s2.s.m1); // $ir,ast
}

void deep_member_field_dot_different_fields() {
  S2 s2;
  taint_a_ptr(&s2.s.m1);
  sink(s2.s.m2);
}

void deep_member_field_dot_2() {
  S2 s2;
  taint_a_ptr(&s2.s.m1);
  S2 s2_2 = s2;
  sink(s2_2.s.m1); // $ir,ast
}

void deep_member_field_dot_different_fields_2() {
  S2 s2;
  taint_a_ptr(&s2.s.m1);
  S2 s2_2 = s2;
  sink(s2_2.s.m2);
}

void deep_member_field_arrow(S2 *ps2) {
  taint_a_ptr(&ps2->s.m1);
  sink(ps2->s.m1); // $ir,ast
}

void deep_member_field_arrow_different_fields(S2 *ps2) {
  taint_a_ptr(&ps2->s.m1);
  sink(ps2->s.m2);
}

void test_deep_struct_fields() {
  S2 s2;
  s2.s.m1 = user_input();
  S s = s2.s;
  sink(s.m1); // $ir,ast
}

void test_deep_struct_fields_no_flow() {
  S2 s2;
  s2.s.m1 = user_input();
  S s = s2.s;
  sink(s.m2);
}

void test_deep_struct_fields_taint_through_call() {
  S2 s2;
  taint_a_ptr(&s2.s.m1);
  S s = s2.s;
  sink(s.m1); // $ir,ast
}

void test_deep_struct_fields_taint_through_call_no_flow() {
  S2 s2;
  taint_a_ptr(&s2.s.m1);
  S s = s2.s;
  sink(s.m2);
}

struct B {
  int a;
  int c;
  int d;
  int e;
};

struct A {
  B b;
  int y;
};

void call_sink_with_B(B* p) {
  sink(p->e); // $ir=256:10 $ir=266:10 $ast $f-:ast=266:10
}

void test_multiple_loads_from_a_same_memory_1() {
  A a;
  B *p = &a.b;
  p->c = user_input();
  p->e = p->c;
  call_sink_with_B(p);
}

void multiple_loads_from_a_same_memory(B* p) { p->e = p->c; }

void test_multiple_loads_from_a_same_memory_2() {
  A a;
  B *p = &a.b;
  p->c = user_input();
  multiple_loads_from_a_same_memory(p);
  call_sink_with_B(p);
}