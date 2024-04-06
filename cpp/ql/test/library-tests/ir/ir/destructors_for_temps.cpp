class ClassWithDestructor2 {
public:
    ClassWithDestructor2();
    ~ClassWithDestructor2();

    char get_x();
};

class ClassWithConstructor {
public:
    ClassWithConstructor(char x, char y);
};

char temp_test() {
    char x = ClassWithDestructor2().get_x();
    ClassWithConstructor y('a', ClassWithDestructor2().get_x());
    return ClassWithDestructor2().get_x();
}


char temp_test2() {
    new ClassWithDestructor2();
    return ClassWithDestructor2().get_x() + ClassWithDestructor2().get_x();
}

template<typename T>
T returnValue();

void temp_test3() {
    const ClassWithDestructor2& rs = returnValue<ClassWithDestructor2>();
}

void temp_test4() {
    ClassWithDestructor2 c;
    const ClassWithDestructor2& rs2 = returnValue<ClassWithDestructor2>();
}

void temp_test5(bool b) {
  b ? ClassWithDestructor2() : ClassWithDestructor2();
}

void temp_test6(bool b) {
    ClassWithDestructor2 c;
    if (b) {
      throw ClassWithConstructor('x', ClassWithDestructor2().get_x());
    }
}

void temp_test7(bool b) {
    ClassWithDestructor2 c;
    b ? throw ClassWithConstructor('x', ClassWithDestructor2().get_x()) : ClassWithDestructor2();
}

void temp_test8(bool b) {
    b ? throw ClassWithConstructor('x', ClassWithDestructor2().get_x()) : ClassWithDestructor2();
}

void temp_test8_simple(bool b) {
    b ? throw ClassWithDestructor2().get_x() : 'a';
}

struct string
{
    string(const char *);
    ~string();
};

bool const_ref_string(const string &);

bool conditional_temp_via_conjunction(bool b)
{
    return b && const_ref_string("");
}

ClassWithDestructor2 make();

void temp_test9() {
    // At the semicolon `~ClassWithDestructor2::ClassWithDestructor2()` is called
    // to destruct the temporary created by `make()`. We get a consistency error
    // here because the read side effect instruction doesn't have a memory to
    // read from since the IR doesn't have return value side effects to produce
    // a memory. The same problem happens in `temp_test5`.
    make();
}


void temp_test10(int i) {
    while(i < 10) {
        // Here we get a `missingPhiOperand` inconsistency error for the same reason
        // that we're getting a `missingOperandType` in `temp_test9`.
        make();
    }
}