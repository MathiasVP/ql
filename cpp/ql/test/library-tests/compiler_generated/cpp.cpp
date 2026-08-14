
int x;

class MySuperClass {
    public:
        MySuperClass() { x = 1; }
        ~MySuperClass() { x = 2; }
};

class MyClass : MySuperClass {
};

void g1(void) {
    MyClass *m = new MyClass();
    delete m;
}

void predefined_macros() {
    // These are predefined variables that has initializers inside any function that uses them.
    auto a = __PRETTY_FUNCTION__;
    auto b = __func__;
}