int source();
void sink(int);

void throughLocal() {
    int local = source();
    sink(local); // $ ast,ir
}

int flowTestGlobal1 = 0;

void readWriteGlobal1() {
    sink(flowTestGlobal1); // $ ir MISSING: ast
    flowTestGlobal1 = source();
}

static int flowTestGlobal2 = 0;

void readGlobal2() {
    sink(flowTestGlobal2); // $ ir MISSING: ast
}

void writeGlobal2() {
    flowTestGlobal2 = source();
}

namespace MyNamespace {
    struct A {
        int x;
    };

    A global_a;

    void set_without_ssa_def() {
        global_a.x = source();
    }

    void call_set_without_ssa_def() {
        set_without_ssa_def();
        sink(global_a.x); // $ ir MISSING: ast
    }
}