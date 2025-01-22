int source();
void sink(int);

void loop1(const bool* a, int len) { // $ ast-def=a
  int x = 0;
  for (int i = 0; i < len; i++) {
    bool b = a[i];
    if (b) {
      x = source();
    }
    if (!b) {
      sink(x); // $ ast,ir
    }
    // flow can loop around from one iteration to the next
  }
}

void loop2(const bool* a, int len) { // $ ast-def=a
  for (int i = 0; i < len; i++) {
    // x is local to the loop iteration and thus cannot loop around and reach the sink
    int x = 0;
    bool b = a[i];
    if (b) {
      x = source();
    }
    if (!b) {
      sink(x); // $ SPURIOUS: ast
    }
  }
}