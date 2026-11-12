void sink(...);
int source();

int global_int = source(); // $ initializer
const char global_array[] = "source"; // $ MISSING: initializer

void read_globals() {
  sink(global_int); // $ asVariable=global_int
  sink(global_array); // $ asVariable=global_array
}
