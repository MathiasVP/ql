typedef unsigned long size_t;
typedef long ssize_t;

#include "common.h"

template <typename T>
struct S {
  int get_int();
  T get_template_value();
};

template <typename U>
void template_func_calling_printf(S<U> &obj) {
  ::printf("%d\n", obj.get_int());
  ::printf("%d\n", obj.get_template_value()); // $ Alert
}

void instantiate() {
  S<int>  s_int;
  S<long> s_long;

  template_func_calling_printf(s_int);  // ok
  template_func_calling_printf(s_long); // not ok (long -> int)
}

struct FirstFormatPointer {};
struct SecondFormatPointer {};

void correlated_format_types(FirstFormatPointer *first, SecondFormatPointer *second,
                             const char *text, double number, int width) {
  printf("%p %s %d", first, text, width);
  printf("%s %p %f", text, second, number);
  printf("%d %s", width, text);
  printf("%s %d", text, width);
  printf("%s", first); // $ Alert[cpp/wrong-type-format-argument]
  printf("%d", text); // $ Alert[cpp/wrong-type-format-argument]
  printf("%f", width); // $ Alert[cpp/wrong-type-format-argument]
  printf("%*.*f", width, width, number);
  printf("%*s", number, text); // $ Alert[cpp/wrong-type-format-argument]
}
