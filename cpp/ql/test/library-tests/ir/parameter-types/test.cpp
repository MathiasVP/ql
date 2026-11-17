void pointer_param(char **argv) { // $ type="glval<char **>"
}

void array_param(char *argv[]) { // $ type="glval<char **>"
}

// The parameter is declared as `char **argv` in `declarations.cpp`.
void array_param_with_pointer_declaration(char *argv[]) { // $ type="glval<char **>"
}
