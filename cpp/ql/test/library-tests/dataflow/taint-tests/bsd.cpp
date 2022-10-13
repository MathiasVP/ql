void sink(...);
int source();

// --- accept ---

struct sockaddr {
	unsigned char length;
	int sa_family;
	char* sa_data;
};

int accept(int, const sockaddr*, int*);

void sink(sockaddr);

void test_accept() {
  int s = source();
  sockaddr addr;
  int size = sizeof(sockaddr);
  int a = accept(s, &addr, &size);

  sink(a); // $ ir
  sink(addr); // $ MISSING: ir
}
