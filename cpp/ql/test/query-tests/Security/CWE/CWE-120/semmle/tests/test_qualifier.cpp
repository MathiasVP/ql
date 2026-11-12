typedef unsigned long size_t;
size_t recv(int s, void *buf, size_t len, int flags);
char *strcpy(char *dest, const char *src);

struct S {
	char buf[100];
};

void test_object_qualifier(int sock, char *dest)
{
	S s;
	recv(sock, &s, sizeof(s), 0); // $ Source[cpp/unbounded-write]
	strcpy(dest, s.buf); // $ Alert[cpp/unbounded-write] // BAD
}
