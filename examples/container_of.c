
#define container_of(ptr, type, member) (type *)( (unsigned char *)(ptr) - offsetof(type,member) )

struct test {
  int a;
  int b;
};

[[rc::returns("{4} @ int<i32>")]]
int container_of_test() {
  struct test t = {.a = 1, .b = 2};
  int *b = &t.b;
  *b = 3;
  struct test *pt = container_of(b, struct test, b);
  pt->a = 4;
  return t.a;
}
