#include <latch.h>
#include "list.h"
#include "alloc_internal.h"

[[rc::global("{alloc_initialized} @ latch")]]
static struct latch initialized = LATCH_INIT;

#define DATA_SIZE 10000
static unsigned char allocator_data[DATA_SIZE];

[[rc::requires("[initialized \"initialized\" ()]")]]
[[rc::requires("global allocator_state : uninit<struct_alloc_state>")]]
[[rc::requires("global allocator_data  : uninit<{Layout (Z.to_nat 10000) 3}>")]]
[[rc::returns("int<i32>")]]
int main() {
    init_alloc();
    free(DATA_SIZE, allocator_data);
    latch_release(&initialized);

    test();
    return 0;
}

[[rc::requires("[initialized \"initialized\" ()]")]]
[[rc::returns("int<i32>")]]
int main2() {
    latch_wait(&initialized);

    test();
    return 0;
}
