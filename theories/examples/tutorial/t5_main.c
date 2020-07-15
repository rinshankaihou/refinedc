#include "list.h"
#include "alloc_internal.h"

#define DATA_SIZE 10000
static unsigned char allocator_data[DATA_SIZE];

[[rc::requires("[global_with_type \"allocator_state\" Own (uninit struct_alloc_state)]")]]
[[rc::requires("[global_with_type \"allocator_data\" Own (uninit (mk_layout (Z.to_nat 10000) 3))]")]]
[[rc::returns("int<i32>")]]
int main() {
    init_alloc();
    free(DATA_SIZE, allocator_data);

    test();
    return 0;
}
