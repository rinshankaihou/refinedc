#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include "../inc/refinedc.h"

#define ITEM_EMPTY ((size_t)0)
#define ITEM_ENTRY ((size_t)1)
#define ITEM_TOMBSTONE ((size_t)2)

//@rc::inlined
//@Inductive item_ref type : Type :=
//@  | Empty
//@  | Entry (key : Z) (ty : type)
//@  | Tombstone (key : Z).
//@
//@Arguments Empty {_}.
//@Arguments Entry {_}.
//@Arguments Tombstone {_}.
//@rc::end

struct
[[rc::tagged_union("{item_ref type}")]]
item {
  size_t tag;

  union item_union {
    [[rc::union_tag("Empty")]]
    struct empty {
        [[rc::field("int<size_t>")]]
        size_t dummy; // TODO should empty struct be allowed / supported?
    } empty;

    [[rc::union_tag("Entry (key : Z) (ty : type)")]]
    struct entry {
        [[rc::field("key @ int<size_t>")]]
        size_t key;
        [[rc::field("&own<ty>")]]
        void* value;
    } entry;

    [[rc::union_tag("Tombstone (key : Z)")]]
    struct tombstone {
        [[rc::field("key @ int<size_t>")]]
        size_t key;
    } tombstone;
  } u;
};

[[rc::parameters("i : loc")]]
[[rc::args("i @ &own<uninit<struct_item>>")]]
[[rc::ensures("i @ &own<Empty @ item>")]]
void test_item_set_empty(struct item *i) {
    i->tag = ITEM_EMPTY;
    i->u.empty.dummy = 0;
}

[[rc::parameters("i : loc", "k : Z", "ty : type")]]
[[rc::args("i @ &own<uninit<struct_item>>", "k @ int<size_t>", "&own<ty>")]]
[[rc::ensures("i @ &own<{Entry k ty} @ item>")]]
void test_item_set_entry(struct item *i, size_t key, void *val) {
    i->tag = ITEM_ENTRY;
    i->u.entry.key = key;
    i->u.entry.value = val;
}

[[rc::parameters("i : loc", "x : {item_ref type}", "k : Z")]]
[[rc::args("i @ &own<x @ item>", "k @ int<size_t>")]]
[[rc::returns("int<size_t>")]]
[[rc::ensures("i @ &own<item>")]]
size_t test_item_modify_entry(struct item *i, size_t key) {
    size_t old_key;

    if (i->tag == ITEM_ENTRY) {
        old_key = i->u.entry.key;
        i->tag = ITEM_TOMBSTONE;
        i->u.tombstone.key = key;
        return old_key;
    }
    return key;
}
