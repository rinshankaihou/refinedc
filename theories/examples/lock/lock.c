#include <stddef.h>
#include "../inc/refinedc.h"
#include "../inc/spinlock.h"


struct [[rc::refined_by("n1 : Z", "n2 : Z", "n3 : Z")]]
       [[rc::exists("l: lock_id")]] lock_test {

    [[rc::field("n1 @ int<size_t>")]]
    size_t outside;

    [[rc::field("spinlock<l>")]]
    struct spinlock lock;

    [[rc::field("spinlocked_ex<l, {\"locked_int\"}, n2, λ n. n @ int<size_t>>")]]
    size_t locked_int;

    [[rc::field("spinlocked_ex<l, {\"locked_struct\"}, n3, λ n3. ...>")]]
    struct [[rc::exists("a : Z", "b : Z")]]
           [[rc::constraints("{n3 = (a + b)%Z}", "{it_in_range size_t n3}")]] lock_test_inner {

        [[rc::field("a @ int<size_t>")]]
        size_t a;

        [[rc::field("b @ int<size_t>")]]
        size_t b;
    } locked_struct;
};

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<struct_lock_test>>")]]
[[rc::ensures("p @ &own<{0, 0, 10} @ lock_test>")]]
void init(struct lock_test* t) {
    t->outside = 0;
    t->locked_int = 0;
    t->locked_struct.a = 0;
    t->locked_struct.b = 10;
    sl_init(&t->lock);
}

[[rc::parameters("p : loc", "n : Z", "n1 : Z", "n2 : Z", "n3 : Z")]]
[[rc::args("p @ &own<{n1, n2, n3} @ lock_test>", "n @ int<size_t>")]]
[[rc::ensures("p @ &own<{n, n2, n3} @ lock_test>")]]
void write_outside(struct lock_test* t, size_t n) {
    t->outside = n;
}

[[rc::parameters("p : loc", "n1 : Z", "n2 : Z", "n3 : Z")]]
[[rc::args("p @ &own<{n1, n2, n3} @ lock_test>")]]
[[rc::returns("n1 @ int<size_t>")]]
[[rc::ensures("p @ &own<{n1, n2, n3} @ lock_test>")]]
size_t read_outside(struct lock_test* t) {
    return t->outside;
}

[[rc::parameters("p : loc", "n : Z", "q : own_state", "n1 : Z", "n2 : Z", "n3 : Z")]]
[[rc::args("p @ &frac<q, {n1, n2, n3} @ lock_test>", "n @ int<size_t>")]]
[[rc::ensures("p @ &frac<q, {n1, n, n3} @ lock_test>")]]
void write_locked(struct lock_test* t, size_t n) {
    sl_lock(&t->lock);

    rc_unlock(t->locked_int);

    t->locked_int = n;
    sl_unlock(&t->lock);
}

[[rc::parameters("p : loc", "q : own_state", "n1 : Z", "n2 : Z", "n3 : Z")]]
[[rc::args("p @ &frac<q, {n1, n2, n3} @ lock_test>")]]
[[rc::exists("n : Z")]]
[[rc::returns("n @ int<size_t>")]]
[[rc::ensures("p @ &frac<q, {n1, n2, n3} @ lock_test>", "{q = Own → n = n2}")]]
size_t read_locked(struct lock_test* t) {
    sl_lock(&t->lock);
    rc_unlock(t->locked_int);

    size_t ret = t->locked_int;

    sl_unlock(&t->lock);
    return ret;
}

[[rc::parameters("p : loc", "q : own_state", "n1 : Z", "n2 : Z", "n3 : Z")]]
[[rc::args("p @ &frac<q, {n1, n2, n3} @ lock_test>")]]
[[rc::exists("n : Z")]]
[[rc::returns("n @ int<size_t>")]]
[[rc::ensures("p @ &frac<q, {n1, n2, n3} @ lock_test>", "{q = Own → n ≤ n3}")]]
size_t increment(struct lock_test* t) {
    sl_lock(&t->lock);
    rc_unlock(t->locked_struct);

    if (t->locked_struct.b > (size_t)0) {
        t->locked_struct.a += 1;
        t->locked_struct.b -= 1;
    }
    size_t ret = t->locked_struct.a;

    sl_unlock(&t->lock);
    return ret;
}
