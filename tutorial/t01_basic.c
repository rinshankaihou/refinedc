#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

// TODO: Make the structure of this tutorial clearer

// TODO: clearly separate parts about how to use RefinedC and how
// RefinedC works -> especially type checking part

// TODO: clear explanation what rc::parameter, rc::exists, rc::args,
// ... are, what kind of arguments they take, with a small cheatsheet

/**
   We start with one of the simplest functions one could verify:
   [int_id] returns the int which it receives as its argument. Let's
   verify that this function actually returns an integer if it is
   passed an integer as the argument. This is stated using
   [rc::args], which gives RefinedC types to arguments, and
   [rc::return], which gives a RefinedC type to the resulting value.
   The RefinedC type [int<i32>] is the type of signed integers with 32
   bits and corresponds to the [int] type in C.

   If you build this file according to the README, you should see a line which says
   something like

   ...
   coqc tutorial/proofs/t01_basic/.generated_proof_int_id.aux,...
   ...

   This means that this function was verified successfully. If you only see

   Entering directory '/local/home/mackie/andres/Jobs/MPI-SWS/repos/refinedc'

   This means that the proof is already up-to-date. The simplest way
   to force a rechecking is to add an empty line at the top of this
   file then try again.

*/
[[rc::args("int<i32>")]]
[[rc::returns("int<i32>")]]
int int_id(int a) {
    return a;
}

/**
   Aside: As the [int<i32>] type shows, types in RefinedC can be
   parametrized --- here the parameter inside the <..> is i32 and
   denotes that the integer is a signed 32-bit integer. But one can
   for example also write [int<u64>] to refer to a unsigned 64-bit
   integer.

   In general, RefinedC types can be parametrized by
   arbitrary Coq types. In this case, [int<..>] is parametrized by
   what is called an [int_type], which describes an integer type and
   is a combination of signedness and number of bits. The predefined
   [int_type] are [u8, u16, u32, u64, i8, i16, i32, i64, size_t,
   ssize_t]. As a user of RefinedC, you only need to care
   about these predefined [int_type].

   Aside: As we have seen, there are three type systems involved when
   working with RefinedC:
   - The C type system: This is the normal type system of C which one uses also
     without RefinedC. The role of this type system is mostly to describe the physical
     layout of types (e.g. how many bytes does this value have? What are the alignment
     constraints?) and the operations (e.g. which casts should be inserted when adding
     two numbers? How many bytes should be read when dereferencing a pointer?). This type
     system does it's job well, but it is too weak to describe interesting properties.
     For this we need...
   - The RefinedC type system: This type system drives the verification when using RefinedC.
     We will get to know it better over the course of this tutorial. But as we have already
     seen the RefinedC type system also uses...
   - The Coq type system: This is the type system of the Coq proof assistant on which RefinedC
     is based. The most important role of this type system is to give mathematical
     representations, e.g. of integers, lists or maps. This tutorial will show you the types you
     need for some verification tasks. But if you have some experience in Coq, you can also
     define your own Coq types and use them in you specifications. But more on that later...

   When talking about a type, you have to be careful which type system you are referring to.
   Types in different type systems might have the same name as we have already seen with [int]
   in the C type system roughly corresponding to [int<i32>] in the RefinedC type system.
   In this tutorial we will qualify the type name by its type system if it is not obvious from
   the context.
 */

/**
   Refinement types
   ================

   While [int_id] fulfills its specification, this specification is
   quite weak. We would additionally like to prove that it is indeed
   the identity function, i.e. it returns the same integer as it was
   passed for the argument. To be able to state this specification, we
   use the name-giving feature of RefinedC: refinement types.

   Refinement types as used by RefinedC are quite straightforward:
   Each RefinedC type can have an associated Coq type, which is the
   mathematical representation of a value which has the RefinedC type.
   We say that the RefinedC type is /refined by/ its associated Coq
   type or that the Coq type is /the refinement of/ the RefinedC type.

   For example, the RefinedC type [int<...>] which represents C
   integers of a fixed size is refined by the Coq type [Z] of
   unbounded mathematical integers. During verification one only
   interacts with the mathematical integers represented by the
   refinement, e.g. a [+] in a specification is a mathematical [+]
   which is a lot nicer to work with than [+] on fixed size integers
   as one does not have to consider overflow etc.

   In general, what the refinement of a RefinedC type represents
   depends on the RefinedC type. For [int<..>] it is the mathematical
   representation of the physical value, for a linked list type it
   might be a mathematical list,... We will see more examples in this
   tutorial. Some RefinedC types also don't have a refinement (e.g.
   the [null] RefinedC type is only inhabited by the NULL value and
   thus does not need a refinement).

   Refinements in RefinedC are denoted with the [... @ ...] syntax.
   E.g. [n @ int<i32>] is the type of integers which correspond to the
   mathematical integer [n] (in this case only a single value inhabits
   the RefinedC type [n @ int<i32>]). If a type with a refinement is
   used without [@], the value of the refinement is implicitly
   existentially quantified, i.e. one can think of [int<i32>] as [∃ n,
   n @ int<i32>].

   Now back to our id function: The specification we want is that if
   one passes an arbitrary integer [n] as the argument, [int_id2]
   returns the same integer. Stating this is simple in RefinedC:

   First, we need to make the specification parametric on the integer
   [n] which is passed as the argument via [rc::parameters...] where
   we give a list of names and Coq types in which the specification
   should be parametric in. In particular, the arguments for
   rc::parameters are universally quantified in the rest of the
   specification.

   Second, we use [n @ int<i32>] for both the argument and the return
   type, which enforces that the integer returned by [int_id2] is the
   same integer as given for the argument.
*/

[[rc::parameters("n : Z")]]
[[rc::args("n @ int<i32>")]]
[[rc::returns("n @ int<i32>")]]
int int_id2(int a) {
    return a;
}

/**
   Now to a function which is a bit more interesting than the identity
   function, but only a little bit: adding 1 to an integer.

   Except for the [rc::requires...] annotation, the specification of
   [add1] should be straightforward. Note that one needs to surround
   mathematical (Coq) expressions (like [n + 1]) with [{...}] if the
   they are more than an identifier.

   An [rc::requires...] annotation states additional preconditions
   which the caller of a function has to fulfill. Here the caller
   needs to ensure that the addition does not overflow. In RefinedC
   (like in VCC) all over- and underflow is considered undefined
   behaviour and verification with RefinedC ensures that no overflow
   or underflow can happen. This is why the precondtion [n + 1 ≤
   max_int i32] is necessary.
 */
[[rc::parameters("n : Z")]]
[[rc::args("n @ int<i32>")]]
  /* try commenting out the following line */
[[rc::requires("{n + 1 ≤ max_int i32}")]]
[[rc::returns("{n + 1} @ int<i32>")]]
int add1(int a) {
    return a + 1;
}

/**
   Failing side conditions
   =======================

   Try commenting out the line with [rc::requires...] on the [add1]
   function and running RefinedC. You should see an output which looks
   something like:

   Cannot solve sidecondition in function "add1" !
   Location: "tutorial/t01_basic.c" [ 154 : 11 - 154 : 16 ]
   Location: "tutorial/t01_basic.c" [ 154 : 4 - 154 : 17 ]
   up to date: true
   Goal:
   n : Z
   H : (min_int i32 ≤ n)
   H0 : (n ≤ max_int i32)
   H1 : (min_int i32 ≤ 1)
   ---------------------------------------
   (n + 1 ≤ max_int i32)


   This is one of the possible failure modes of RefinedC. If you look
   at the first line, you can see that RefinedC could not prove a side
   condition which arose during the typechecking of this function.
   Afterwards, you see a bunch of line and column numbers. These tell
   you where the sidecondition comes from (the line numbers in this
   comment might be a bit of). Here the line numbers show that this
   problem comes from the the [a + 1]. [up to date: true] in the error
   message shows that the line numbers can be considered accurate.

   After the line numbers, you can see the goal which RefinedC could
   not prove. Everything above the long line are the facts which are
   known at this point in the program and below you can see the
   statement which could not be proven. In this example, RefinedC
   cannot prove [n + 1 ≤ max_int i32] which means that [n + 1] is
   in the range of a signed 32-bit integer ([i32]). As we have
   discussed before, this condition is generated by typechecking of
   the [+] since overflow is undefined behavior in the RefinedC C
   semantics. If you now look at the facts we know, we can see that
   this problem is not a problem of the RefinedC automation but the
   goal is actually not provable since n might very well be INT_MAX-1.
   This reasoning shows that we actually need the [rc::requires...]
   clause on [add1] since it is not well-typed otherwise.
 */


/**
   Typechecking
   ============

   Based on the next example, we want to get a better high-level
   understanding how the typechecker of RefinedC works.

   When a C program is translated into Coq by the frontend, it is
   transformed into a control flow graph representation.

     Aside: If you are interested, you can look at the file
     proofs/t01_basic/generated_code.v to see the representation
     in Coq. This is only for understanding what happens under the
     hood, you usually do not interact with it directly.

   The high-level picture of how the the RefinedC typechecker works is
   very simple: Typechecking starts at each basic block, which has an
   annotated precondtion. (The first block of the function always has
   the precondtion of the whole function. Other preconditions might
   come from loop invariants as we will see later.) Then the RefinedC
   typechecker simply processes each statement in the block one by
   one, updates its typing context and generates sideconditions. It
   does this until it reaches a [return] statement or a block with a
   precondition, in which case it proves the postcondition of the
   function resp. the precondition of the block.

   During this traversal of the program, the typechecking might split
   into two (or more) branches via case distinctions. The most common
   way for these to occur are on if statements. So let's look at the
   following [min] function. Currently, it verifies without problems.
   But try changing the condition in the [assert] and see what happens.

   E.g. if you change the first assert to [r == a] you should get an
   error that RefinedC cannot prove [b = a] on the line of the assert.
   If you look at the output of RefinedC, you should also see
   something like:

     Case distinction (if bool_decide (a < b)) -> false
     at "tutorial/t01_basic.c" [ 256 : 7 - 256 : 12 ]

   This kind of output gives us some information which case
   distinctions took place before this sidecondition was generated,
   i.e. from which path through the program this sidecondition arises.
   In this example, we see that the case distinction comes from the [a
   < b] inside the if statement via the location information in the
   last line and also based on [(if bool_decide (a < b))].
   The [false] tells us that we are in the case where the check
   failed, i.e. type checking went through the else branch.

   Play a bit around with this example until you have a better
   understanding how typechecking in RefinedC works!
*/

[[rc::parameters("a : Z", "b : Z")]]
[[rc::args("a @ int<i32>", "b @ int<i32>")]]
[[rc::returns("{a `min` b} @ int<i32>")]]
int min(int a, int b) {
    int r;
    if(a < b) {
        r = a;
    } else {
        r = b;
    }
    // try different conditions here (e.g. r == a, r > b) and see what
    // happens
    assert(r <= a);
    assert(r <= b); // these are C assertions
    return r;
}

/**
   Loop invariants
   ===============

   Loops are a bit more complicated than if statements, so let's have
   a look at the world's most stupid add function: [looping_add]

   As you can see, loops must have an annotated loop invariant.

     ATTENTION: If you forget annotating a loop invariant, the
     frontend will automatically generate a loop invariant that
     is very likely wrong.

  The main part of the loop invariant annotation is the [rc::inv_vars]
  annotation. It specifies the types of the local variables at the
  beginning of the loop, /before/ the check of the loop condition.

  [rc::exists] gives Coq variables which might vary from iteration to
  interation. Here, [acc] is [va] plus how much we have already added.

  [rc::constraints] gives additional constraints which have to hold
  before the check of the loop condition. Here we have to make sure
  that [acc], the value stored in [a], is not negative, as otherwise the
  loop will underflow.

  Note that RefinedC does not prove termination, so there is no need
  to specify a loop variant or similar.

  Try to play around with this loop invariant (e.g. changing the
  refinement of [b] or the rc::constraints clause) and see if you can
  understand why certain errors occur and how they can be fixed.

  For a general explanation of loop invariants look e.g. at
  https://www.cs.cornell.edu/courses/cs2112/2015fa/lectures/lec_loopinv/
*/

[[rc::parameters("va : Z", "vb : Z")]]
[[rc::args("va @ int<i32>", "vb @ int<i32>")]]
[[rc::requires("{va + vb ≤ max_int i32}", "{0 <= va}")]]
[[rc::returns("{va + vb} @ int<i32>")]]
int looping_add(int a, int b) {
    [[rc::exists("acc : Z")]]
    [[rc::inv_vars("a : acc @ int<i32>", "b : {va + vb - acc} @ int<i32>")]]
    [[rc::constraints("{0 <= acc}")]] // try commenting this line and see what happens
    while(a > 0) {
        b++;
        // try uncommenting the following line: (see below for explanation)
        /* rc_stop(a); */
        a--;
    }
    return b;
}

/**
   Type system error messages
   ==========================

   We also want to use the [looping_add] example to understand the
   type system a bit better. You can use the [rc_stop] macro, which
   takes as argument an arbitrary variable, to artifically stop the
   type system by changing the goal to False. Uncommenting the
   [rc_stop] results in an error which we have not seen before:

     Type system got stuck in function "looping_add" in block "#1" !

   This is a different error from the "Cannot solve sidecondition" which
   we have seen before. In general, this kind of error occurs if no
   typing rule of the type system applies to the goal. In this case,
   the reason is obvious, but in general this kind of error occurs if
   there is ownership reasoning which the type system cannot figure
   out automatically. We will see examples of that later.

   In addition to the information, which is also present in the
   "Cannot solve sidecondition" error, the "Type system got stuck"
   error also shows the typing context at the point where the program
   gets stuck. For this example, it should look something like

     _ : block{ "#1" }
     _ : i2v (va + vb - acc + 1) i32 : (va + vb - acc + 1) @ int<i32>
     _ : own arg_b : (va + vb - acc + 1) @ int<i32>
     _ : own arg_a : acc @ int<i32>
     --------------------------------------∗

   The first line only tells us that there is a precondtion for block
   "#1", but the other ones are more interesting:

      own arg_a : acc @ int<i32>

   Tells us that the /location/ where [a] is stored has type [acc @ int
   i32]. In general, RefinedC has two kinds of type assignments:

   - The main type assignment of RefinedC is based on locations in
     memory, sometimes also called places or lvalues. The location
     type assignment [own l : ty] states that location [l] stores
     something of type [ty]. All local variables and arguments are
     represented as locations in RefinedC, so most of the reasoning is
     done using this type assignment. All types have a location type
     assignment.

   - The other type assignment is more traditional and assigns types
     to values, i.e. [v : ty]. While most types support this value
     type assignment (we call them "movable" types, some types don't
     support it (we call them "immovable" types). For examples, you
     might have a structures where one field points to another field
     of the same structure. Such a type only makes sense if it is
     stored in memory, but as a value since it is not possible to
     point inside a value.

       Aside: Rust solves this problem a bit differently. In Rust, all
       types a user can define are movable, but instead there is the
       Pinning API (https://doc.rust-lang.org/std/pin/index.html) to
       support intrusive linking.
 */

/**
   Ownership types
   ===============

   So far we have seen many examples using integers, but RefinedC can
   not only reason about integers. Another important feature of C are
   pointers. Reasoning about pointers is handled by ownership types in
   RefinedC.

   The basic idea of ownership types is simple: The type of a pointer
   does no only ensure that the value is a pointer value, but the type
   also ensures exclusive ownership of the memory that the pointer
   points to. Roughly this exclusive ownership ensures that there is
   only one valid pointer to a location of memory at each time so when
   modifying a memory location, one does not need to worry about
   potential aliases.

   Let's look at ownership types in action: The following [int_ptrs]
   function takes two pointer arguments [p1] and [p2]. They have the
   RefinedC type [&own<T>] which denotes that they are owned pointers
   --- concretely, they are owned pointers to integers. (You can
   ignore the rc::ensures) clause for the moment.)
 */

[[rc::parameters("p1 : loc", "p2 : loc")]]
[[rc::args("p1 @ &own<int<i32>>", "p2 @ &own<int<i32>>")]]
[[rc::ensures("own p1 : int<i32>", "own p2 : int<i32>")]]
void int_ptrs(int* p1, int* p2) {
  /** We can write to p1. */
  *p1 = 1;
  /** Afterwards we know that p1 points to 1. */
  assert(*p1 == 1);
  /** We can also write to p2. */
  *p2 = 2;
  /** And afterwards [*p1] contains 1 and [*p2] contains 2. */
  assert(*p1 == 1);
  assert(*p2 == 2);
}

/**
   This verification of [int_ptrs] might seem straightforward, but
   actually it is not obvious that all the asserts in this function
   always succeed. Can you think of a potential caller of this
   function that could make one of the asserts fail?


   The interesting assert is the second [assert(*p1 == 1)]: For
   proving that this assert succeeds, we need to know that [*p1] still
   contains 1 even after the write to [p2]. But what if a client
   passes the same pointer as [p1] and [p2], i.e. [p1] and [p2] alias?
   In this case, the write to [p2] would overwrite the value stored in
   [p1] and the [assert(*p1 == 1)] fails! In general, such aliasing
   makes verification of C code very hard as every write to a pointer
   could potentially invalidate many other pointers. This is where
   ownership types come in to save the day: Ownership types and in
   particular owned pointers rule out aliasing by ensuring that there
   can only be one owned pointer for each memory location. Concretely
   for the example above the owned pointer types of [p1] and [p2] mean
   that they cannot alias since they are both owned pointers and there
   can only be one owned pointer to each memory location. This
   implicitly ensures that the write to [p2] does not change the value
   stored at [p1] and thus the second [assert(*p1 == 1)] always
   succeeds.

   We can see the ownership constraint that the [int_ptrs] places on
   its clients more clearly when looking at the following function:
   */

[[rc::ensures("True")]]
void call_int_ptrs() {
  int p1 = 0, p2 = 0;
  /** Calling int_ptrs with two different pointers is fine. */
  int_ptrs(&p1, &p2);
  /** But calling [int_ptrs] with aliasing pointers gives an error.
   * Try uncommenting the next line to see it.  */
  // int_ptrs(&p1, &p1); // try uncommenting this line
}

/**
    When you uncomment the second call to [int_ptrs], you should get
    an error which roughly looks like the following:

    Type system got stuck in function "call_int_ptrs" in block "#0" !
    Location: "tutorial/t01_basic.c" [ 462 : 16 - 462 : 19 ]
    Location: "tutorial/t01_basic.c" [ 462 : 2 - 462 : 21 ]
    Location: "tutorial/t01_basic.c" [ 462 : 2 - 462 : 21 ]
    up to date: true
    Goal:
    global_int_ptrs : loc
    local_p1 : loc
    local_p2 : loc
    Q : (gmap label stmt)
    R : (val → type → iProp Σ)
    v : val
    x : Z
    x0 : Z
    ---------------------------------------
    _ : global_int_ptrs ∶ global_int_ptrs @ function_ptr type_of_int_ptrs
    --------------------------------------□
    _ : i2v 0 i32 ∶ 0 @ int<i32>
    _ : i2v 0 i32 ∶ 0 @ int<i32>
    _ : own local_p2 ∶ x0 @ int<i32>
    _ : v ∶ void
    --------------------------------------∗
    find_in_context (FindLoc local_p1)
    ...

    This error might seem quite intimidating at first, but it is not
    too hard to understand what it means. The important part for
    understanding error messages like this is to look at the top-most
    connective after
    --------------------------------------∗

    This shows the head of the Goal where the RefinedC type checker
    got stuck. In this case, it is [find_in_context (FindLoc
    local_p1)]. This tells us that the RefinedC type system could not
    find ownership of the location [local_p1] (i.e. the location of
    the local variable [p1]) in the context. In fact, we can see that
    the context only contains ownership of [local_p2] (i.e. own
    local_p2 ∶ x0 @ int<i32>) but not of [p1]. Looking at the line
    numbers tells us that this happens when type checking the &p1 in
    the second argument to int_ptrs. With this information we can
    figure out what happened: We passed ownership of [p1] to
    [int_ptrs] together with the first argument so that when RefinedC
    tries to pass the ownership of the second argument, it gets stuck
    because this ownership is already gone! Overall, this shows how
    RefinedC rules out aliasing using ownership types.

*/

/**
   TODO: Talk about rc::ensures clauses with ownership types.
 */

/**
   So far we have only looked at the [int] type, but there are more
   types in RefinedC. The next example of a function which initializes
   an integer to 1 shows two of them:

   - [uninit<layout>] represents uninitialized memory which might
     contain arbitrary values (including poison). It is parametrized
     by a [layout], which describes the size of the uninitialized
     memory. There is a coercions from [int_type] to [layout] so we
     can just use [uninit<i32>] to denote uninitialized memory which
     can fit an integer.

   - [&own<T>] is an owned pointer to [T]. RefinedC uses an ownership
     type system inspired by Rust, but without lifetimes. [&own<T>]
     corresponds roughly to [Box<T>], but without guarantee that it is
     allocated on the heap. Instead of lifetimes, in RefinedC
     ownership is explicitly passed back to the caller via the ensures
     clause. The key trick which makes this work is the refinement of
     [&own]: It is refined by a location (represented by the Coq type
     [loc]). Notice how the [&own] in the [rc::args] and [rc::ensures]
     are refined by the same [p], which tells the caller of this
     function ownership is returned for the /same/ pointer which was
     passed as the argument.
 */

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<i32>>")]]
[[rc::ensures("own p : {1} @ int<i32>")]]
void init_int(int* out) {
    *out = 1;
}

/**
   Subtyping rules convert [int<i32>] to [uninit<i32>] automatically.
 */

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<i32>>")]]
void init_int_test(int* out) {
  int i;
  init_int(&i);
  init_int(&i);
}

/**
   Structs are represented with the [struct<struct_layout, field
   types...>] RefinedC type. The [struct_layout], which corresponds to
   C type of the struct, is necessary since it contains the names of
   the fields and their sizes. The frontend automatically generates the
   layout for each structure in the source file as [struct_<name of
   the struct>], i.e. in this example as [struct_basic]. Operations on
   structures, e.g. initializing, accessing fields, copying structures
   by value, ... simply work as expected.
 */

struct basic { int a, b; };
[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<struct_basic>>")]]
[[rc::ensures("own p : struct<struct_basic, {2} @ int<i32>, {0} @ int<i32>>")]]
void struct_test(struct basic* out) {
    // C guarantees that b is initialized to 0
    *out = (struct basic){.a = 1};
    out->a++;
}

/**
   However, most of the time you will not work with the [struct] type
   directly, but use annotations on structures to define new types, as
   we will see in t03_list.c...
 */
