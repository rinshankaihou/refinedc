#ifndef REFINEDC_H
#define REFINEDC_H

// Required for copy_alloc_id.
#include <stdint.h>

#define rc_unfold(e)                                     \
    _Pragma("GCC diagnostic push")                       \
    _Pragma("GCC diagnostic ignored \"-Wunused-value\"") \
    &(e);                                                \
    _Pragma("GCC diagnostic pop")

#define rc_unfold_int(e)                                 \
    _Pragma("GCC diagnostic push")                       \
    _Pragma("GCC diagnostic ignored \"-Wunused-value\"") \
    e + 0;                                               \
    _Pragma("GCC diagnostic pop")

#define rc_annot(e, ...)                                 \
    _Pragma("GCC diagnostic push")                       \
    _Pragma("GCC diagnostic ignored \"-Wunused-value\"") \
    [[rc::annot(__VA_ARGS__)]] &(e);                     \
    _Pragma("GCC diagnostic pop")

#define rc_unlock(e) rc_annot(e, "UnlockA")
#define rc_to_uninit(e) rc_annot(e, "ToUninit")
#define rc_stop(e) rc_annot(e, "StopAnnot")
#define rc_share(e) rc_annot(e, "ShareAnnot")
#define rc_unfold_once(e) rc_annot(e, "UnfoldOnceAnnot")
#define rc_learn(e) rc_annot(e, "LearnAnnot")
#define rc_learn_alignment(e) rc_annot(e, "LearnAlignmentAnnot")

#ifdef RC_ENABLE_FOCUS
#define RC_FOCUS ,rc::trust_me
#define RC_FOCUS_X
#else
#define RC_FOCUS
#define RC_FOCUS_X
#endif

#define RC_MACRO_ARG(arg) "ARG", #arg
#define RC_MACRO_EXPR(expr) "EXPR", expr
#define RC_MACRO(name, m, ...) (0 ? ("rc_macro", #name, __VA_ARGS__, (m)) : (m))

// Note that copy_alloc_id exposes the provenance of [from] by casting it
// to an integer (throwing away the result).
#if defined (__cerb__)
#define copy_alloc_id(to, from) __cerbvar_copy_alloc_id((to), (from))
#else
static inline void *copy_alloc_id(uintptr_t to, void *from) {
  return ((uintptr_t) (from), (void*) (to));
}
#endif

#endif
