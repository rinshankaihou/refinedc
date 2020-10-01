#ifndef REFINEDC_H
#define REFINEDC_H

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
#define rc_uninit_strengthen_align(e) rc_annot(e, "UninitStrengthenAlign")
#define rc_stop(e) rc_annot(e, "StopAnnot")
#define rc_share(e) rc_annot(e, "ShareAnnot")
#define rc_unfold_once(e) rc_annot(e, "UnfoldOnceAnnot")
#define rc_learn(e) rc_annot(e, "LearnAnnot")

#ifdef RC_ENABLE_FOCUS
#define RC_FOCUS ,rc::trust_me
#define RC_FOCUS_X
#else
#define RC_FOCUS
#define RC_FOCUS_X
#endif

#endif
