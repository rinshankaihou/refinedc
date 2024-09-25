From refinedc.typing Require Import typing.
From refinedc.examples.scheduler.src.fdsched Require Import generated_code.
From refinedc.examples.scheduler.src.fdsched Require Import message_extra.
From caesium Require Import builtins_specs.
From refinedc.examples.scheduler.src.fdsched Require Import priority_extra.
From refinedc.examples.scheduler.src.fdsched Require Import scheduler_extra.
From refinedc.examples.scheduler.src.fdsched Require Import fdsched_extra.
From refinedc.examples.scheduler.src.fdsched Require Import fdsched_extra.
From refinedc.typing Require Import malloc.
From refinedc.examples.scheduler.src.fdsched Require Import fdsched_extra.
Set Default Proof Using "Type".

(* Generated from [examples/scheduler/src/fdsched.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Inlined code. *)

   Notation F_SETFL := 4 (only parsing).
   Notation O_NONBLOCK := 2048 (only parsing).

  (* Definition of type [message]. *)
  Definition message_rec : (message_data * type → type) → (message_data * type → type) := (λ self patt__,
    let data := patt__.1 in
    let cont := patt__.2 in
    struct struct_message [@{type}
      ((m_type data) @ (int (u8))) ;
      ((m_length data) @ (int (u64))) ;
      (cont) ;
      (array_p (u8) ((get_packet_data data.(m_id)) `at_type` int u8) (Z.to_nat max_msg_len))
    ]
  )%I.
  Global Typeclasses Opaque message_rec.

  Global Instance message_rec_le : TypeMono message_rec.
  Proof. solve_type_proper. Qed.

  Definition message (cont : type) : rtype (message_data) := {|
    rty r__ := message_rec (type_fixpoint message_rec) (r__, cont)
  |}.

  Lemma message_unfold (cont : type) (data : message_data):
    (data @ message cont)%I ≡@{type} (
      struct struct_message [@{type}
        ((m_type data) @ (int (u8))) ;
        ((m_length data) @ (int (u64))) ;
        (cont) ;
        (array_p (u8) ((get_packet_data data.(m_id)) `at_type` int u8) (Z.to_nat max_msg_len))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 message_rec). Qed.

  Definition message_simplify_hyp_place_inst_generated (cont : type) patt__ :=
    [instance simplify_hyp_place_eq _ _ (message_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance message_simplify_hyp_place_inst_generated.
  Definition message_simplify_goal_place_inst_generated (cont : type) patt__ :=
    [instance simplify_goal_place_eq _ _ (message_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance message_simplify_goal_place_inst_generated.

  Definition message_simplify_hyp_val_inst_generated (cont : type) patt__ :=
    [instance simplify_hyp_val_eq _ _ (message_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance message_simplify_hyp_val_inst_generated.
  Definition message_simplify_goal_val_inst_generated (cont : type) patt__ :=
    [instance simplify_goal_val_eq _ _ (message_unfold (cont : type) patt__) with 100%N].
  Global Existing Instance message_simplify_goal_val_inst_generated.

  (* Definition of type [message_queue]. *)
  Definition message_queue_rec : ((list message_data) → type) → ((list message_data) → type) := (λ self messages,
    (∃ₜ p, own_constrained (tyown_constraint (p) (null)) (
      struct struct_message_queue [@{type}
        (tyfold ((λ data cont, &own (malloced (ly_size struct_message) (data @ message cont)) : type) <$> messages) (place (p))) ;
        (&own (place (p)))
      ]
    ))
  )%I.
  Global Typeclasses Opaque message_queue_rec.

  Global Instance message_queue_rec_le : TypeMono message_queue_rec.
  Proof. solve_type_proper. Qed.

  Definition message_queue : rtype ((list message_data)) := {|
    rty r__ := message_queue_rec (type_fixpoint message_queue_rec) r__
  |}.

  Lemma message_queue_unfold (messages : (list message_data)):
    (messages @ message_queue)%I ≡@{type} (
      (∃ₜ p, own_constrained (tyown_constraint (p) (null)) (
        struct struct_message_queue [@{type}
          (tyfold ((λ data cont, &own (malloced (ly_size struct_message) (data @ message cont)) : type) <$> messages) (place (p))) ;
          (&own (place (p)))
        ]
      ))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 message_queue_rec). Qed.

  Definition message_queue_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (message_queue_unfold patt__) with 100%N].
  Global Existing Instance message_queue_simplify_hyp_place_inst_generated.
  Definition message_queue_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (message_queue_unfold patt__) with 100%N].
  Global Existing Instance message_queue_simplify_goal_place_inst_generated.

  Definition message_queue_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (message_queue_unfold patt__) with 100%N].
  Global Existing Instance message_queue_simplify_hyp_val_inst_generated.
  Definition message_queue_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (message_queue_unfold patt__) with 100%N].
  Global Existing Instance message_queue_simplify_goal_val_inst_generated.

  (* Definition of type [prio_bitmap_t]. *)
  Definition prio_bitmap_t_rec : ((list bool) → type) → ((list bool) → type) := (λ self bitmap,
    (
      constrained (struct struct_prio_bitmap [@{type}
        (array (u64) (encode_prio_bitmap bitmap `at_type` int u64))
      ]) (
        ⌜length bitmap = Z.to_nat num_priorities⌝
      )
    )
  )%I.
  Global Typeclasses Opaque prio_bitmap_t_rec.

  Global Instance prio_bitmap_t_rec_le : TypeMono prio_bitmap_t_rec.
  Proof. solve_type_proper. Qed.

  Definition prio_bitmap_t : rtype ((list bool)) := {|
    rty r__ := prio_bitmap_t_rec (type_fixpoint prio_bitmap_t_rec) r__
  |}.

  Lemma prio_bitmap_t_unfold (bitmap : (list bool)):
    (bitmap @ prio_bitmap_t)%I ≡@{type} (
      (
        constrained (struct struct_prio_bitmap [@{type}
          (array (u64) (encode_prio_bitmap bitmap `at_type` int u64))
        ]) (
          ⌜length bitmap = Z.to_nat num_priorities⌝
        )
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 prio_bitmap_t_rec). Qed.

  Definition prio_bitmap_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (prio_bitmap_t_unfold patt__) with 100%N].
  Global Existing Instance prio_bitmap_t_simplify_hyp_place_inst_generated.
  Definition prio_bitmap_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (prio_bitmap_t_unfold patt__) with 100%N].
  Global Existing Instance prio_bitmap_t_simplify_goal_place_inst_generated.

  Definition prio_bitmap_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (prio_bitmap_t_unfold patt__) with 100%N].
  Global Existing Instance prio_bitmap_t_simplify_hyp_val_inst_generated.
  Definition prio_bitmap_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (prio_bitmap_t_unfold patt__) with 100%N].
  Global Existing Instance prio_bitmap_t_simplify_goal_val_inst_generated.

  (* Definition of type [callback_t]. *)
  Definition callback_t_rec : (nat → type) → (nat → type) := (λ self priority,
    (
      constrained (struct struct_callback [@{type}
        (priority @ (int (u8))) ;
        (function_ptr (fn(∀ (msg, q) : message_data * loc;(&own (msg @ (message (uninit (void*))))); True) →∃ () : (), (int (i32));True))
      ]) (
        ⌜0 <= priority < 256⌝
      )
    )
  )%I.
  Global Typeclasses Opaque callback_t_rec.

  Global Instance callback_t_rec_le : TypeMono callback_t_rec.
  Proof. solve_type_proper. Qed.

  Definition callback_t : rtype (nat) := {|
    rty r__ := callback_t_rec (type_fixpoint callback_t_rec) r__
  |}.

  Lemma callback_t_unfold (priority : nat):
    (priority @ callback_t)%I ≡@{type} (
      (
        constrained (struct struct_callback [@{type}
          (priority @ (int (u8))) ;
          (function_ptr (fn(∀ (msg, q) : message_data * loc;(&own (msg @ (message (uninit (void*))))); True) →∃ () : (), (int (i32));True))
        ]) (
          ⌜0 <= priority < 256⌝
        )
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 callback_t_rec). Qed.

  Definition callback_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (callback_t_unfold patt__) with 100%N].
  Global Existing Instance callback_t_simplify_hyp_place_inst_generated.
  Definition callback_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (callback_t_unfold patt__) with 100%N].
  Global Existing Instance callback_t_simplify_goal_place_inst_generated.

  Definition callback_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (callback_t_unfold patt__) with 100%N].
  Global Existing Instance callback_t_simplify_hyp_val_inst_generated.
  Definition callback_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (callback_t_unfold patt__) with 100%N].
  Global Existing Instance callback_t_simplify_goal_val_inst_generated.

  (* Definition of type [npfp_t]. *)
  Definition npfp_t_rec : (npfp_sched → type) → (npfp_sched → type) := (λ self npfp_scheduler,
    (
      struct struct_npfp_scheduler [@{type}
        (array (struct_callback) (callbacks npfp_scheduler `at_type` callback_t)) ;
        (array (struct_message_queue) (msg_qs npfp_scheduler `at_type`  message_queue)) ;
        ((create_bitmap (msg_qs npfp_scheduler)) @ (prio_bitmap_t))
      ]
    )
  )%I.
  Global Typeclasses Opaque npfp_t_rec.

  Global Instance npfp_t_rec_le : TypeMono npfp_t_rec.
  Proof. solve_type_proper. Qed.

  Definition npfp_t : rtype (npfp_sched) := {|
    rty r__ := npfp_t_rec (type_fixpoint npfp_t_rec) r__
  |}.

  Lemma npfp_t_unfold (npfp_scheduler : npfp_sched):
    (npfp_scheduler @ npfp_t)%I ≡@{type} (
      (
        struct struct_npfp_scheduler [@{type}
          (array (struct_callback) (callbacks npfp_scheduler `at_type` callback_t)) ;
          (array (struct_message_queue) (msg_qs npfp_scheduler `at_type`  message_queue)) ;
          ((create_bitmap (msg_qs npfp_scheduler)) @ (prio_bitmap_t))
        ]
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 npfp_t_rec). Qed.

  Definition npfp_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (npfp_t_unfold patt__) with 100%N].
  Global Existing Instance npfp_t_simplify_hyp_place_inst_generated.
  Definition npfp_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (npfp_t_unfold patt__) with 100%N].
  Global Existing Instance npfp_t_simplify_goal_place_inst_generated.

  Definition npfp_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (npfp_t_unfold patt__) with 100%N].
  Global Existing Instance npfp_t_simplify_hyp_val_inst_generated.
  Definition npfp_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (npfp_t_unfold patt__) with 100%N].
  Global Existing Instance npfp_t_simplify_goal_val_inst_generated.

  (* Definition of type [fd_t]. *)
  Definition fd_t_rec : (fd_sched → type) → (fd_sched → type) := (λ self fd_scheduler,
    (
      struct struct_fd_scheduler [@{type}
        (array_p (i32) (input_channels fd_scheduler `at_type` (int i32)) (16%nat)) ;
        ((length (input_channels fd_scheduler)) @ (int (u64))) ;
        ((sched_state fd_scheduler) @ (npfp_t))
      ]
    )
  )%I.
  Global Typeclasses Opaque fd_t_rec.

  Global Instance fd_t_rec_le : TypeMono fd_t_rec.
  Proof. solve_type_proper. Qed.

  Definition fd_t : rtype (fd_sched) := {|
    rty r__ := fd_t_rec (type_fixpoint fd_t_rec) r__
  |}.

  Lemma fd_t_unfold (fd_scheduler : fd_sched):
    (fd_scheduler @ fd_t)%I ≡@{type} (
      (
        struct struct_fd_scheduler [@{type}
          (array_p (i32) (input_channels fd_scheduler `at_type` (int i32)) (16%nat)) ;
          ((length (input_channels fd_scheduler)) @ (int (u64))) ;
          ((sched_state fd_scheduler) @ (npfp_t))
        ]
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 fd_t_rec). Qed.

  Definition fd_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (fd_t_unfold patt__) with 100%N].
  Global Existing Instance fd_t_simplify_hyp_place_inst_generated.
  Definition fd_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (fd_t_unfold patt__) with 100%N].
  Global Existing Instance fd_t_simplify_goal_place_inst_generated.

  Definition fd_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (fd_t_unfold patt__) with 100%N].
  Global Existing Instance fd_t_simplify_hyp_val_inst_generated.
  Definition fd_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (fd_t_unfold patt__) with 100%N].
  Global Existing Instance fd_t_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_errno]. *)
  Definition type_of___builtin_errno :=
    fn(∀ n : Z; (is_errno n))
      → ∃ () : (), (&own (n @ (int (i32)))); (is_errno n).

  (* Specifications for function [fcntl]. *)
  Definition type_of_fcntl :=
    fn(∀ () : (); (int (i32)), ((F_SETFL) @ (int (i32))), ((O_NONBLOCK) @ (int (i32))); True)
      → ∃ () : (), ((0) @ (int (i32))); True.

  (* Function [poll] has been skipped. *)

  (* Specifications for function [read]. *)
  Definition type_of_read :=
    fn(∀ (data, fd, l, t1, errno) : (list Z) * Z * loc * nat * Z; (fd @ (int (i32))), (l @ (&own (uninit (mk_array_layout u8 (Z.to_nat max_msg_len))))), (max_msg_len @ (int (u64))); (curr_read_index t1) ∗ (is_errno errno))
      → ∃ (n, pckt) : Z * packet_ID, ((if (bool_decide $ is_Some $ (packet_arrivals fd t1)) then length (get_packet_data pckt) else -1) @ (int (i64))); ⌜pckt = {|fd := fd; read_index := t1|}⌝ ∗ ⌜if  (bool_decide $ is_Some $ (packet_arrivals fd t1)) then True else n = EWOULDBLOCK⌝ ∗ (is_errno n) ∗ (l ◁ₗ (array_p (u8) (get_packet_data pckt `at_type` int(u8)) (Z.to_nat max_msg_len))) ∗ (curr_read_index (t1 + 1%nat)).

  (* Specifications for function [message_identify_type]. *)
  Definition type_of_message_identify_type :=
    fn(∀ (msg, q) : message_data * loc; (q @ (&own (struct (struct_message) [@{type} uninit (u8) ; (m_length msg) @ (int (u64)) ; uninit (void*) ; array_p (u8) ((get_packet_data  msg.(m_id)) `at_type` int u8) (Z.to_nat max_msg_len) ]))); True)
      → ∃ () : (), ((message_identify_type_coq msg.(m_id)) @ (int (u8))); (q ◁ₗ (struct (struct_message) [@{type} uninit (u8) ; (m_length msg) @ (int (u64)) ; uninit (void*) ; array_p (u8) (get_packet_data msg.(m_id) `at_type` int(u8)) (Z.to_nat max_msg_len) ])).

  (* Specifications for function [message_queue_add]. *)
  Definition type_of_message_queue_add :=
    fn(∀ (data, msg, q) : (list message_data) * message_data * loc; (q @ (&own (data @ (message_queue)))), (&own (malloced (ly_size struct_message) (msg @ (message (uninit (void*)))))); True)
      → ∃ () : (), (void); (q ◁ₗ ((data ++ [msg]) @ (message_queue))).

  (* Specifications for function [message_queue_empty]. *)
  Definition type_of_message_queue_empty :=
    fn(∀ (data, q) : (list message_data) * loc; (q @ (&own (data @ (message_queue)))); True)
      → ∃ () : (), ((bool_decide (data = [])) @ (boolean (i32))); (q ◁ₗ (data @ (message_queue))).

  (* Specifications for function [message_queue_remove]. *)
  Definition type_of_message_queue_remove :=
    fn(∀ (data, q) : (list message_data) * loc; (q @ (&own (data @ (message_queue)))); ⌜data ≠ []⌝)
      → ∃ () : (), ((head data) @ (optionalO (λ msg1,
        &own (malloced (ly_size struct_message) (msg1 @ (message (uninit (void*)))))
      ) null)); (q ◁ₗ ((tail data) @ (message_queue))).

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [prio_level_init]. *)
  Definition type_of_prio_level_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_prio_bitmap)))); True)
      → ∃ () : (), (void); (p ◁ₗ ((replicate (Z.to_nat num_priorities) false) @ (prio_bitmap_t))).

  (* Specifications for function [highest_pending_priority]. *)
  Definition type_of_highest_pending_priority :=
    fn(∀ (p, bm) : loc * (list bool); (p @ (&own (bm @ (prio_bitmap_t)))); ⌜length bm = Z.to_nat num_priorities⌝)
      → ∃ () : (), ((find_highest_prio bm) @ (int (i32))); (p ◁ₗ (bm @ (prio_bitmap_t))).

  (* Specifications for function [priority_search_none_found]. *)
  Definition type_of_priority_search_none_found :=
    fn(∀ res : Z; (res @ (int (i32))); True)
      → ∃ () : (), ((bool_decide (res < 0)) @ (boolean (i32))); True.

  (* Specifications for function [priority_level_set]. *)
  Definition type_of_priority_level_set :=
    fn(∀ (p, priority, bm) : loc * Z * (list bool); (p @ (&own (bm @ (prio_bitmap_t)))), (priority @ (int (u8))); ⌜priority < num_priorities⌝ ∗ ⌜0 <= priority⌝)
      → ∃ () : (), (void); (p ◁ₗ ((<[Z.to_nat priority := true]> bm) @ (prio_bitmap_t))).

  (* Specifications for function [priority_level_clear]. *)
  Definition type_of_priority_level_clear :=
    fn(∀ (p, priority, bm) : loc * Z * (list bool); (p @ (&own (bm @ (prio_bitmap_t)))), (priority @ (int (u8))); ⌜priority < num_priorities⌝ ∗ ⌜0 <= priority⌝)
      → ∃ () : (), (void); (p ◁ₗ ((<[Z.to_nat priority := false]> bm) @ (prio_bitmap_t))).

  (* Specifications for function [npfp_enqueue]. *)
  Definition type_of_npfp_enqueue :=
    fn(∀ (m_len, l1, l2, sched_state, id) : Z * loc * loc * npfp_sched * packet_ID; (l1 @ (&own (sched_state @ (npfp_t)))), (l2 @ (&own (malloced (ly_size struct_message) (struct (struct_message) [@{type} uninit (u8) ; m_len @ (int (u64)) ; uninit (void*) ; array_p (u8) (get_packet_data id `at_type` (int u8)) (Z.to_nat max_msg_len) ])))); True)
      → ∃ () : (), (void); (l1 ◁ₗ ((let msg := {|m_type := (message_identify_type_coq id);m_length := m_len;m_id := id|} in npfp_enqueue_func sched_state msg) @ (npfp_t))).

  (* Specifications for function [npfp_dequeue]. *)
  Definition type_of_npfp_dequeue :=
    fn(∀ (l1, sched_state) : loc * npfp_sched; (l1 @ (&own (sched_state @ (npfp_t)))); True)
      → ∃ () : (), ((get_highest_prio_msg sched_state) @ (optionalO (λ msg,
        &own (malloced (ly_size struct_message) (msg @ (message (uninit (void*)))))
      ) null)); (l1 ◁ₗ ((npfp_dequeue_func sched_state) @ (npfp_t))).

  (* Function [npfp_dispatch] has been skipped. *)

  (* Specifications for function [fds_init]. *)
  Definition type_of_fds_init :=
    fn(∀ (fds_refn, p) : fd_sched * loc; (p @ (&own (struct (struct_fd_scheduler) [@{type} uninit (mk_array_layout i32 16) ; uninit (u64) ; uninit (struct_npfp_scheduler) ]))); True)
      → ∃ () : (), (void); (p ◁ₗ (({|input_channels :=[];sched_state := initialize_scheduler|}) @ (fd_t))).

  (* Specifications for function [fds_add_channel]. *)
  Definition type_of_fds_add_channel :=
    fn(∀ (fd_state, p, fd) : fd_sched * loc * Z; (p @ (&own (fd_state @ (fd_t)))), (fd @ (int (i32))); ⌜length fd_state.(input_channels) < 16⌝)
      → ∃ () : (), ((0) @ (int (i32))); (p ◁ₗ (((fds_add_channel_func fd_state fd)) @ (fd_t))).

  (* Specifications for function [fds_set_callback]. *)
  Definition type_of_fds_set_callback :=
    fn(∀ (fds, msg_type, prio, p) : fd_sched * nat * nat * loc; (p @ (&own (fds @ (fd_t)))), (msg_type @ (int (u8))), (function_ptr (fn(∀ (msg, q) : message_data * loc;(&own (msg @ (message (uninit (void*)))));True)→∃ () : (), (int (i32));True)), (prio @ (int (u8))); ⌜msg_type < num_msg_types⌝ ∗ ⌜prio < num_priorities⌝)
      → ∃ () : (), (void); (p ◁ₗ (((fds_set_callback_func fds msg_type prio)) @ (fd_t))).

  (* Function [fds_run] has been skipped. *)

  (* Specifications for function [safe_exit]. *)
  Definition type_of_safe_exit :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜False⌝.

  (* Specifications for function [malloc]. *)
  Definition type_of_malloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (optionalO (λ _ : unit,
        &own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))
      ) (null)); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ n : Z; (&own (malloced_early (n) (uninit (ly_max_align (Z.to_nat n))))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [xmalloc]. *)
  Definition type_of_xmalloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (&own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))); True.

  (* Specifications for function [nop_callback]. *)
  Definition type_of_nop_callback :=
    fn(∀ (msg, q) : message_data * loc; (&own (msg @ (message (uninit (void*))))); True)
      → ∃ () : (), (int (i32)); True.

  (* Specifications for function [receive_one_message]. *)
  Definition type_of_receive_one_message :=
    fn(∀ (fd_state, p1, fd, t1, errno) : fd_sched * loc * Z * nat * Z; (p1 @ (&own (fd_state @ (fd_t)))), (fd @ (int (i32))); (curr_read_index t1) ∗ (is_errno errno))
      → ∃ n : Z, ((if (bool_decide $ is_Some $ (packet_arrivals fd t1)) then 0 else -1) @ (int (i32))); (curr_read_index (t1 + 1)%nat) ∗ (p1 ◁ₗ ((receive_one_message_func t1 fd fd_state) @ (fd_t))) ∗ (is_errno n) ∗ ⌜if (bool_decide $ is_Some $ (packet_arrivals fd t1)) then True else n = 80⌝.

  (* Specifications for function [receive_messages]. *)
  Definition type_of_receive_messages :=
    fn(∀ (fd_state, p1, fd, t1, errno) : fd_sched * loc * Z * nat * Z; (p1 @ (&own (fd_state @ (fd_t)))), (fd @ (int (i32))); (curr_read_index t1) ∗ (is_errno errno))
      → ∃ (m, flag, errno) : nat * Z * Z, (flag @ (int (i32))); (curr_read_index (t1 + (S m))) ∗ (is_errno errno) ∗ ⌜fd_has_n_msgs fd m t1⌝ ∗ ⌜flag = bool_to_Z (bool_decide (m <> 0))%nat⌝ ∗ (p1 ◁ₗ ((receive_n_messages_func t1 fd fd_state (S m)) @ (fd_t))).

  (* Specifications for function [check_channels]. *)
  Definition type_of_check_channels :=
    fn(∀ (fd_state, p1, t1, errno) : fd_sched * loc * nat * Z; (p1 @ (&own (fd_state @ (fd_t)))); (curr_read_index t1) ∗ (is_errno errno))
      → ∃ (ns, flag, errno) : (list nat) * Z * Z, (flag @ (int (i32))); (curr_read_index (t1 + num_reads_for_ns ns)%nat) ∗ (is_errno errno) ∗ ⌜flag = bool_to_Z (bool_decide (Exists (λ n, (n <> 0)%nat) ns))⌝ ∗ (p1 ◁ₗ ((check_n_channels_func t1 fd_state (length (input_channels fd_state)) ns) @ (fd_t))) ∗ ⌜fds_have_n_msgs (input_channels fd_state) ns t1⌝.

  (* Specifications for function [check_channels_until_empty]. *)
  Definition type_of_check_channels_until_empty :=
    fn(∀ (fd_state, p1, t1, errno) : fd_sched * loc * nat * Z; (p1 @ (&own (fd_state @ (fd_t)))); (curr_read_index t1) ∗ (is_errno errno))
      → ∃ ns_list : (list (list nat)), ((0) @ (int (i32))); (curr_read_index (t1 + num_reads_for_ns_list ns_list)) ∗ (p1 ◁ₗ ((check_channels_until_empty_func t1 fd_state ns_list) @ (fd_t))) ∗ ⌜fds_have_ns_list_msgs_done (input_channels fd_state) ns_list t1⌝.
End spec.

Notation "message< cont >" := (message cont)
  (only printing, format "'message<' cont '>'") : printing_sugar.

Global Typeclasses Opaque message_rec.
Global Typeclasses Opaque message.
Global Typeclasses Opaque message_queue_rec.
Global Typeclasses Opaque message_queue.
Global Typeclasses Opaque prio_bitmap_t_rec.
Global Typeclasses Opaque prio_bitmap_t.
Global Typeclasses Opaque callback_t_rec.
Global Typeclasses Opaque callback_t.
Global Typeclasses Opaque npfp_t_rec.
Global Typeclasses Opaque npfp_t.
Global Typeclasses Opaque fd_t_rec.
Global Typeclasses Opaque fd_t.
