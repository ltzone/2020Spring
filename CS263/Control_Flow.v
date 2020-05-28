Require Import Coq.Lists.List.
Require Import PL.Imp3.

(* ################################################################# *)
(** * The language *)

(** Now, let's consider a programming language with [break] and [continue]
commands.

The majority of our definition remains the same with the language in [Imp].
We only add two kinds of commands to the definition of [com]: *)

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CBreak                       (* <--- new *)
  | CCont                        (* <--- new *)
  .

(** In this lecture, we discover how to defines its Hoare logic, denotational
semantics and small step semantics.

Obviously, the functionalities of [Break] and [Skip] are different. But they
look the same if only considering their modification on program states: neither
of them modify program states. The difference between them is about determining
which command will be executed next. This is called _control flow_. *)

(* ################################################################# *)
(** * Denotational Semantics *)

(** We start from denotational semantics. *)

Module Denotation_With_ControlFlow.

(** Program's denotation is defined as a ternary relation. Specifically,
[st1, ek, st2] belongs to the denotation of program [c] if and only if
executing [c] from [st1] may terminate at state [st2] with exit kind [ek]. *)

Inductive exit_kind: Type :=
  | EK_Normal
  | EK_Break
  | EK_Cont.

Definition skip_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Normal.

Definition asgn_sem (X: var) (E: aexp): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    ek = EK_Normal.

(** Obviously, skip commands and assignment commands can only terminate normally. *)

Definition break_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Break.

Definition cont_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Cont.

(** In contrast, [CBreak] and [CCont] will never terminate will normal exit. *)

Definition seq_sem (d1 d2: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st3 =>
    (exists st2, d1 st1 EK_Normal st2 /\ d2 st2 ek st3) \/
    (d1 st1 ek st3 /\ ek <> EK_Normal).

(** For sequential composition, the second command will be executed if and only
if the first one terminates normally. *)

Definition test_sem (X: state -> Prop): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ X st1 /\ ek = EK_Normal.

Definition union_sem (d d': state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    d st1 ek st2 \/ d' st1 ek st2.

Definition if_sem (b: bexp) (d1 d2: state -> exit_kind ->state -> Prop)
  : state -> exit_kind ->state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> exit_kind -> state -> Prop)
  (n: nat)
  : state -> exit_kind -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 => exists n, d n st1 ek st2.

Definition loop_sem (b: bexp) (loop_body: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

(** The semantics of branches and loops are similar to our original definitions.
    But remember, a loop itself will never terminate by [break] or [continue]
    although a loop body may break and terminates whole loop's execution. *)

Fixpoint ceval (c: com): state -> exit_kind -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | CBreak => break_sem
  | CCont => cont_sem
  end.

End Denotation_With_ControlFlow.

(* ################################################################# *)
(** * Hoare Logic *)

(** A Hoare logic for [Imp] with [break] and [continue] has multiple
    postconditions. *)

Module Hoare_logic.

Import Assertion_S.

Notation "d [ X |-> a ]" := (assn_sub X a ((d)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a0 [ X |-> a ]" := (aexp_sub X a ((a0)%imp)) (at level 10, X at next level) : imp_scope.

Parameter hoare_triple: Assertion ->
                         com ->
                         Assertion *  (* Normal Postcondition *)
                         Assertion *  (* Break  Postcondition *)
                         Assertion ->  (* Continue Condition *)
                         Prop.

Notation "{{ P }}  c  {{ Q }} {{ QB }} {{ QC }}" :=
  (hoare_triple
     P
     c
     (Q%assert: Assertion, QB%assert: Assertion, QC%assert: Assertion))
  (at level 90, c at next level).

(** This Hoare triple says: if command [c] is started in a state satisfying
assertion [P], and if [c] eventually terminates normally / by break / by 
continue in some final state, then this final state will satisfy assertion
[Q / QB / QC].

All proof rules need to be slightly modified: *)

Axiom hoare_seq : forall (P Q R RB RC: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} {{RB}} {{RC}} ->
  {{Q}} c2 {{R}} {{RB}} {{RC}} ->
  {{P}} CSeq c1 c2 {{R}} {{RB}} {{RC}}.

Axiom hoare_skip : forall P,
  {{P}} CSkip {{P}} {{False}} {{False}}.

Axiom hoare_if : forall P Q QB QC b c1 c2,
  {{ P AND {[b]} }} c1 {{Q}} {{QB}} {{QC}} ->
  {{ P AND NOT {[b]} }} c2 {{Q}} {{QB}} {{QC}} ->
  {{ P }} CIf b c1 c2 {{Q}} {{QB}} {{QC}}.

Axiom hoare_asgn_fwd : forall P (X: var) E,
  {{ P }}
  CAss X E
  {{ EXISTS x, P [X |-> x] AND
               {[AId X]} = {[ E [X |-> x] ]} }}
  {{False}}
  {{False}}.

Axiom hoare_asgn_bwd : forall P (X: var) E,
  {{ P [ X |-> E] }} CAss X E {{ P }} {{False}} {{False}}.

Axiom hoare_consequence : forall (P P' Q Q' QB QB' QC QC' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} {{QB'}} {{QC'}}->
  Q' |-- Q ->
  QB' |-- QB ->
  QC' |-- QC ->
  {{P}} c {{Q}} {{QB}} {{QC}}.

(** The proof rules for break / continue / while is most interesting.
    Specifically, the assumption of [hoare_while] says: if the loop invariant
    [I] and the loop condition [b] is satisfied initially, then executing the
    loop body [c] may have these different results:

    - Terminating normally at some state satisfying the invariant again;

    - Terminating by break at some state satisfying the loop's postcondition
      [P];

    - Terminating by continue at some state satisfying the invariant again;

    - Not terminating.

    The conclusion of [hoare_while] says: if the loop invariant [I] is
    satisfied initially, then the whole loop either does not terminate or
    terminates normally at some state satisfying [ I AND NOT {[ b ]} ] or [P].*)

Axiom hoare_break : forall P,
  {{P}} CBreak {{False}} {{P}} {{False}}.

Axiom hoare_cont : forall P,
  {{P}} CCont {{False}} {{False}} {{P}}.

Axiom hoare_while : forall I P b c,
  {{ I AND {[b]} }} c {{I}} {{P}} {{I}} ->
  {{ I }} CWhile b c {{ P OR (I AND NOT {[b]}) }} {{False}} {{False}}.

End Hoare_logic.

(* ################################################################# *)
(** * Small Step Semantics With Virtual Loop Commands *)

(** We demonstrate two versions of small step semantics, one based on virtual
    loops and one based on control stack. *)

Module Small_Step_Semantics_Virtual_Loop.

(** The main idea of virtual loops is to introduce a different loop command
    [CWhile'] which takes three argument intead of two. [CWhile' c1 b c] means:
    during executing the loop body of [While b Do c Endwhile], [c1] is the
    leftover part of current iteration. [CWhile'] is not something appearing in
    real programs, but is used here for the purpose of describing program
    semantics. *)
  
Inductive com' : Type :=
  | CSkip'
  | CAss' (X: var) (a : aexp)
  | CSeq' (c1 c2 : com')
  | CIf' (b : bexp) (c1 c2 : com')
  | CWhile' (c1: com') (b : bexp) (c : com')  (* <--- the real change *)
  | CBreak'
  | CCont'
  .

(** Of course we can easily define an injection from real programs' syntax trees
    to these auxiliary syntax trees. *)

Fixpoint com_inj (c: com): com' :=
  match c with
  | CSkip => CSkip'
  | CAss X a => CAss' X a
  | CSeq c1 c2 => CSeq' (com_inj c1) (com_inj c2)
  | CIf b c1 c2 => CIf' b (com_inj c1) (com_inj c2)
  | CWhile b c => CWhile' CSkip' b (com_inj c)
  | CBreak => CBreak'
  | CCont => CCont'
  end.

(** Then, in our small step semantics, loops' behavior can be described by rules
    like the followings:

    [

    CS_While : forall st1 st2 c b c1 c2,
      cstep
        (c1, st1)
        (c2, st2) ->
      cstep
        (CWhile' c1 b c, st1)
        (CWhile' c2 b c, st2)

    CS_WhileNormal : forall st b c,
      cstep
        (CWhile' CSkip' b c, st)
        (CWhile' (CIf' b c CBreak') b c, st).

    ]

    Obviously, when a loop body's execution arrive at a break, the whole loop
    should terminate. You may think of the following rule:

    [

    forall b c st,
      cstep
        (CWhile' CBreak' b c, st)
        (CSkip', st)

    ]

    However, this rule above is not good enough because "arriving at a break"
    does not mean that loop body's leftover part is exactly a break. It can be
    anything that start with a break. Thus, we need the following definition. *)

Inductive start_with_break: com'-> Prop :=
| SWB_Break: start_with_break CBreak'
| SWB_Seq: forall c1 c2,
             start_with_break c1 ->
             start_with_break (CSeq' c1 c2).

(** Similarly, we use the following definitions for commands starting with a
    continue. *)

Inductive start_with_cont: com' -> Prop :=
| SWC_Cont: start_with_cont CCont'
| SWC_Seq: forall c1 c2,
             start_with_cont c1 ->
             start_with_cont (CSeq' c1 c2).

(** After all, the small step semantics for control-flow-involved programs can
    be described as follows. *)

Inductive cstep : (com' * state) -> (com' * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep
        (CAss' X a, st)
        (CAss' X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep
        (CAss' X (ANum n), st1)
        (CSkip', st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep
        (c1, st)
        (c1', st') ->
      cstep
        (CSeq' c1 c2, st)
        (CSeq' c1' c2, st')
  | CS_Seq : forall st c2,
      cstep
        (CSeq' CSkip' c2, st)
        (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (CIf' b c1 c2, st)
        (CIf' b' c1 c2, st)
  | CS_IfTrue : forall st c1 c2,
      cstep
        (CIf' BTrue c1 c2, st)
        (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep
        (CIf' BFalse c1 c2, st)
        (c2, st)
  | CS_While : forall st1 st2 c b c1 c2,          (* <-- new *)
      cstep
        (c1, st1)
        (c2, st2) ->
      cstep
        (CWhile' c1 b c, st1)
        (CWhile' c2 b c, st2)
  | CS_WhileNormal : forall st b c,               (* <-- new *)
      cstep
        (CWhile' CSkip' b c, st)
        (CWhile' (CIf' b c CBreak') b c, st)
  | CS_WhileBreak : forall st b c_break c,        (* <-- new *)
      start_with_break c_break ->
      cstep
        (CWhile' c_break b c, st)
        (CSkip', st)
  | CS_WhileCont : forall st b c_cont c,          (* <-- new *)
      start_with_break c_cont ->
      cstep
        (CWhile' c_cont b c, st)
        (CWhile' (CIf' b c CBreak') b c, st)
.

End Small_Step_Semantics_Virtual_Loop.

Module Small_Step_Semantics_Control_Stack.

(** Now we turn to a control-stack-based definition. Here, every element in
    a control stack describe a loop (loop condition and loop body) and an
    after-loop command. *)

Definition cstack: Type := list (bexp * com * com).

(** Similar to our small step semantics via virtual loops, we need some
    auxiliary definitions:

    - a command [c] starts with [break]: [start_with_break c];

    - a command [c] starts with [continue]: [start_with_break c];

    - a command [c] is equivalent with a sequential composition of loop
      [CWhile b c1] and another command [c2]: [start_with_loop c b c1 c2].
*)

Inductive start_with_break: com -> Prop :=
| SWB_Break: start_with_break CBreak
| SWB_Seq: forall c1 c2,
             start_with_break c1 ->
             start_with_break (CSeq c1 c2).

Inductive start_with_cont: com -> Prop :=
| SWC_Cont: start_with_cont CCont
| SWC_Seq: forall c1 c2,
             start_with_cont c1 ->
             start_with_cont (CSeq c1 c2).

Inductive start_with_loop: com -> bexp -> com -> com -> Prop :=
| SWL_While: forall b c, start_with_loop (CWhile b c) b c CSkip
| SWL_Seq: forall c1 b c11 c12 c2,
             start_with_loop c1 b c11 c12 ->
             start_with_loop (CSeq c1 c2) b c11 (CSeq c12 c2).

(** Now, we are ready to define a small step semantics with control stack. In
    the following definition, the most important rules are [CS_While],
    [CS_Skip], [CS_Break] and [CS_Cont]. [CS_While] says: one more program
    context will be pushed into the stack. [CS_Skip] and [CS_Cont] talk about
    the scenarios when a loop body ends normally or ends by a continue.
    [CS_Break] says: when a loop body ends by a break, a program context will
    be popped our from the control stack. *)

Inductive cstep : (com * cstack * state) -> (com * cstack * state) -> Prop :=
  | CS_AssStep : forall st s X a a',
      astep st a a' ->
      cstep
        (CAss X a, s, st)
        (CAss X a', s, st)
  | CS_Ass : forall st1 st2 s X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep
        (CAss X (ANum n), s, st1)
        (CSkip, s, st2)
  | CS_SeqStep : forall st s c1 c1' st' c2,
      cstep
        (c1, s, st)
        (c1', s, st') ->
      cstep
        (CSeq c1 c2, s, st)
        (CSeq c1' c2, s, st')
  | CS_Seq : forall st s c2,
      cstep
        (CSeq CSkip c2, s, st)
        (c2, s, st)
  | CS_IfStep : forall st s b b' c1 c2,
      bstep st b b' ->
      cstep
        (CIf b c1 c2, s, st)
        (CIf b' c1 c2, s, st)
  | CS_IfTrue : forall st s c1 c2,
      cstep
        (CIf BTrue c1 c2, s, st)
        (c1, s, st)
  | CS_IfFalse : forall st s c1 c2,
      cstep
        (CIf BFalse c1 c2, s, st)
        (c2, s, st)
  | CS_While : forall st s c b c1 c2,                 (* <-- new *)
      start_with_loop c b c1 c2 ->
      cstep
        (c, s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Skip : forall st s b c1 c2,                    (* <-- new *)
      cstep
        (CSkip, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Break : forall st s b c1 c2 c,                 (* <-- new *)
      start_with_break c ->
      cstep
        (c, (b, c1, c2) :: s, st)
        (c2, s, st)
  | CS_Cont : forall st s b c1 c2 c,                  (* <-- new *)
      start_with_cont c ->
      cstep
        (c, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
.

End Small_Step_Semantics_Control_Stack.

(* Tue May 12 12:50:28 CST 2020 *)
