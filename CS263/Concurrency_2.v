Require Import Coq.Lists.List.
Require Import PL.Imp3.
Require Import PL.ImpExt4.
Local Open Scope Z.

(* ################################################################# *)
(** * Review *)

(** Last time, we have introduced a programming language with parallel
    composition. *)

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CPar (c1 c2: com) (* <- new *)
  .

Bind Scope imp_scope with com.
Notation "'Skip'" :=
   CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (CIf c1 c2 c3) (at level 10, right associativity) : imp_scope.
Local Open Scope imp.

(** We introduced its small step semantics. *)

Module SmallStepSemantics.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2,
      cstep (Skip ;; c2, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st)
  | CS_ParLeft: forall st st' c1 c1' c2,
      cstep (c1, st) (c1', st') ->
      cstep (CPar c1 c2, st) (CPar c1' c2, st')
  | CS_ParRight: forall st st' c1 c2 c2',
      cstep (c2, st) (c2', st') ->
      cstep (CPar c1 c2, st) (CPar c1 c2', st')
  | CS_Par: forall st,
      cstep (CPar Skip Skip, st) (Skip, st).

End SmallStepSemantics.

(* ################################################################# *)
(** * Denotational Semantics *)

(** Obviously, original denotational semantics does not work. If using initial
    state and ending state pairs as denotations, then

    - [X ::= 1]

    - [X ::= 2;; X ::= 1]

    have the same denotations. However, parallelly executing one of them and

    - [Y ::= X]

    may have different results. That means, this ordinary approach is not
    expressive enough. In the following part of this lecture, we will use trace
    sets to describe all intermediate states. *)

Module DenotationalSemantics_Trace.

(** Here, we use a combination of

    - initial state

    - intermediate states

    - ending state

    to represent an execution trace. But we do not only consider the behavior of
    one program itself. We only consider potential behavior of other threads, we
    call that environment's behavior. Specifically, we distinguish thread local
    actions and envirionment actions. *)

Inductive abs_thread :=
| LOCAL
| ENVIR.

Definition trace_set := state -> list (abs_thread * state) -> state -> Prop.

Inductive environ_trace: trace_set :=
| environ_trace_nil: forall st, environ_trace st nil st
| environ_trace_cons: forall st1 st2 st3 tr,
    environ_trace st2 tr st3 ->
    environ_trace st1 ((ENVIR, st2) :: tr) st3.

Definition seq_sem (d1 d2: trace_set): trace_set :=
  fun st1 tr st3 =>
    exists tr1 tr2 st2,
      d1 st1 tr1 st2 /\ d2 st2 tr2 st3 /\ tr = tr1 ++ tr2.

Definition union_sem (d d': trace_set): trace_set :=
  fun st1 tr st2 =>
    d st1 tr st2 \/ d' st1 tr st2.

Definition omega_union_sem (d: nat -> trace_set): trace_set :=
  fun st1 tr st2 => exists n, d n st1 tr st2.

(** The most interesting case is to define parallel compositions' behavior. *)

Inductive interleave_trace:
  list (abs_thread * state) ->
  list (abs_thread * state) ->
  list (abs_thread * state) ->
  Prop :=
| interleave_nil: interleave_trace nil nil nil
| interleave_cons_l: forall tr1 tr2 tr3 st,
    interleave_trace tr1 tr2 tr3 ->
    interleave_trace ((LOCAL, st) :: tr1) ((ENVIR, st) :: tr2) ((LOCAL, st) :: tr3)
| interleave_cons_r: forall tr1 tr2 tr3 st,
    interleave_trace tr1 tr2 tr3 ->
    interleave_trace ((ENVIR, st) :: tr1) ((LOCAL, st) :: tr2) ((LOCAL, st) :: tr3)
| interleave_cons_env: forall tr1 tr2 tr3 st,
    interleave_trace tr1 tr2 tr3 ->
    interleave_trace ((ENVIR, st) :: tr1) ((ENVIR, st) :: tr2) ((ENVIR, st) :: tr3).

Definition par_sem (d1 d2: trace_set): trace_set :=
  fun st1 tr st2 =>
    exists tr1 tr2,
      d1 st1 tr1 st2 /\ d2 st1 tr2 st2 /\ interleave_trace tr1 tr2 tr.

Module DenotationalSemantics_MiddleStepTrace.
  
Definition skip_sem: state -> list (abs_thread * state) -> state -> Prop :=
  environ_trace.

Definition local_asgn_sem (X: var) (E: aexp): trace_set :=
  fun st1 tr st2 =>
    st2 X = aeval E st1 /\
    (forall Y, X <> Y -> st1 Y = st2 Y) /\
    tr = (LOCAL, st2) :: nil.

Definition asgn_sem (X: var) (E: aexp): trace_set :=
  seq_sem environ_trace (seq_sem (local_asgn_sem X E) environ_trace).

Definition local_test_sem (X: state -> Prop): trace_set :=
  fun st1 tr st2 =>
    st1 = st2 /\ tr = (LOCAL, st1) :: nil /\ X st1.

Definition if_sem (b: bexp) (d1 d2: trace_set): trace_set :=
  union_sem
    (seq_sem environ_trace (seq_sem (local_test_sem (beval b)) d1))
    (seq_sem environ_trace (seq_sem (local_test_sem (beval (! b))) d2)).

Fixpoint iter_loop_body (b: bexp) (loop_body: trace_set) (n: nat): trace_set :=
  match n with
  | O => local_test_sem (beval (! b))
  | S n' => seq_sem
              (local_test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: trace_set): trace_set :=
  seq_sem
    environ_trace
    (seq_sem (omega_union_sem (iter_loop_body b loop_body)) environ_trace).

Fixpoint ceval (c: com): trace_set :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | CPar c1 c2 => par_sem (ceval c1) (ceval c2)
  end.

End DenotationalSemantics_MiddleStepTrace.

Module DenotationalSemantics_SmallStepTrace.

(** In the definitions above, we actually assume that an assignment or an
    testing can happen in one instant. However, you may think it is not true
    because evaluating an expression needs to read program variables' values.
    That does not happen instantly. Due to that consideration, we may choose
    an alternative semantics. *)

Local Open Scope Z.

Definition ANum_sem (n: Z): Z -> trace_set :=
  fun res st1 tr st2 =>
    environ_trace st1 tr st2 /\ res = n.

Definition local_AId_sem (X: var): Z -> trace_set :=
  fun res st1 tr st2 =>
    st1 = st2 /\ tr = (LOCAL, st1) :: nil /\ res = st1 X.

Definition AId_sem (X: var): Z -> trace_set :=
  fun res =>
    seq_sem environ_trace (seq_sem (local_AId_sem X res) environ_trace).

Definition APlus_sem (d1 d2: Z -> trace_set): Z -> trace_set :=
  fun res st1 tr st2 =>
    exists res1 res2,
      seq_sem (d1 res1) (d2 res2) st1 tr st2 /\ res = res1 + res2.

Definition AMinus_sem (d1 d2: Z -> trace_set): Z -> trace_set :=
  fun res st1 tr st2 =>
    exists res1 res2,
      seq_sem (d1 res1) (d2 res2) st1 tr st2 /\ res = res1 - res2.

Definition AMult_sem (d1 d2: Z -> trace_set): Z -> trace_set :=
  fun res st1 tr st2 =>
    exists res1 res2,
      seq_sem (d1 res1) (d2 res2) st1 tr st2 /\ res = res1 * res2.

Fixpoint aeval (a: aexp): Z -> trace_set :=
  match a with
  | ANum n => ANum_sem n
  | AId X => AId_sem X
  | APlus a1 a2 => APlus_sem (aeval a1) (aeval a2)
  | AMinus a1 a2 => AMinus_sem (aeval a1) (aeval a2)
  | AMult a1 a2 => AMult_sem (aeval a1) (aeval a2)
  end.

Definition BEq_sem (d1 d2: Z -> trace_set): bool -> trace_set :=
  fun res st1 tr st2 =>
    exists res1 res2,
      seq_sem (d1 res1) (d2 res2) st1 tr st2 /\ (res = true <-> res1 = res2).

Definition BLe_sem (d1 d2: Z -> trace_set): bool -> trace_set :=
  fun res st1 tr st2 =>
    exists res1 res2,
      seq_sem (d1 res1) (d2 res2) st1 tr st2 /\ (res = true <-> res1 <= res2).

Definition BTrue_sem: bool -> trace_set :=
  fun res st1 tr st2 =>
    environ_trace st1 tr st2 /\ res = true.

Definition BFalse_sem: bool -> trace_set :=
  fun res st1 tr st2 =>
    environ_trace st1 tr st2 /\ res = false.

Definition BNot_sem (d: bool -> trace_set) : bool -> trace_set :=
  fun res st1 tr st2 =>
    exists res',
      d res' st1 tr st2 /\ res = negb res'.

Definition BAnd_sem (d1 d2: bool -> trace_set) : bool -> trace_set :=
  fun res st1 tr st2 =>
    (d1 false st1 tr st2 /\ res = false) \/
    (seq_sem (d1 true) (d2 res) st1 tr st2).

Fixpoint beval (b: bexp): bool -> trace_set :=
  match b with
  | BEq a1 a2 => BEq_sem (aeval a1) (aeval a2)
  | BLe a1 a2 => BLe_sem (aeval a1) (aeval a2)
  | BTrue => BTrue_sem
  | BFalse => BFalse_sem
  | BNot b0 => BNot_sem (beval b0)
  | BAnd b1 b2 => BAnd_sem (beval b1) (beval b2)
  end.

Definition skip_sem: state -> list (abs_thread * state) -> state -> Prop :=
  environ_trace.

Definition local_asgn_sem (X: var) (n: Z): trace_set :=
  fun st1 tr st2 =>
    st2 X = n /\
    (forall Y, X <> Y -> st1 Y = st2 Y) /\
    tr = (LOCAL, st2) :: nil.

Definition asgn_sem (X: var) (E: aexp): trace_set :=
  fun st1 tr st2 =>
    exists n,
      seq_sem (aeval E n) (seq_sem (local_asgn_sem X n) environ_trace) st1 tr st2.

Definition if_sem (b: bexp) (d1 d2: trace_set): trace_set :=
  union_sem
    (seq_sem (beval b true) d1)
    (seq_sem (beval b false) d2).

Fixpoint iter_loop_body (b: bexp) (loop_body: trace_set) (n: nat): trace_set :=
  match n with
  | O => beval b false
  | S n' => seq_sem
              (beval b true)
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: trace_set): trace_set :=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): trace_set :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | CPar c1 c2 => par_sem (ceval c1) (ceval c2)
  end.

End DenotationalSemantics_SmallStepTrace.
End DenotationalSemantics_Trace.

(* ################################################################# *)
(** * Hoare Logic *)

(** For axiomatic semantics, we introduce an extension of Hoare logic here, the
    logic of _rely-guanrantee_ (依赖保证). Sometimes we write RG for simplicity.
    In short, rely is a set of actions that the environment may take. Guanrantee
    is a promise that the local thread make: "I will only take these actions." *)

Module HoareLogic.

Import Assertion_D.

(** Here,
    
    - [stable P R] means if a program state statisfies [P] then it will still
      satisfy [P] if an action in [R] is taken;

    - [permit P X E G] means if a program state statisfies [P] then [X ::= E]
      is an action permit by [G].

*)

Class Actions : Type := {
  action_set: Type;
  action_union: action_set -> action_set -> action_set;
  stable: Assertion -> action_set -> Prop;
  permit: Assertion -> var -> aexp -> action_set -> Prop
}.

Inductive hoare_triple {A: Actions}: Type :=
| Build_hoare_triple
    (R: action_set)
    (G: action_set)
    (P: Assertion)
    (c: com)
    (Q: Assertion).

Reserved Notation "R :; G |-- {{ P }}  c  {{ Q }}"
  (at level 90, G at next level, P at next level, c at next level, Q at next level).

Inductive provable {A: Actions} {T: FirstOrderLogic}: hoare_triple -> Prop :=
  | hoare_seq : forall R G (P1 P2 P3: Assertion) (c1 c2: com),
      R :; G |-- {{P1}} c1 {{P2}} ->
      R :; G |-- {{P2}} c2 {{P3}} ->
      R :; G |-- {{P1}} (CSeq c1 c2) {{P3}}
  | hoare_skip : forall R G P,
      stable P R ->
      R :; G |-- {{P}} CSkip {{P}}
  | hoare_if : forall R G P Q (b: bexp) c1 c2,
      R :; G |-- {{ P AND {[b]} }} c1 {{ Q }} ->
      R :; G |-- {{ P AND NOT {[b]} }} c2 {{ Q }} ->
      R :; G |-- {{ P }} CIf b c1 c2 {{ Q }}
  | hoare_while : forall R G P (b: bexp) c,
      stable (P AND NOT {[b]}) R ->
      R :; G |-- {{ P AND {[b]} }} c {{P}} ->
      R :; G |-- {{P}} CWhile b c {{ P AND NOT {[b]} }}
  | hoare_asgn_bwd : forall R G P (X: var) (E: aexp),
      stable (P [ X |-> E ]) R ->
      stable P R ->
      permit (P [ X |-> E ]) X E G ->
      R :; G |-- {{ P [ X |-> E] }} CAss X E {{ P }}
  | hoare_par : forall G1 G2 R P c1 c2 Q,
      G1 :; action_union G2 R |-- {{ P }} c1 {{ Q }} ->
      G2 :; action_union G1 R |-- {{ P }} c2 {{ Q }} ->
      action_union G1 G2 :; R |-- {{ P }} CPar c1 c2 {{ Q }}
  | hoare_consequence : forall R G (P P' Q Q' : Assertion) c,
      stable P R ->
      stable Q R ->
      P |-- P' ->
      R :; G |-- {{P'}} c {{Q'}} ->
      Q' |-- Q ->
      R :; G |-- {{P}} c {{Q}}
where "R :; G |-- {{ P }}  c  {{ Q }}" :=
  (provable (Build_hoare_triple R G P (c%imp) Q)).

End HoareLogic.

(* Wed Jun 10 23:33:23 CST 2020 *)
