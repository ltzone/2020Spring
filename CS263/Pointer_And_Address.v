Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.

Open Scope Z.

(* ################################################################# *)
(** * A Language With Addresses And Pointers *)

(** In this lecture, we consider a typical programming language, extending the
    simple imperative language with _addresses_ (地址) and _pointers_ (指针).
    We still use their indices to represent variables and add two operators to
    the programming language: dereference and address-of.

    Dereferece is like the "*" operator in C, e.g. [ x = * y; ]. Address-of is
    like the "&" operator in C, e.g. [y = & x]. *)

Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADeref (a1: aexp)            (* <-- new *)
  | AAddr (a1: aexp).            (* <-- new *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAss (a1 a2 : aexp)          (* <-- new *)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Module Example1.

(** We suppose that [X] and [Y] are variable #0 and #1. *)

Definition X := 0%nat.
Definition Y := 1%nat.

(** Here is some sample expressions and command. *)

Example aexp_sample: aexp := ADeref (APlus (AAddr (AId X)) (ANum 1)).
  (* It is like the C expression: [ * (& x + 1) ]. *)

Example bexp_sample: bexp := BEq (ADeref (AId X)) (ADeref (AId X)).
  (* It is like the C expression: [ * x == * y ]. *)

Example com_sample1: com :=
  CAss (ADeref (AId X)) (APlus (ADeref (AId X)) (ANum 1)).
  (* It is like the C program: [ ( * x ) ++; ]. *)

Example com_sample2: com :=
  CWhile (BNot (BEq (AId X) (ANum 0)))
         (CSeq (CAss (AId Y) (APlus (AId Y) (ANum 1)))
               (CAss (AId X) (ADeref (AId X)))).
  (* It is like the C program: [ while (x != 0) { y ++; x = * x; } ]. *)

End Example1.

(* ################################################################# *)
(** * Expressions' Denotations *)

(** In order to make the program state model simple, we assume the value of
    program variable [#n] is stored at address [n + 1]. A program state is a
    partial mapping from addresses to values. It is a partial function instead
    of a total functions since some addresses may be invalid. *)

Definition var2addr (X: var): Z := Z.of_nat X + 1.

Definition state: Type := Z -> option Z.

(** In order to define a denotational semantics, we define two functions for
    expression evaluation: [aevalR] and [aevalL]. They define expressions'
    _rvalue_ (右值) and _lvalue_ (左值). Rvalues are the values for computation
    and lvalues are the addresses for reading and writing. We introduce [aevalR]
    and [aevalL] by a mutually inductive definition. *)

Inductive aevalR : aexp -> state -> Z -> Prop :=
  | E_ANum n st:
      aevalR (ANum n) st n
  | E_AId X st n:
      st (var2addr X) = Some n ->
      aevalR (AId X) st n
  | E_APlus (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2) :
      aevalR (APlus e1 e2) st (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2) :
      aevalR (AMinus e1 e2) st (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2) :
      aevalR (AMult e1 e2) st (n1 * n2)
  | E_ADeref (e1: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : st n1 = Some n2) :
      aevalR (ADeref e1) st n2
  | E_AAddr (e1: aexp) (n1: Z) st
      (H1 : aevalL e1 st n1):
      aevalR (AAddr e1) st n1
with aevalL : aexp -> state -> Z -> Prop :=
  | EL_AId X st:
      aevalL (AId X) st (var2addr X)
  | EL_ADeref (e1: aexp) (n1: Z) st
      (H1 : aevalR e1 st n1) :
      aevalL (ADeref e1) st n1.

Inductive beval : bexp -> state -> bool -> Prop :=
  | E_BTrue st:
      beval BTrue st true
  | E_BFalse st:
      beval BFalse st false
  | E_BEqTrue (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2)
      (H3 : n1 = n2) :
      beval (BEq e1 e2) st true
  | E_BEqFalse (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2)
      (H3 : n1 <> n2) :
      beval (BEq e1 e2) st false
  | E_BLeTrue (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2)
      (H3 : n1 <= n2) :
      beval (BLe e1 e2) st true
  | E_BLeFalse (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2)
      (H3 : n1 > n2) :
      beval (BLe e1 e2) st false
  | E_BNot (e: bexp) (b: bool) st
      (H1 : beval e st b):
      beval (BNot e) st (negb b)
  | E_BAndTrue (e1 e2: bexp) (b2: bool) st
      (H1 : beval e1 st true)
      (H2 : beval e2 st b2):
      beval (BAnd e1 e2) st b2
  | E_BAndFalse (e1 e2: bexp) st
      (H1 : beval e1 st false):
      beval (BAnd e1 e2) st false.

Module Example2.

(** The following statements are all straightforward if you know a little bit
about C programming. The point here is not to persuad yourself that they are
correct. It is rather important to see that we can formally prove them under
our definitions above. We suppose that [X] and [Y] are variable #0 and #1. *)

Definition X := 0%nat.
Definition Y := 1%nat.

(** Suppose [st] is a program state such that the values stored on [X] and [Y]
are 100 and 99. Also, we assume that the value stored on address 99 and 100 are
both 0, and 0 is a null address. *)

Parameter st: state.
Hypothesis stX: st (var2addr X) = Some 100.
Hypothesis stY: st (var2addr Y) = Some 99.
Hypothesis st99: st 99 = Some 0.
Hypothesis st100: st 100 = Some 0.
Hypothesis st0: st 0 = None.

(** Here are two basic statements. *)

Fact ex1: aevalR (AId X) st 100.
Proof. apply E_AId. apply stX. Qed.

Fact ex2: aevalR (AId Y) st 99.
Proof. apply E_AId. apply stY. Qed.

(** The following statements talk about [X] and [Y]'s address. *)

Fact ex3: aevalL (AId X) st 1.
Proof. apply EL_AId. Qed.

Fact ex4: aevalL (AId Y) st 2.
Proof. apply EL_AId. Qed.

Fact ex5: aevalR (AAddr (AId X)) st 1.
Proof. apply E_AAddr. apply EL_AId. Qed.

Fact ex6: aevalR (AAddr (AId Y)) st 2.
Proof. apply E_AAddr. apply EL_AId. Qed.

(** We can also use the values stored in [X] and [Y] as addresses. *)

Fact ex7: aevalR (ADeref (AId X)) st 0. (* The value of expreesion [* X]. *)
Proof. eapply E_ADeref. apply E_AId. apply stX. apply st100. Qed.

Fact ex8: aevalR (ADeref (AId Y)) st 0. (* The value of expreesion [* Y]. *)
Proof. eapply E_ADeref. apply E_AId. apply stY. apply st99. Qed.

(** It is not too weird to talk about dereference of dereference. *)

Fact ex9: forall v, ~ aevalR (ADeref (ADeref (AId X))) st v.
(* The value of expreesion [* * X]. *)
Proof.
  intros.
  destruct (classic (aevalR (ADeref (ADeref (AId X))) st v));
    [exfalso | tauto].
  inversion H; subst.
  inversion H0; subst.
  inversion H3; subst.
  rewrite stX in H5.
  injection H5 as ?.
  subst n0.
  rewrite st100 in H4.
  injection H4 as ?.
  subst n1.
  rewrite st0 in H2.
  discriminate H2.
Qed.

End Example2.

(* ################################################################# *)
(** * Programs' Denotations *)

(** The interesting cases below are about assignment commands. Specifically,
an assignment command may fail in 3 different way: l-value evaluation fails;
rvalue evaluation fails; the address to write is not available. *)

Inductive ceval : com -> state -> option state -> Prop :=
  | E_Skip st:
      ceval CSkip st (Some st)
  | E_AssSucc st1 st2 E E' n n'                            (* <-- new *)
      (H1: aevalL E st1 n)
      (H2: aevalR E' st1 n')
      (H3: st1 n <> None)
      (H4: st2 n = Some n')
      (H5: forall n'', n <> n'' -> st1 n'' = st2 n''):
      ceval (CAss E E') st1 (Some st2)
  | E_AssFail1 st1 E E'                                    (* <-- new *)
      (H1: forall n, ~aevalL E st1 n):
      ceval (CAss E E') st1 None
  | E_AssFail2 st1 E E'                                    (* <-- new *)
      (H1: forall n', ~aevalR E' st1 n'):
      ceval (CAss E E') st1 None
  | E_AssFail3 st1 E E' n                                  (* <-- new *)
      (H1: aevalL E st1 n)
      (H2: st1 n = None):
      ceval (CAss E E') st1 None
  | E_SeqSafe c1 c2 st st' o
      (H1: ceval c1 st (Some st'))
      (H2: ceval c2 st' o):
      ceval (CSeq c1 c2) st o
  | E_SeqCrush c1 c2 st
      (H1: ceval c1 st None):
      ceval (CSeq c1 c2) st None
  | E_IfTrue st o b c1 c2
      (H1: beval b st true)
      (H2: ceval c1 st o):
      ceval (CIf b c1 c2) st o
  | E_IfFalse st o b c1 c2
      (H1: beval b st false)
      (H2: ceval c2 st o):
      ceval (CIf b c1 c2) st o
  | E_IfFail st b c1 c2
      (H1: ~ beval b st true)
      (H2: ~ beval b st false):
      ceval (CIf b c1 c2) st None
  | E_WhileFalse b st c
      (H1: beval b st false):
      ceval (CWhile b c) st (Some st)
  | E_WhileTrue st o b c
      (H1: beval b st true)
      (H2: ceval (CSeq c (CWhile b c)) st o):
      ceval (CWhile b c) st o
  | E_WhileFail st b c
      (H1: ~ beval b st true)
      (H2: ~ beval b st false):
      ceval (CWhile b c) st None.

(* ################################################################# *)
(** * Small Step Semantics for Expression Evaluation *)

Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astepR : state -> aexp -> aexp -> Prop :=
  | ASR_Id : forall st X n,
      st (var2addr X) = Some n ->
      astepR st
        (AId X) (ANum n)

  | ASR_Plus1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      astepR st
        (APlus a1 a2) (APlus a1' a2)
  | ASR_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      astepR st
        (APlus a1 a2) (APlus a1 a2')
  | ASR_Plus : forall st n1 n2,
      astepR st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | ASR_Minus1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      astepR st
        (AMinus a1 a2) (AMinus a1' a2)
  | ASR_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      astepR st
        (AMinus a1 a2) (AMinus a1 a2')
  | ASR_Minus : forall st n1 n2,
      astepR st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | ASR_Mult1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      astepR st
        (AMult a1 a2) (AMult a1' a2)
  | ASR_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      astepR st
        (AMult a1 a2) (AMult a1 a2')
  | ASR_Mult : forall st n1 n2,
      astepR st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2))

  | ASR_DerefStep : forall st a1 a1',
      astepR st
        a1 a1' ->
      astepR st
        (ADeref a1) (ADeref a1')
  | ASR_Deref : forall st n n',
      st n = Some n' ->
      astepR st
        (ADeref (ANum n)) (ANum n')

  | ASR_AddrStep : forall st a1 a1',
      astepL st
        a1 a1' ->
      astepR st
        (AAddr a1) (AAddr a1')
  | ASR_Addr : forall st n,
      astepR st
        (AAddr (ADeref (ANum n))) (ANum n)
with astepL : state -> aexp -> aexp -> Prop :=
  | ASL_Id: forall st X,
      astepL st
        (AId X) (ADeref (ANum (var2addr X)))

  | ASL_DerefStep: forall st a1 a1',
      astepR st
        a1 a1' ->
      astepL st
        (ADeref a1) (ADeref a1')
.

Inductive bstep : state -> bexp -> bexp -> Prop :=

  | BS_Eq1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      bstep st
        (BEq a1 a2) (BEq a1 a2')
  | BS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BTrue
  | BS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BFalse

  | BS_Le1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      bstep st
        (BLe a1 a2) (BLe a1 a2')
  | BS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BTrue
  | BS_Le_False : forall st n1 n2,
      n1 > n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BFalse

  | BS_NotStep : forall st b1 b1',
      bstep st
        b1 b1' ->
      bstep st
        (BNot b1) (BNot b1')
  | BS_NotTrue : forall st,
      bstep st
        (BNot BTrue) BFalse
  | BS_NotFalse : forall st,
      bstep st
        (BNot BFalse) BTrue

  | BS_AndStep : forall st b1 b1' b2,
      bstep st
        b1 b1' ->
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st
       (BAnd BFalse b) BFalse.

(** Here, we assume [BAnd] expressions use short circuit evaluation. *)

(* ################################################################# *)
(** * Small Step Semantics for Program Execution *)

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep1 st E1 E1' E2                                (* <-- new *)
      (H1: astepL st E1 E1'):
      cstep (CAss E1 E2, st) (CAss E1' E2, st)
  | CS_AssStep2 st n E2 E2'                                 (* <-- new *)
      (H1: astepR st E2 E2'):
      cstep (CAss (ADeref (ANum n)) E2, st) (CAss (ADeref (ANum n)) E2', st)
  | CS_Ass st1 st2 n1 n2                                    (* <-- new *)
      (H1: st1 n1 <> None)
      (H2: st2 n1 = Some n2)
      (H3: forall n, n1 <> n -> st1 n = st2 n):
      cstep (CAss (ADeref (ANum n1)) (ANum n2), st1) (CSkip, st2)
  | CS_SeqStep st c1 c1' st' c2
      (H1: cstep (c1, st) (c1', st')):
      cstep (CSeq c1 c2 , st) (CSeq c1' c2, st')
  | CS_Seq st c2:
      cstep (CSeq CSkip c2, st) (c2, st)
  | CS_IfStep st b b' c1 c2
      (H1: bstep st b b'):
      cstep (CIf b c1 c2, st) (CIf b' c1 c2, st)
  | CS_IfTrue st c1 c2:
      cstep (CIf BTrue c1 c2, st) (c1, st)
  | CS_IfFalse st c1 c2:
      cstep (CIf BFalse c1 c2, st) (c2, st)
  | CS_While st b c:
      cstep
        (CWhile b c, st)
        (CIf b (CSeq c (CWhile b c)) CSkip, st).

(* ################################################################# *)
(** * Discussion: Type Safety *)

(** Is this programming language a safe one? Definitely no. There are several
    kinds of errors that may happen.

    The first is illegal assignments. In the C language, [ x + 1 = 0 ] is an
    illegal assignment. In our language, the corresponding syntax tree is

        - [CAss (APlus (AId X) (ANum 1)) (ANum 0).]

    It causes error because its left hand side is not an lvalue. We do not want
    to call it a run-time-error because it should be detected at compile time.

    
    The second is illegal dereferece. When we want to read or write on address
    [n] but this address is not accessible, it is a run time error. It is hard
    to completely get rid of this kind of errors at compile time. *)

(* Thu May 21 00:37:03 CST 2020 *)
