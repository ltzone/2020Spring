(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/05/29.                                             *)
(* Due: 2020/06/02, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment9.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment9.vo" file is generated.         *)
(*                                                                   *)
(* 5. Do not copy and paste others' answer.                          *)
(*                                                                   *)
(* 6. Using any theorems and/or tactics provided by Coq's standard   *)
(*    library is allowed in this assignment, if not specified.       *)
(*                                                                   *)
(* 7. When you finish, answer the following question:                *)
(*                                                                   *)
(*      Who did you discuss with when finishing this                 *)
(*      assignment? Your answer to this question will                *)
(*      NOT affect your grade.                                       *)
(*      (* FILL IN YOUR ANSWER HERE AS COMMENT *)                    *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PL.ImpExt4.
Require Import PL.Lambda.

(* ################################################################# *)
(** * Task 1: Mix Typed Expressions *)

Module Task1.
Local Open Scope Z.

(** This is our definition of mix typed expressions. In this task, you need to
    answer questions about their evaluation process and type checking results. *)

Definition var: Type := nat.

Definition state: Type := var -> Z.

Inductive mexp : Type :=
  | MNum (n : Z)
  | MId (X : var)
  | MPlus (a1 a2 : mexp)
  | MMinus (a1 a2 : mexp)
  | MMult (a1 a2 : mexp)
  | MTrue
  | MFalse
  | MEq (a1 a2 : mexp)
  | MLe (a1 a2 : mexp)
  | MNot (b : mexp)
  | MAnd (b1 b2 : mexp)
.

(** Here is some coercion and notations for pretty printing. *)

Declare Scope mexp.
Delimit Scope mexp with mexp.
Local Open Scope mexp.

Coercion MNum : Z >-> mexp.
Coercion MId : var >-> mexp.
Notation "x + y" := (MPlus x y) (at level 50, left associativity) : mexp.
Notation "x - y" := (MMinus x y) (at level 50, left associativity) : mexp.
Notation "x * y" := (MMult x y) (at level 40, left associativity) : mexp.
Notation "x <= y" := (MLe x y) (at level 70, no associativity) : mexp.
Notation "x == y" := (MEq x y) (at level 70, no associativity) : mexp.
Notation "x && y" := (MAnd x y) (at level 40, left associativity) : mexp.
Notation "'!' b" := (MNot b) (at level 39, right associativity) : mexp.
Notation "[ x ; .. ; y ]" := (@cons mexp x .. (@cons mexp y (@nil mexp)) ..).

Module Task1_Examples.

Parameter X: var.
Parameter S: var.
  
(** Suppose [X] and [S] are program variables and [st: state] satisfies:

    - [st X = 0]

    - [st S = 0].

    Please describe the evaluation process of

    - [S + (X == 0)]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_1: list mexp :=
  [ S + (X == 0);
    0 + (X == 0);
    0 + (0 == 0);
    0 + MTrue;
    0 + 1;
    1 ]
.

(** Suppose [X] and [S] are program variables and [st: state] satisfies:

    - [st X = 0]

    - [st S = 0].

    Please describe the evaluation process of

    - [S && (X == 0)]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_2: list mexp :=
  [ S && (X == 0);
    0 && (X == 0) ]
.

End Task1_Examples.

(** **** Exercise: 2 stars, standard  *)

Parameter P: var.
Parameter X: var.

(** Suppose [P] and [X] are program variables and [st: state] satisfies:

    - [st P = 0]

    - [st X = 1].

    Please describe the evaluation process of

    - [(P == 0) && (X && (X + 1))]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_1_1: list mexp := 
  [(P == 0) && (X && (X + 1));
   (0 == 0) && (X && (X + 1));
   MTrue && (X && (X + 1));
   X && (X + 1);
   1 && (X + 1)].
(** [] *)

(** **** Exercise: 2 stars, standard  *)

(** This time, consider a slightly different situation. Suppose [st: state]
    satisfies:

    - [st P = 1]

    - [st X = 1].

    Please describe the evaluation process of

    - [(P == 0) && (X && (X + 1))]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_1_2: list mexp :=
  [(P == 0) && (X && (X + 1));
   (1 == 0) && (X && (X + 1));
   MFalse && (X && (X + 1));
   MFalse].
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Does [(P == 0) && (X && (X + 1))] type check?
    1. Yes. 2. No.
*)

Definition my_answer_1_3: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Does [(P == 0) && (P == 1) && (X && (X + 1))] type check?
    1. Yes. 2. No.
*)

Definition my_answer_1_4: Z := 2.
(** [] *)

Import ListNotations.

(** **** Exercise: 1 star, standard  *)

(** Which of the following statements are correct about [mexp]'s small step
    semantics and type checking function?

    1. Its semantics is type safe since it has the progress property and
       the preservation property.

    2. Every legal expression (according the type checking function) can be
       evaluated safely to the end on any program state and the evaluation
       process will either end in an integer constant or a boolean constant.

    3. If an expression [m: mexp] can be safely evaluated on a state [st],
       then [m] must be a well-typed expression.

    4. If an expression [m: mexp] can be safely evaluated on any state [st],
       then [m] must be a well-typed expression.

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_answer_1_5: list Z := [1;2].
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2: Lambda Expressions *)

Module Task2.
Import LambdaIB.
Local Open Scope Z.
Local Open Scope string.
Notation "[ x ; .. ; y ]" := (@cons tm x .. (@cons tm y (@nil tm)) ..).

(** **** Exercise: 2 stars, standard  *)

(** Please describe the evaluation process of

    - [app
         (app
            (abs "f" (abs "x" (app "f" "x")))
            (abs "x" (app (app Omult "x") "x")))
         2].

    If writing this expression in python, it is:

    - [(lambda f: lambda x: f (x)) (lambda x: x * x) (2)].

*)

Definition process_2_1: list tm :=
  [app
     (app
        (abs "f" (abs "x" (app "f" "x")))
        (abs "x" (app (app Omult "x") "x")))
     2;
  (app
     (abs "x" (app (abs "x" (app (app Omult "x") "x")) "x"))
     2);
   app (abs "x" (app (app Omult "x") "x")) 2;
   app (app Omult 2) 2;
   4].

(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Now you know the evaluation result is 4. Please prove it in Coq. *)

Example result_2_1:
  clos_refl_trans step
    (app
       (app (abs "f" (abs "x" (app "f" "x")))
            (abs "x" (app (app Omult "x") "x")))
       2)
    4.
Proof.
  etransitivity_1n.
  { apply S_app1. apply S_beta. constructor. }
  simpl subst. etransitivity_1n.
  { apply S_beta. constructor. }
  simpl subst. etransitivity_1n.
  { apply S_beta. constructor. }
  simpl subst. etransitivity_1n.
  { apply S_base. constructor. }
  reflexivity. 
Qed. 
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** We usually call [ abs "f" (abs "x" (app "f" "x")) ] the "apply" function. In
    other words, it APPLIES function "f" on "x". Please prove that it is
    well-typed. *)

Example type_2_1: forall T1 T2: ty,
  empty_context |-
    (abs "f" (abs "x" (app "f" "x"))) \in ((T1 ~> T2) ~> T1 ~> T2).
Proof.
  intros.
  apply T_abs.
  apply T_abs.
  eapply T_app;apply T_var;reflexivity.
Qed.

(** **** Exercise: 2 stars, standard  *)

(** Please describe the evaluation process of

    - [app
         (abs "x"
            (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) 1))
         2].

    If writing this expression in Coq, it is like:

    - [ (fun x => if x ?= 0 then 0 else 1) 2 ].

*)

Definition process_2_2: list tm :=
  [app
     (abs "x"
        (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) 1))
     2;
   app (app (app Oifthenelse (app (app Oeq 2) 0)) 0) 1;
   app (app (app Oifthenelse false) 0) 1;
   1 ].
(** [] *)

(** **** Exercise: 2 stars, standard  *)

(** In the example above, the function

    - [ abs "x" (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) 1) ]

    is usually called the "test_zero" function. If it applies to zero, the
    result is zero. If it applies to non-zero, the result is one. Of course,
    it has type [TInt ~> TInt]. But, if you write it in a wrong way, you can
    easily make it ill-typed. For example, the following expression writes:
    if "x" is non-zero, return false instead of one. This must cause a chaos
    in types.

    Hint: in order to prove the following property, you need to use [inversion]
    to trace back through the type derivation. You may use

    - [deduce_types_from_head]

    to speed up. But it will only solve parts, but not all, of the problem. *)

Lemma ill_typed_example: forall Gamma T,
  Gamma |-
    abs "x" (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) false) \in T ->
  False.
Proof.
  intros.
  inversion H;subst.
  deduce_types_from_head H4.
  inversion H3;subst.
  inversion H1;subst.
  inversion H5;subst.
  inversion H7.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** It is a nice property that the small step semantics of lambda expressions
    (as we introduced in lectures) are type safe. In other words, for any
    [t: tm] and [T: ty], if

    - [empty_context |- t \in T]

    then evaluating [t] must be safe. But, is the reverse direction also true?
    In other words, is there such an expression [t] that evaluating [t] is safe
    but no type [T] makes [empty_context |- t \in T] true.

    1. There exists such [t].

    2. There does not exist such [t]. *)

Definition my_choice: Z := 1.
(** [] *)

(** You should start your proof with either one of the following:

    - [ left; split; [reflexivity |] ]

    - [ right; reflexivity ]

*)

Lemma reverse_of_type_safe:
  (my_choice = 1 /\
   exists t t', clos_refl_trans step t t' /\ tm_halt t' /\
                (forall T, empty_context |- t \in T -> False)) \/
  (my_choice = 2).
Proof.
  left; split; [reflexivity |].
  exists (app
            (abs "x" (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) false))
            5), false.
  repeat split;[|constructor|].
  - etransitivity_1n.
    { apply S_beta. constructor. }
    simpl subst. etransitivity_1n.
    { apply S_app1. apply S_app1.
      apply S_app2. constructor.
      apply S_base. apply BS_eq_false. omega. }
    etransitivity_1n.
    { apply S_base. apply BS_if_false. }
    reflexivity.
  - intros. inversion H;subst.
    apply (ill_typed_example _ _ H3).
Qed.

End Task2.

(* Fri May 29 22:59:47 CST 2020 *)
