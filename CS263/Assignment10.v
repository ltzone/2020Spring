(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/06/08.                                             *)
(* Due: 2020/06/12, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment10.v) on CANVAS.        *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment10.vo" file is generated.        *)
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
Require Import PL.Lambda2.

(* ################################################################# *)
(** * Task 1: Progress And Preservation *)

Module Task1.

Import LambdaIB.
Local Open Scope Z.
Local Open Scope string.

(** In this task, you need to answer some basic questions about lambda
    expressions with integers and booleans involved (references are not
    involved). We have seen the definition of [do_it_three_times] and
    [add_one] in class. *)

Definition do_it_three_times: tm :=
  abs "f" (abs "x" (app "f" (app "f" (app "f" "x")))).

Definition add_one: tm :=
  abs "x" (app (app Oplus "x") 1).

(** Please prove that the following expression is well-typed. Hint: you may use
    [type_of_add_one] and [type_of_do_it_three_times] in this proof. *)

(* type_of_add_one: empty_context |- add_one \in (TInt ~> TInt) *)

(* type_of_do_it_three_times: forall T,
  empty_context |- do_it_three_times \in ((T ~> T) ~> (T ~> T)) *)

(** **** Exercise: 2 stars, standard (power_3_3_well_typed)  *)
Lemma power_3_3_well_typed:
  empty_context |- app (app do_it_three_times do_it_three_times) add_one \in
    (TInt ~> TInt).
Proof.
  eapply T_app.
  2: { apply type_of_add_one. }
  eapply T_app.
  apply type_of_do_it_three_times.
  apply type_of_do_it_three_times.
Qed.
(** [] *)

(** Obviously, we can take at least one step to in the process of evaluating
    this expression above. In other words, the following statement is true: *)

Definition step_statement: Prop :=
  exists step_result: tm,
    step (app (app do_it_three_times do_it_three_times) add_one) step_result.

(** On one hand, we can prove this statement above by providing a [step_result]
    explicitly and prove the step relation. What is that step result? *)

(** **** Exercise: 1 star, standard (step_result)  *)
Definition step_result: tm
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** On the other hand, we know that step result must exists since lambda
    expression evaluation is type safe. Which type safety property proves this
    existences lemma?

    1. Progress. 2. Preservation. *)

(** **** Exercise: 1 star, standard  *)
Definition my_choice1: Z := 1.
(** [] *)

(** Moreover, from type safety, we know that the [step_result] is also well
    typed. In other words, *)

Definition step_result_type_statement: Prop :=
  empty_context |- step_result \in (TInt ~> TInt).

(** Which type safety property proves this claim?

    1. Progress. 2. Preservation. *)

(** **** Exercise: 1 star, standard  *)
Definition my_choice2: Z := 2.
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2: Let In Lambda Expressions *)

Module Task2.
Import LambdaIBR.
Local Open Scope Z.
Local Open Scope string.

(** We have seen how to encode "let" expression using normal lambda expressions.
    Please describe the evaluation result of the following lambda expressions.
*)

Module Task2_Example.

Definition expression: tm := \let "x" \be (app Onot true) \in "x".
  
Definition eval_result: tm := false.

(** Remember, when we write [false] here, it actually means

    - [con (bool_const (false))].

*)

End Task2_Example.

(** **** Exercise: 1 star, standard  *)

Module Task2_1.

Definition expression: tm :=
  \let "x" \be 1 \in
  \let "y" \be ("x" + 1)%tm \in
  \let "x" \be ("y" + 1)%tm \in
  "x".
  
Definition eval_result: tm := 3.
(** [] *)

End Task2_1.

(** **** Exercise: 1 star, standard  *)

Module Task2_2.

Definition expression: tm :=
  \let "x" \be app (abs "x" "x") 1 \in
  "x".
  
Definition eval_result: tm := 1.
(** [] *)

End Task2_2.

(** **** Exercise: 1 star, standard  *)

Module Task2_3.

Definition expression: tm :=
  \let "F" \be
     (abs "f" (abs "x"
        (\let "x" \be app "f" "x" \in
         \let "x" \be app "f" "x" \in
         \let "x" \be app "f" "x" \in
         "x"))) \in
  app (app (app "F" "F") (abs "x" ("x" + 1)%tm)) 0.
  
Definition eval_result: tm := 27.
(** [] *)

End Task2_3.

(** **** Exercise: 1 star, standard  *)

Module Task2_4.

Definition expression: tm :=
  \let "swap_arg" \be
     (abs "f" (abs "x" (abs "y" (app (app "f" "y") "x")))) \in
  app "swap_arg" (abs "x" (abs "y" ("x" - "y")%tm)).
  
Definition eval_result: tm :=
  abs "x" (abs "y" (
     app (app (abs "x" (abs "y" ("x" - "y")%tm)) "y") "x")).
  
(** [] *)

End Task2_4.

End Task2.

(* ################################################################# *)
(** * Lambda Expressions With References *)

Module Task3.

Import LambdaIBR.
Local Open Scope Z.
Local Open Scope string.

(** Please describe the evaluation results. *)

(** **** Exercise: 2 stars, standard  *)

Module Task3_1.

Definition expression: tm :=
  \let "get_and_add" \be
    (abs "p"
      (\let "x" \be (app Oread "p") \in
       \let "y" \be ("x" + 1)%tm \in      
       \let "_" \be (app (app Owrite "p") "y") \in
       "x")) \in
  \let "p" \be app Oalloc 0 \in
  \let "x" \be app "get_and_add" "p" \in
  \let "x" \be app "get_and_add" "p" \in
  \let "x" \be app "get_and_add" "p" \in
  "x".


Definition eval_result: tm := 2.
(** [] *)

End Task3_1.

(** **** Exercise: 2 stars, standard  *)

Module Task3_2.

Definition expression: tm :=
  \let "func_add_one" \be
     (abs "f" (abs "x" ((app "f" "x") + 1)%tm)) \in
  \let "f" \be (abs "x" "x") \in
  \let "p" \be (app Oalloc "f") \in
  \let "f" \be (app "func_add_one" (app Oread "p")) \in
  \let "p" \be (app Oalloc "f") \in
  \let "f" \be (app "func_add_one" (app Oread "p")) \in
  app "f" 0.


Definition eval_result: tm := 2.

(** [] *)

End Task3_2.

End Task3.

(* Mon Jun 8 22:00:04 CST 2020 *)
