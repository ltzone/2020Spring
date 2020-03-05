
(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/03/05.                                             *)
(* Due: 2020/03/09, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment1.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment1.vo" file is generated.         *)
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

Require Import PL.Imp.

(** The command [Admitted] can be used as a placeholder for an
    incomplete proof or an in complete definition.  We'll use it in
    exercises, to indicate the parts that we're leaving for you --
    i.e., your job is to replace [Admitted]s with real proofs and/or
    definitions. *)

(* ################################################################# *)
(** * Task 1 *)

(** Equalities are symmetric and transive. Prove it in Coq. You should
fill in your proof scripts and replace "Admitted" with "Qed".  *)

(** **** Exercise: 1 star, standard  *)
Theorem eq_sym: forall (A: Type) (x y: A), x = y -> y = x.
Proof.
  intros.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Theorem eq_trans: forall (A: Type) (x y z: A), x = y -> y = z -> x = z.
Proof.
  intros.
(* FILL IN HERE *) Admitted.
(** [] *)

(** The following example is an special instance of congruence properties.
That is, equalities between integers are preserved by addition. *)

(** **** Exercise: 1 star, standard  *)
Theorem Zplus_add: forall x1 x2 y1 y2: Z,
  x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2.
Proof.
  intros.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Task 2 *)

(** Read the following pairs of English descriptions and Hoare triples.
Determine whether they express equivalent meaning. *)

Module Task2_Example.

(**
Hoare triple: {{ True }} c {{ {[X]} <= 3 AND 3 <= {[X]} }}.
Informal description: the program [c] will turn the value of [X] into [3].
Do they express equivalent meaning? 1: Yes. 2: No.
*)

Definition my_choice: Z := 1.

End Task2_Example.

(** **** Exercise: 1 star, standard  *)
Module Task2_1.

(**
Hoare triple: {{ {[X]} <= {[Y]} }} c {{ {[Y]} <= {[X]} }}.
Informal description: the program [c] will swap the values of [X] and [Y].
Do they express equivalent meaning? 1: Yes. 2: No.

Remove "[Admitted.]" and write down your choice.
*)

Definition my_choice: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

End Task2_1.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_2.

(**
Hoare triple: {{ EXISTS k. {[X]} = 2 * k }} c {{ {[Y]} = 0 }}.
Informal description: the program [c] will test whether [X] is an even
number (偶数); if yes, [0] will be assigned into [Y].
Do they express equivalent meaning? 1: Yes. 2: No.
*)

Definition my_choice: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

End Task2_2.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_3.

(**
Hoare triple: {{ True }} c {{ False }}.
Informal description: the program [c] will never terminate.
Do they express equivalent meaning? 1: Yes. 2: No.
*)

Definition my_choice: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

End Task2_3.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_4.

(**
Hoare triple: {{ True }} c {{ True }}.
Informal description: any program [c].
Do they express equivalent meaning? 1: Yes. 2: No.
*)

Definition my_choice: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

End Task2_4.
(** [] *)

(** **** Exercise: 1 star, standard  *)
Module Task2_5.

(**
Hoare triple: for any m, {{ {[X]} + {[Y]} = m }} c {{ {[X]} + {[Y]} = m }}.
Informal description: the program [c] will not change the sum of [X] and [Y].
Do they express equivalent meaning? 1: Yes. 2: No.
*)

Definition my_choice: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

End Task2_5.
(** [] *)

(* ################################################################# *)
(** * Task 3 *)

(** **** Exercise: 3 stars, standard (swapping_by_arith)  *)

Module swapping_by_arith.
Import Concrete_Pretty_Printing.
Import Axiomatic_semantics.

(** Prove the following swapping programs correct. Hoare triples about single
assignment commands are provided as hypothese.

       X ::= X + Y;;
       Y ::= X - Y;;
       X ::= X - Y
*)

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

(** Here are three hypothese. *)

Hypothesis triple1: forall x y: Z,
  {{ {[X]} = x AND {[Y]} = y }}
  X ::= X + Y
  {{ {[X]} = x + y AND {[Y]} = y }}.

Hypothesis triple2: forall x y: Z,
  {{ {[X]} = x + y AND {[Y]} = y }}
  Y ::= X - Y
  {{ {[X]} = x + y AND {[Y]} = x }}.

Hypothesis triple3: forall x y: Z,
  {{ {[X]} = x + y AND {[Y]} = x }}
  X ::= X - Y
  {{ {[X]} = y AND {[Y]} = x }}.

(** Now, prove the following Hoare triple by Hoare logic axioms. *)

Fact swapping_by_arith_correct:
  forall x y: Z,
       {{ {[X]} = x AND {[Y]} = y }}
       X ::= X + Y;;
       Y ::= X - Y;;
       X ::= X - Y
       {{ {[X]} = y AND {[Y]} = x }}.
Proof.
  intros.
(* FILL IN HERE *) Admitted.
(** [] *)
End swapping_by_arith.

(* ################################################################# *)
(** * Task 4: Using [apply] in more Coq proofs *)

(** A binary relation [R] is called a pre-order if it is reflexive and
transitive. Here is a very simple property about pre-orders. Try to prove
it in Coq. *)

Section PreOrder.

Variable A: Type.
Variable R: A -> A -> Prop.
Hypothesis R_refl: forall a, R a a.
Hypothesis R_trans: forall a b c, R a b -> R b c -> R a c.

(** **** Exercise: 1 star, standard  *)
Fact R_trans5: forall a b c d e, R a b -> R b c -> R c d -> R d e -> R a e.
Proof.
  intros.
(* FILL IN HERE *) Admitted.
(** [] *)

End PreOrder.



(* Thu Mar 5 01:20:37 CST 2020 *)
