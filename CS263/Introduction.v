(** * What is this course about? *)

(** This course, Programming Languages, is about the theory for the following
questions: is this program correct? why is it correct? why is it not correct? *)

(* ================================================================= *)
(** ** Sample program 1. *)

(**

struct list {unsigned int head; struct list *tail;};

unsigned int sumlist (struct list * t) {
  unsigned int s = 0;
  struct list * u;
  if (t == NULL)
     return 0;
  u = t -> tail;
  while (t) {
     s = s + (t->head);
     t = u;
     u = t->tail;
  }
  return s;
}

Is this program correct? Suppose t is guaranteed to be a linked list's head
pointer.*)

(* ================================================================= *)
(** ** Sample program 2. *)

(** 

int binary_search (int L, int R) {
  int m;
  while (L < R) {
    m = (L + R) / 2;
    if (test(m))
    {
      L = m;
    }
    else
    {
      R = m;
    }
  }
  return L;
}

Is this program correct? *)

(* ================================================================= *)
(** ** Sample program 2'. *)

(**

\\ test(m) is true when m is too small
\\ test(m) is false when m is OK or too large

int binary_search (int L, int R) {
  int m;
  while (L < R) {
    m = (L + R) / 2;
    if (test(m))
    {
      L = m + 1;
    }
    else
    {
      R = m;
    }
  }
  return L;
}

Is this program correct? *)

(* ================================================================= *)
(** ** Sample program 3. *)

(**

void swap_int (int * L, int * R) {
  * L = ( * L ) + ( * R );
  * R = ( * L ) - ( * R );
  * L = ( * L ) - ( * R );
}

Is this program correct? Suppose L and R are different addresses. *)

(** Yes and no again? *)

(** It is more tricky! On almost all reasonable compilers, this program will
never go wrong, even if arithmetic overflow appears. But it is not guaranteed.
Here is what C standard says (C11 6.5.5): *)

(**

                    If an exceptional condition occurs during the
                    evaluation of an expression (that is, if the
                    result is not mathematically defined or not
                    in the range of representable values for its
                    type), the behavior is undefined.
*)

(** Now we all agree, being correct is a nontrivial concept. Whether a program
is correct does not only depend on what a program will do (determined by source
program and compiler) but also depends what is a program expected to do. *)

(* ================================================================= *)
(** ** Terminology *)

(** Program specification (程序规约）: the designed functionality of a program. *)

(** Program semantics (程序语义）: a description of programs' behavior. *)

(* ################################################################# *)
(** * How will this course be taught? *)

(** The lectures will be Chinese but all course material will be in English.
Terminologies will be taught in both Chinese and English. *)

(* ################################################################# *)
(** * Course material *)

(** All lecture notes will be online. They will be presented both in Coq and in
html. Coq is a language for writing formal math definitions and proofs. You need
to do homework in Coq too. *)

(** Coq download: https://github.com/coq/coq/releases/tag/V8.11.0 *)

(** For Coq usage (additional): Software Foundation Volume 1,
 https://softwarefoundations.cis.upenn.edu/lf-current/toc.html *)

(** For course text book (additional): Software Foundation Volume 2,
 https://softwarefoundations.cis.upenn.edu/plf-current/toc.html *)

(* ################################################################# *)
(** * Course grade *)

(** 10 attendence + 50 homework (10 assignments) + 40 final project *)

(** 7-late-day policy: everyone has 7 late days for homework through the whole
semester. Any other late submissions are NOT allowed. Late days cannot be used
on final project. *)

(** Discussion is allowed but should be documented. Copy & paste is NOT allowed.
*)

(** Homework should be submitted on CANVAS. *)

(* ################################################################# *)
(** * Office hour *)

(** Time: Tuesday 16:00 - 17:00. *)

(** Location: online. *)

(* ################################################################# *)
(** * One more thing: a Coq demo *)

Require Import Setoid.

(** Coq is a proof management tool---it is designed to help researchers write
math definitions and strict math proofs. For example, the following theorem
might be the first proof that students will learn in an abstract algebra course.

First, a group contains an underlying set A with a unit element, a binary
operator (addition) and a unary operator (negation). They are usually rewriten
as (A, 0, +, -). *)

Section Group.

Variable A: Type.
Variable z: A.
Variable add: A -> A -> A.
Variable neg: A -> A.
Notation "x + y" := (add x y).
Notation "- x" := (neg x).
Notation "0" := z.

(** Such quadruple is called a group if it satisfies associativity, the left
unit property and the left inversion property. *)

Hypothesis assoc: forall (x y z: A), (x + y) + z = x + (y + z).
Hypothesis left_unit: forall (x: A), 0 + x = x.
Hypothesis left_inv: forall (x: A), (- x) + x = 0.

(** Then we prove that such a group must have the right inversion property and
the right unit property. *)

(** Keywords "Theorem", "Lemma" and "Corollary" indicates the beginning of a
theorem statement. Users should write proof scripts inside a "Proof-Qed" block.
*)

Theorem right_inv: forall (x: A), x + (- x) = 0.
Proof.

(** In the proof mode, you can always see a proof goal (or proof goals) on the
right side windows of your IDE. For example, you can see a proof goal now. *)

(** Every tactic will reduce a proof goal into zero, one, or more proof goals.
For example, a Coq proof script usually starts with "intros". *)
  
  intros.

(** Then "rewrite" can be used to turn an expression into an equivalent one. *)

  rewrite <- left_unit with (x := (x + - x)).
  rewrite <- (left_inv (-x)).
  rewrite -> assoc.
  rewrite <- assoc with (x := -x).
  rewrite left_inv.
  rewrite left_unit.
  rewrite left_inv.

(** In the end, we use "reflexivity" to complete the proof since equlity is
reflexive. *)

  reflexivity.
Qed.

(** Here is another proof. *)

Theorem right_unit: forall (x: A), x + 0 = x.
Proof.
  intros.
  rewrite <- left_inv with (x := x).
  rewrite <- assoc.

(** We can not only use hypothesis but also proved theorems when proving new
theorems. We just proved [right_inv]; now we use it. *)

  rewrite right_inv.
  rewrite left_unit.
  reflexivity.
Qed.

Theorem neg_involutive: forall (x:A), x = - - x.
Proof.
  intros.
  rewrite <- (left_unit x) at 1.
  rewrite <- (left_inv (-x)).
  rewrite assoc.
  rewrite left_inv.
  rewrite right_unit.
  reflexivity.
Qed.

End Group.

(* Tue Feb 25 11:01:13 CST 2020 *)
