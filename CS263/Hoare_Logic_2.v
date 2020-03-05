(** Remark. Some material in this lecture is from << Software Foundation >>
volume 2. *)

(** Like our last lecture, we need to import [Imp] first. *)

Require Import PL.Imp.

Import Assertion_S.
Import Concrete_Pretty_Printing.



(* ################################################################# *)
(** * Axiomatic semantics for loops *)

(** Axiomatic semantics of loops: *)

Axiom hoare_while : forall P b c,
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

(** Here, the assertion [P] is called a _loop invariant_ (循环不变量). *)

(* ================================================================= *)
(** ** Example: Reduce to Zero *)

(** This program will terminate until [X] is zero.

        {{ True }}
        While !(X == 0) Do
          X ::= X - 1
        EndWhile
        {{ {[ X ]} = 0 }}

Using [True] as loop invariant! *)

(* ================================================================= *)
(** ** Example: Division *)

(** For fixed positive integer [m] and [n], the following program calculates the
integer quotient and remainder. 

       {{ 0 <= m AND 0 < n }}
       X ::= m;;
       Y ::= 0;;
       While n <= X Do
         X ::= X - n;;
         Y ::= Y + 1
       EndWhile
       {{ n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n }}.
*)

(** Loop invariant:

       n * {[Y]} + {[X]} = m AND 0 <= {[X]}.
*)

(* ================================================================= *)
(** ** How to find a good loop invariant? *)

(** The most critical steps in our examples above is to find a good loop
invariant. Is there a generic method of doing that? *)

(** (1) A loop invariant should not be too strong. The program states before and
after every single loop body's iteration should satisfy the invariant. *)

(** (2) A loop invariant [P] should not be too weak to derive meaningful
conclusion from the conjunction [ P AND NOT {[b]} ]. *)

(* ================================================================= *)
(** ** Example: Remainder Only *)

(** The following program calculates the remainder only. 

       {{ 0 <= m }}
       X ::= m;;
       While n <= X Do
         X ::= X - n
       EndWhile
       {{ (EXISTS q, n * q + {[X]} = m) AND 0 <= {[X]} AND {[X]} < n }}.

Our loop loop invariant is:

       (EXISTS q, n * q + {[X]} = m) AND 0 <= {[X]}
*)




(* ################################################################# *)
(** * Summary of axiomatic semantics *)

(** So far, we've introduced four axioms for four program constructor. They are: *)

Module Axiomatic_semantics.

Axiom hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1;;c2 {{R}}.

Axiom hoare_skip : forall P,
  {{P}} Skip {{P}}.

Axiom hoare_if : forall P Q b c1 c2,
  {{ P AND {[b]} }} c1 {{ Q }} ->
  {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.

Axiom hoare_while : forall P b c,
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

End Axiomatic_semantics.

(** Because we use these axioms about Hoare triples to define program semantics,
such definition is called an _axiomatic semantics_ (公理化语义). We also say that
these axioms form a _proof system_ (推理系统), or a _Hoare logic_ (霍尔逻辑). *)

(* ################################################################# *)
(** * Program correctness proof in Coq *)

(** Before we go through further examples, I wanna remind you that you may
choose your editor preference in menu (Edit => Preferences => Editor). In those
choices, "auto indentation" (自动缩进) and "auto completion" (自动填充) are
very useful. *)

(** If you prefer a monospaced font, just choose "monospace". If you prefer to
read those Chinese charecters inside comments, you can choose something like
"YouYuan" or "KaiTi" *)

(* ================================================================= *)
(** ** Example: Swapping *)

Module swapping.
Import Axiomatic_semantics.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().
Local Instance TEMP: var := new_var().

(** We are going to prove: 

       {{ {[X]} = x AND {[Y]} = y }}
       TEMP ::= X;;
       X ::= Y;;
       Y ::= TEMP
       {{ {[X]} = y AND {[Y]} = x }}.

This is based on 3 Hoare triples about assignment commands. In fact, we have not
proved them yet in any precise way. They are just true by own intuition. Thus we
wrote them down as hypothesis here. *)

Hypothesis triple1: forall x y: Z,
       {{ {[X]} = x AND {[Y]} = y }}
       TEMP ::= X
       {{ {[Y]} = y AND {[TEMP]} = x }}.

Hypothesis triple2: forall x y: Z,
       {{ {[Y]} = y AND {[TEMP]} = x }}
       X ::= Y
       {{ {[X]} = y AND {[TEMP]} = x }}.

Hypothesis triple3: forall x y: Z,
       {{ {[X]} = y AND {[TEMP]} = x }}
       Y ::= TEMP
       {{ {[X]} = y AND {[Y]} = x }}.

(** Then we start our theorem proving. Usually, a theorem statement starts with
"Theorem", "Lemma", "Corollary", "Fact" or "Example". *)

Fact swaping_correct:
  forall x y: Z,
       {{ {[X]} = x AND {[Y]} = y }}
       TEMP ::= X;;
       X ::= Y;;
       Y ::= TEMP
       {{ {[X]} = y AND {[Y]} = x }}.
Proof.
  intros.
(** We have seen this command "intros" in our introduction to this course. It
will move universally quantified variables in the conclusion into assumptions.
*)  
  apply hoare_seq with ({[Y]} = y AND {[TEMP]} = x)%assert.
(** This tactic says: we choose to use [hoare_seq] to prove our conclusion. The
"with" clause indicates the middle condition. We use [%assert] to let CoqIDE
know that this argument is an assertion. 

    This tactic reduces the original proof goal into two smaller ones---one is a
Hoare triple for the first command and the other is a Hoare triple for the last
two assignment commands. They corresponds to two assumptions of [hoare_seq]
respectively. This is reasonable---in order to prove something using
[hoare_seq], one have to prove its assumptions first. *)
  apply triple1.
(** The first proof goal is our first hypothesis. *)
  apply hoare_seq with ({[X]} = y AND {[TEMP]} = x)%assert.
(** The second proof goal needs [hoare_seq] again. *)
  apply triple2.
  apply triple3.
(** In the end, we write "Qed" to complete our proof. *)
Qed.

(** If you go through this proof above, you may feel that it is in a backward
direction---we reduced our proof goal step by step and achieve our assuptions
in the end. In fact, you can also write forward proofs in Coq. *)

Fact swaping_correct_again:
  forall x y: Z,
       {{ {[X]} = x AND {[Y]} = y }}
       TEMP ::= X;;
       X ::= Y;;
       Y ::= TEMP
       {{ {[X]} = y AND {[Y]} = x }}.
Proof.
  intros.
  pose proof triple1 x y.
  pose proof triple2 x y.
  pose proof triple3 x y.
  pose proof hoare_seq
               ({[Y]} = y AND {[TEMP]} = x)
               ({[X]} = y AND {[TEMP]} = x)
               ({[X]} = y AND {[Y]} = x)
               (X ::= Y)
               (Y ::= TEMP)
               H0
               H1.
  (** When you are able to derive a new conclusion from assumptions, the
  "pose proof" tactic can be used to put that conclusion above the line. *)
  clear H0 H1.
  (** At this point, if you feel that some assumptions are redundant above the
  line, you can use clear to remove them. *)
  pose proof hoare_seq _ ({[Y]} = y AND {[TEMP]} = x) _ _ _ H H2.
  (** You do not need to type all arguments manually. Use underscore [_] if Coq
  can infer that. *)
  exact H0.
  (** In the end, what we want to prove is already proved. We use "exact". *)
Qed.

End swapping.

(* Thu Mar 5 01:20:37 CST 2020 *)
