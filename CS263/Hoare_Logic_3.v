(** Remark. Some material in this lecture is from << Software Foundation >>
volume 2. *)

Require Import PL.Imp.

Import Assertion_S.
Import Concrete_Pretty_Printing.

(** In the last lecture, we have learned how to prove a program correct by Hoare
logic and how to use [apply] in Coq to formalize those proofs. We have shown
the following swapping program's proof in Coq. *)

Module Axiomatic_semantics_demonstration.

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

End Axiomatic_semantics_demonstration.

(** Till now, we have learnt how to formalize some Hoare logic proofs in Coq.
But you might have noticed two tiny problems. 1. We have proved nothing for
assignment commands. We only assume that some Hoare triples about assignment
commands are true. Coq forces us to distinguish which parts really get proved
and which parts are actually hypotheses. 2. Our postconditions look not nice.
For example, in [div_mod_correct] we have to write

    {{ n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND NOT {[n <= X]} }}

instead of

    {{ n * {[Y]} + {[X]} = m AND 0 <= {[X]} AND {[X]} < n }}.

Coq forces us to strictly follow axioms' statements. But we really hope that we
can at least replace an assertion with an equivalent one. *)

(** We introduce several more axioms in response to this concern. *)

(* ################################################################# *)
(** * Assignment rule (forward) *)




(** We clearly see a common pattern when we try to write postconditions for
assignment commands with form [X ::= E]. Each of these postconditions has two
parts (1) the original value of [X] satisfies the precondition; (2) the current
value of [X] can be calculated by [E] using the original value of [X]. The
original value of [X] plays a very important role here! But, we cannot always
refer to the original value directly. Here is an example: *)

(** What is the best postcondition for the following command?

       {{ n * {[Y]} + {[X]} + n = m AND 0 <= {[X]} AND {[X]} < n }}
       Y ::= 0
       {{ ??? }}
*)

(** The best postcondition is:

       {{ EXISTS y, n * y + {[X]} + n = m AND
          0 <= {[X]} AND {[X]} < n AND {[Y]} = 0 }}

This example gives us a hint---we do not need to refer to the old value
directly; we can talk about it using the existential quantifier. In general,
given a precondition [P], a program variable [X] and a program expression [E],
we can write the following postcondition informally:

       There exists an old value x of program variable
       X, such that (1) the precondition P would hold if
       the value of X would be x (2) the value of X is
       result of evaluating the expression E if treating
       all occurrences of X in E as x.
*)

(* ================================================================= *)
(** ** Symbolic substitution in program expressions *)

(** Suppose [E] is an integer-type expression of the programming language,

    E [X |-> E0]

represents the result of replacing every occurence of program variable [X] with
program expression [E0] in [E]. This result is still an integer-type
expression. *)



(** We can also apply symbolic substitution on a boolean expression.
Specifically, for a boolean-type expression [B] and an integer-type expression
 [E0], we use

    B [X |-> E0]

to represent the result of replacing every occurence of program variable [X]
with [E0] in [B], e.g.

    (!(X <= Y))[X |-> 0]

is [ ! (0 <= Y) ].
*)

(* ================================================================= *)
(** ** Symbolic substitution in assertions *)

(** We can also define symbolic substitution in assertions. We use

    P [X |-> E0]

to represent the result of replacing every occurence of program variable [X]
with program expression [E0] in assertion [P]. For example,

        ({[X + Y <= Z]} AND 0 <= {[X]} + {[Y]}) [X |-> x]
        ({[X + Y <= Z]} AND 0 <= {[X]} + {[Y]}) [X |-> 0]

are

        {[x + Y <= Z]} AND 0 <= {[x]} + {[Y]}.
        {[0 + Y <= Z]} AND 0 <= {[0]} + {[Y]}.

In other words, the effect of symbolic substitution on an assertion [P] is
applying object language substitution on those program expressions mentioned in
[P]. *)

(* ================================================================= *)
(** ** Proof rule *)

(** The following axiom describes the behavior of assignment commands. *)

Axiom hoare_asgn_fwd : forall P `(X: var) E,
  {{ P }}
  X ::= E
  {{ EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} }}.




(* ################################################################# *)
(** * Assignment rule (backward) *)

(** When C. A. R. Hoare first proposed Hoare logic for program correctness
proof in 1960s, the assignment rule is not in the forward direction; it was in
the backward direction. Robert W. Floyd proposed forward assignment rule later.
Due to this reason, people also use the nomenclature "Floyd-Hoare" logic
sometimes. (Another reason is that the original ideas of Hoare logic were seeded
by Floyd's work of a similar system for flowcharts.) *)

Axiom hoare_asgn_bwd : forall P `(X: var) E,
  {{ P [ X |-> E] }} X ::= E {{ P }}.

(* ################################################################# *)
(** * Consequence rule *)

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.

(* ################################################################# *)
(** * Summary: axiomatic semantics *)

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

Axiom hoare_asgn_fwd : forall P `(X: var) E,
  {{ P }}
  X ::= E
  {{ EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} }}.

Axiom hoare_asgn_bwd : forall P `(X: var) E,
  {{ P [ X |-> E] }} X ::= E {{ P }}.

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.

End Axiomatic_semantics.



(* Mon Mar 9 21:59:58 CST 2020 *)
