(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/04/24.                                             *)
(* Due: 2019/04/27, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment6.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment6.vo" file is generated.         *)
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

Require Import PL.Imp3.
Require Import Coq.Lists.List.
Import ListNotations.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(* ################################################################# *)
(** * Task 1: Understanding Syntax Trees *)

Module Task1.

(** **** Exercise: 1 star, standard  *)

(** Is the following claim correct?

    If [X], [Y] and [Z] are distinct program variables and [x] is a logical
    variable, then the subtitution result of
      [   ({[ X + Y ]} = {[Z]} + x) [X |-> x]   ]
    is
      [   {[ x + Y ]} = {[Z]} + x   ].

    1: Yes. 2: No. *)

Definition my_choice1: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following claim correct?

    If [X] and [Y] are distinct program variables, [E1] and [E2] are integer
    expressions, [P] is an assertion, then 
      [   P [X |-> E1] [Y |-> E2]   ]
    and
      [   P [Y |-> E2] [X |-> E1]   ]
    are always equivalent assertions.

    1: Yes. 2: No. *)

Definition my_choice2: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following claim correct?

    If [X] is a program variables, [E1] and [E2] are integer expressions, [P] is
    an assertion, then 
      [   P [X |-> E1] [X |-> E2]   ]
    and
      [   P [X |-> E1]   ]
    are always equivalent assertions.

    1: Yes. 2: No. *)

Definition my_choice3: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following claim correct?

    If [X] is a program variables, [x] is a logical variable, [P] is an
    assertion, then [P] is a stronger assertion than
      [   EXISTS x, P [X |-> x]   ].

    1: Yes. 2: No. *)


Definition my_choice4: Z := 1.
(** [] *)

End Task1.

(** Task 2: Understand Validity and Provability *)

Module Task2.

(** **** Exercise: 1 star, standard  *)

(** Is the following reasoning about "valid" correct?

    BECAUSE the subtitution result of
    [    ({[X]} = m AND {[Y]} = n) [Y |-> Y - X]    ]
    is
    [    {[X]} = m AND {[Y - X]} = n    ],
    the following Hoare triple is VALID:
    [
          {{ {[X]} = m AND {[Y - X]} = n }}
             Y ::= Y - X
          {{ {[X]} = m AND {[Y]} = n }}.
    ]

    1: Yes. 2: No. *)

Definition my_choice1: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following reasoning about "valid" correct?

    The following Hoare triple is VALID:
    [
          {{ True }}
             While X <= X Do X ::= X + 1 EndWhile
          {{ False }}.
    ]
    BECAUSE the loop will never terminate according to the denotational
    semantics [ceval].

    1: Yes. 2: No. *)

Definition my_choice2: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following claim about "provable" correct?

    If [ {{ P }} (c1 ;; c2);; c3 {{ Q }} ] is provable, then
    [ {{ P }} c1 ;; (c2 ;; c3) {{ Q }} ] is also provable.

    1: Yes. 2: No. *)

Definition my_choice3: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following reasoning about "provable" correct?

    BECAUSE the ending state of [Skip] is always the same as its beginning
    state (according to the definition of [ceval]), this following Hoare triple
    is always PROVABLE:
        [    {{ P }} Skip {{ P }}.   ]

    1: Yes. 2: No. *)

Definition my_choice4: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following reasoning about "valid" correct?

    Using [hoare_seq] and [hoare_asgn_bwd], we can build a Hoare logic proof for
    the following Hoare triple:
    [
          {{ {[(X + Y) - X]} = m AND {[(X + Y) - (X + Y - X)]} = n }}
             Y ::= X + Y;;
             X ::= Y - X;;
             Y ::= Y - X
          {{ {[X]} = m AND {[Y]} = n }}.
    ]
    IF our Hoare logic is complete, THEN this Hoare triple is also valid.

    1: Yes. 2: No. *)

(* IF Hoare Logic has soundness ... *)

Definition my_choice5: Z := 2.
(** [] *)

End Task2.

(* ################################################################# *)
(** * Task 3: Alternative Primary Proof Rules *)

Module Task3.

(** Consider the following proof rule for if-commands:

    - If [  {{ P }} c1 {{ Q }}  ] and [  {{ P }} c2 {{ Q }}  ], then
      [  {{ P }} If b Then c1 Else c2 EndIf {{ Q }}  ].

    We may add it to our proof system. If doing that, the logic is still sound.
    Your task is to show why. Hint: remember that [ceval_CIf] describes the
    denotational semantics of if-commands. *)

(** **** Exercise: 1 star, standard (new_if_rule_sound)  *)

Lemma new_if_rule_sound: forall P b c1 c2 Q,
  |== {{ P }} c1 {{ Q }} ->
  |== {{ P }} c2 {{ Q }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.
Proof.
  intros.
  hnf in *.
  rewrite ceval_CIf.
  intros.
  destruct H2;destruct H2 as [st' [[H2 H3] H4]].
  + rewrite <- H2 in *. apply (H _ st1);auto.
  + rewrite <- H2 in *. apply (H0 _ st1);auto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** If replacing our original proof rule for if-commands [hoare_if] with this
    new proof rule in the proof system, is the logic still complete?

    1: Yes. 2: No. *)


Definition my_choice1: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Consider the following proof rule for assignment commands:

    - If [X] is a program variable that does not appear in [E], then
      [  {{ P }} X ::= E {{ P [X |-> E] }}  ].

    Is the Hoare logic still sound if this additional rule is added to the proof
    system? (Suppose the underlying logic for assertion derivation is sound.)

    1: Yes. 2: No. *)

Definition my_choice3: Z := 2.
(** [] *)

End Task3.

(* ################################################################# *)
(** * Task 4: Underlying Weakest Preconditions *)

Module Task4.

(** **** Exercise: 2 stars, standard  *)

(** Which of the following statements about weakest preconditions are correct?

    - 1. For any assertion [P], program variable [X] and integer expression [E],
      [ P [X |-> E] ] is a weakest precondition of [X ::= E] and [P].

    - 2. For any assertion [P], logical variable [x], program variable [X] and
      integer expression [E], if [x] does not freely occur in [P], then [ P ] is
      a weakest precondition of [X ::= E] and
          [    EXISTS x, P [X |-> x] AND {[ X ]} = {[ E [X |-> x] ]}    ].
    
    - 3. If [P] is a weakest precondition of [c] and [Q], and [P] is equivalent
      to [P'], then [P'] is also a weakest precondition of [c] and [Q]. (Here,
      we say that [P] and [P'] are equivalent when: for any interpretation [J],
      [J |== P] if and only if [J |== P'].)

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_choice1: list Z := [2;3].
(** [] *)

(** **** Exercise: 2 stars, standard  *)

(** Which of the following statements about weakest preconditions are correct?

    - 1. [True] is a weakest precondition of [While (X <= X) Do Skip EndWhile]
      and [False].

    - 2. [False] is a weakest precondition of [While (X <= X) Do Skip EndWhile]
      and [False].
    
    - 3. For any assertions [P], [Q], any boolean expression [b] and any loop
      body [c], if [P] is a weakest precondition of [While b Do c EndWhile] and
      [Q], and [P] is also a weakest precondition of [While b Do c EndWhile] and
      [ P AND NOT {[ b ]} ].

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_choice2: list Z := [2;3].
(** [] *)

End Task4.

(* Fri Apr 24 16:47:32 CST 2020 *)
