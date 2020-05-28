Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.

Definition var: Type := nat.

Definition state: Type := var -> Z.

Open Scope Z.

(* ################################################################# *)
(** * Run Time Error in Expression Evaluation *)

(** In this lecture, we discuss semantic definitions for programming languages
with potential run time error and nondeterminism. The following definition of
[aexp] adds one more operator to our previous choices: division. *)

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <-- New *)

(** Originally, an [aexp] expression's denotation has type [state -> Z]. Now,
we cannot do that any longer, the evaluation result may be undefined at some
point -- if the divisor is zero.

One potential solution is to use Coq's option type. *)

Print option.
(* Inductive option (A : Type) : Type :=
    Some : A -> option A | None : option A *)

(** We can use [Some] cases of [option] types to represent "defined" and use
[None] cases of [option] types to represent "undefined". *)

Module OptF.

Definition add {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 => Some (v1 + v2)
    | _, _ => None
    end.

Definition sub {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 => Some (v1 - v2)
    | _, _ => None
    end.

Definition mul {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 => Some (v1 * v2)
    | _, _ => None
    end.

(** When defining the semantics of [ADiv], we can state that the result is
defined only when the evaluation result of both sides are defined and the
divisor does not evaluate to zero. *)

Definition div {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 =>
        if Z.eq_dec v2 0
        then None
        else Some (v1 / v2)
    | _, _ => None
    end.

(** Here, [Z.eq_dec] determines whether two integers are equivalent or not. *)

Check Z.eq_dec.

(* Z.eq_dec
     : forall x y : Z, {x = y} + {x <> y} *)

End OptF.

Module Option_Denote_Aexp.

Fixpoint aeval (a : aexp): state -> option Z :=
  match a with
  | ANum n => fun _ => Some n
  | AId X => fun st => Some (st X)
  | APlus a1 a2 => OptF.add (aeval a1) (aeval a2)
  | AMinus a1 a2  => OptF.sub (aeval a1) (aeval a2)
  | AMult a1 a2 => OptF.mul (aeval a1) (aeval a2)
  | ADiv a1 a2 => OptF.div (aeval a1) (aeval a2)
  end.

End Option_Denote_Aexp.

(** Another reasonable formalization is to define the denotation relationally.
In other words, we would use [aeval a st v] as a proposition to say that the
evaluation of [a] is [v] on program state [st]. *)

Module Relational_Denote_Aexp.

Inductive aeval : aexp -> state -> Z -> Prop :=
  | E_ANum n st:
      aeval (ANum n) st n
  | E_AId X st:
      aeval (AId X) st (st X)
  | E_APlus (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2) :
      aeval (APlus e1 e2) st (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2) :
      aeval (AMinus e1 e2) st (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2) :
      aeval (AMult e1 e2) st (n1 * n2)
  | E_ADiv (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2)
      (H3 : n2 <> 0) :
      aeval (ADiv e1 e2) st (n1 / n2).

End Relational_Denote_Aexp.

(** In principle, both definitions make sense here. But the relational version
is more flexible in adding side conditions. Here is another example. *)

Module Bounded_Evaluation.

Definition max32: Z := 2^31 -1.
Definition min32: Z := - 2^31.

Inductive signed32_eval: aexp -> state -> Z -> Prop :=
  | E32_ANum (n: Z) st
      (H: min32 <= n <= max32):
      signed32_eval (ANum n) st n
  | E32_AId (X: var) st
      (H: min32 <= st X <= max32):
      signed32_eval (AId X) st (st X)
  | E32_APlus a1 a2 st v1 v2
      (H1: signed32_eval a1 st v1)
      (H2: signed32_eval a2 st v2)
      (H3: min32 <= v1 + v2 <= max32):
      signed32_eval (APlus a1 a2) st (v1 + v2)
  | E32_AMinus a1 a2 st v1 v2
      (H1: signed32_eval a1 st v1)
      (H2: signed32_eval a2 st v2)
      (H3: min32 <= v1 - v2 <= max32):
      signed32_eval (AMinus a1 a2) st (v1 - v2)
  | E32_AMult a1 a2 st v1 v2
      (H1: signed32_eval a1 st v1)
      (H2: signed32_eval a2 st v2)
      (H3: min32 <= v1 * v2 <= max32):
      signed32_eval (AMult a1 a2) st (v1 * v2)
  | E32_ADiv a1 a2 st v1 v2
      (H1: signed32_eval a1 st v1)
      (H2: signed32_eval a2 st v2)
      (H3: v2 <> 0)
      (H4: v1 <> -1 \/ v2 <> min32):
      signed32_eval (ADiv a1 a2) st (v1 / v2).

(** This definition defines the denotational semantics of expression evaluation
inside signed 32-bit range. We have seen the majority part of this. The case
for division is interesting.

Usually, dividing a signed 32-bit integer by another should result in a signed
32-bit integer as long as the divisor is not zero. But in fact, there is
another exception: dividing [-2^31] by [-1]. The math result should be [2^31]
which is not a signed 32-bit number. This side condition is also part of C
standard of expression evaluation. *)

End Bounded_Evaluation.

(** In summary, if we use [option] types to formalize expressions' denotations:

       - [aeval a st = Some v] when evaluation succeeds;

       - [aeval a st = None] when evaluation fails.

If we use relations to formaliza expressions' denotations:

       - [aeval a st v] when evaluation succeeds;

       - there is no [v] such that [aeval a st v] when evaluation fails.

*)

(* ################################################################# *)
(** * Small Step Semantics for Run Time Error *)

Module Small_Step_Aexp.

Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum (st X))

  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | AS_Minus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMinus a1 a2) (AMinus a1 a2')
  | AS_Minus : forall st n1 n2,
      astep st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | AS_Mult1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMult a1 a2) (AMult a1 a2')
  | AS_Mult : forall st n1 n2,
      astep st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2))

  | AS_Div1 : forall st a1 a1' a2,                    (* <-- new *)
      astep st
        a1 a1' ->
      astep st
        (ADiv a1 a2) (ADiv a1' a2)
  | AS_Div2 : forall st a1 a2 a2',                    (* <-- new *)
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (ADiv a1 a2) (ADiv a1 a2')
  | AS_Div : forall st n1 n2,                         (* <-- new *)
      n2 <> 0 ->
      astep st
        (ADiv (ANum n1) (ANum n2)) (ANum (n1 * n2))
.

(** Notice that there are two situations that no further evaluation step can
happen.

      - Evaluation terminates.

      - Evaluation arrives at an error state.

When there is no [a2] such that [astep st a1 a2], the predicate [aexp_halt a1]
judges which situation between these two above describes the current evulation
status. *)

End Small_Step_Aexp.

(** Boolean Expressions *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Module Relational_Denote_Bexp.
Import Relational_Denote_Aexp.

(** For boolean expressions' denotations, we use Coq's [bool] type in a
relational definition. *)

Print bool.
(* Inductive bool :=  true : bool | false : bool *)

Print negb.
(* negb =
     fun b : bool =>
       match b with
       | true => false
       | false => true
       end
   : bool -> bool *)

Print andb.
(* andb =
     fun b1 b2 : bool =>
       match b1 with
       | true => b2
       | false => false
       end
   : bool -> bool -> bool *)

Inductive beval : bexp -> state -> bool -> Prop :=
  | E_BTrue st:
      beval BTrue st true
  | E_BFalse st:
      beval BFalse st false
  | E_BEqTrue (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2)
      (H3 : n1 = n2) :
      beval (BEq e1 e2) st true
  | E_BEqFalse (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2)
      (H3 : n1 <> n2) :
      beval (BEq e1 e2) st false
  | E_BLeTrue (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2)
      (H3 : n1 < n2) :
      beval (BLe e1 e2) st true
  | E_BLeFalse (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1)
      (H2 : aeval e2 st n2)
      (H3 : n1 >= n2) :
      beval (BLe e1 e2) st false
  | E_BNot (e: bexp) (b: bool) st
      (H1 : beval e st b):
      beval (BNot e) st (negb b)
  | E_BAnd (e1 e2: bexp) (b1 b2: bool) st
      (H1 : beval e1 st b1)
      (H2 : beval e2 st b2):
      beval (BAnd e1 e2) st (andb b1 b2)
      .

End Relational_Denote_Bexp.

Module Small_Step_Bexp.
Import Small_Step_Aexp.

(** The small step semantics of [bexp] is not interesting at all. Although
run time error may occur inside internal integer expression's evaluation, we
just need to copy-paste our original small step definition for [bexp]. *)

Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : state -> bexp -> bexp -> Prop :=

  | BS_Eq1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
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
      astep st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
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

End Small_Step_Bexp.

(* ################################################################# *)
(** * Original Commands *)

Module Original_Com.

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** Originally, we use binary relations among beginning states and ending
states to represent different program commands' denotations. Specifically,
we did define a ternary Coq predicate [ceval] such that:

      - [ceval c st1 st2] when executing [c] from state [st1] will terminate
        in program state [st2];

      - there is no [st2] such that [ceval c st1 st2] when executing [c] from
        state [st1] will not terminate.

Now, a program may crush -- terminate unexpectedly by a run time error. A
natural idea is to formalize program commands' denotations by a similar
approach used in [aeval] in [Relational_Denote_Aexp]:

      - [ceval c st1 st2] when executing [c] from state [st1] is safe and will
        terminate in program state [st2];

      - there is no [st2] such that [ceval c st1 st2] when executing [c] from
        state [st1] will cause run time error.

This does NOT work because we cannot talk about nonterminating execution then.
Thus, the following definition use ternary relations among:

      - [com], for programs

      - [state], for begining states

      - [option state], for ending states

to define [ceval]. Specifically,

      - [ceval c st1 (Some st2)] when executing [c] from state [st1] is safe
        and will terminate in program state [st2];

      - [ceval c st1 None] when executing [c] from state [st1] will cause run
        time error;

      - there is no way that [ ceval c st1 _ ] may hold when executing [c] from
        state [st1] is safe but will not terminate.

We use Coq's inductive predicate to complete this definition. *)

Module Relational_Denote_Com.
Import Relational_Denote_Aexp.
Import Relational_Denote_Bexp.

Inductive ceval : com -> state -> option state -> Prop :=
  | E_Skip st:
      ceval CSkip st (Some st)
  | E_AssSucc st1 st2 X E
      (H1: aeval E st1 (st2 X))                      (* <-- evaluation succeeds *)
      (H2: forall Y, X <> Y -> st1 Y = st2 Y):
      ceval (CAss X E) st1 (Some st2)
  | E_AssFail st1 X E
      (H1: forall st2, ~aeval E st1 (st2 X)):        (* <-- evaluation fails *)
      ceval (CAss X E) st1 None
  | E_SeqSafe c1 c2 st st' o
      (H1: ceval c1 st (Some st'))                   (* <-- first command is safe *)
      (H2: ceval c2 st' o):
      ceval (CSeq c1 c2) st o
  | E_SeqCrush c1 c2 st
      (H1: ceval c1 st None):                        (* <-- first command crush *)
      ceval (CSeq c1 c2) st None
  | E_IfTrue st o b c1 c2
      (H1: beval b st true)
      (H2: ceval c1 st o):
      ceval (CIf b c1 c2) st o
  | E_IfFalse st o b c1 c2
      (H1: beval b st false)
      (H2: ceval c2 st o):
      ceval (CIf b c1 c2) st o
  | E_IfFail st b c1 c2                              (* <-- evaluation fails *)
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
  | E_WhileFail st b c                               (* <-- evaluation fails *)
      (H1: ~ beval b st true)
      (H2: ~ beval b st false):
      ceval (CWhile b c) st None.

(** This definition is very similar to what we did to control flow programs.
The situations here are actually simpler -- there are only two kinds of exit:
safe exit and crush exit. *)

End Relational_Denote_Com.

Module Small_Step_Com.
Import Small_Step_Aexp.
Import Small_Step_Bexp.

(** The small step semantic definition is again not very interesting. Our
original one is just good to use. *)

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep st X a a'
      (H1: astep st a a'):
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass st1 st2 X n
      (H1: st2 X = n)
      (H2: forall Y, X <> Y -> st1 Y = st2 Y):
      cstep (CAss X (ANum n), st1) (CSkip, st2)
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

(** Using multi-step relation, we can classify different execution traces:

      - [multi_cstep (c, st1) (CSkip, st2)], if executing [c] from state [st1]
        is safe and will terminate in program state [st2];

      - [multi_cstep (c, st1) (c', st')] and there is no [c''] and [st''] such
        that [cstep (c', st') (c'', st'')], if executing [c] from state [st1]
        will cause run time error;

      - for any [c'] and [st'], if [multi_cstep (c, st1) (c', st')] then there
        exists [c''] and [st''] such that [cstep (c', st') (c'', st'')] -- this
        condition tells that executing [c] from state [st1] is safe but will
        not terminate.
*)

End Small_Step_Com.

End Original_Com.

(* ################################################################# *)
(** * Nondeterminism *)

(** Besides run time error, we can define program semantics for programs with
nondeterministic behavior. *)

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CChoice (c1 c2: com).                     (* <-- new *)

(** Here, we add one more constructor to the syntax trees of program commands.
To execute [CChoice c1 c2] is to execute either [c1] or [c2]. A compiler or
some external environment may decide which one to choose. Since we did use
relational definitions to formalize programs' denotational semantics and small
step semantics, it is easy to extend those definitions to nondeterministic 
behavior. *)

Module Relational_Denote_Com.
Import Relational_Denote_Aexp.
Import Relational_Denote_Bexp.

Inductive ceval : com -> state -> option state -> Prop :=
  | E_Skip st:
      ceval CSkip st (Some st)
  | E_AssSucc st1 st2 X E
      (H1: aeval E st1 (st2 X))
      (H2: forall Y, X <> Y -> st1 Y = st2 Y):
      ceval (CAss X E) st1 (Some st2)
  | E_AssFail st1 X E
      (H1: forall st2, ~aeval E st1 (st2 X)):
      ceval (CAss X E) st1 None
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
      ceval (CWhile b c) st None
  | E_ChoiceLeft st o c1 c2                        (* <-- new *)
      (H1: ceval c1 st o):
      ceval (CChoice c1 c2) st o
  | E_ChoiceRight st o c1 c2                       (* <-- new *)
      (H1: ceval c2 st o):
      ceval (CChoice c1 c2) st o.

(** This is not an ideal definition. Because it cannot say that: a program may
and may not terminate. *)

End Relational_Denote_Com.

Module Small_Step_Com.
Import Small_Step_Aexp.
Import Small_Step_Bexp.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep st X a a'
      (H1: astep st a a'):
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass st1 st2 X n
      (H1: st2 X = n)
      (H2: forall Y, X <> Y -> st1 Y = st2 Y):
      cstep (CAss X (ANum n), st1) (CSkip, st2)
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
        (CIf b (CSeq c (CWhile b c)) CSkip, st)
  | CS_CChoiceLeft st c1 c2:
      cstep (CChoice c1 c2, st) (c1, st)
  | CS_CChoiceRight st c1 c2:
      cstep (CChoice c1 c2, st) (c2, st).

End Small_Step_Com.

(* Thu May 14 06:43:37 CST 2020 *)
