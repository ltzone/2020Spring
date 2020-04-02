---
title: 【Programming Language】Denotational Semantics 4
url: pl-deno4
date: 2020-04-02 10:26:01
tags: 
- Programming Language

categories: 
- Courses

---

Week 5 of 2020 Spring.

<!--more-->

[toc]

## Inductively Defined Denotational Semantics

```Coq
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      ceval CSkip st  st
  | E_Ass  : forall st1 st2 X E,
      st2 X = aeval E st1 ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      ceval (CAss X E) st1 st2
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st' ->
      ceval c2 st' st'' ->
      ceval (c1 ;; c2) st st''
  | E_IfTrue : forall st st' b c1 c2,
      beval b st ->
      ceval c1 st st' ->
      ceval (If b Then c1 Else c2 EndIf) st st'
  | E_IfFalse : forall st st' b c1 c2,
      ~ beval b st ->
      ceval c2 st st' ->
      ceval (If b Then c1 Else c2 EndIf) st st'
  | E_WhileFalse : forall b st c,
      ~ beval b st ->
      ceval (While b Do c EndWhile) st st
  | E_WhileTrue : forall st st' st'' b c,
      beval b st ->
      ceval c st st' ->
      ceval (While b Do c EndWhile) st' st'' ->
      ceval (While b Do c EndWhile) st st''.
```


也被称为大步语义, 我们一般用指称语义特指此前lec中定义的denotational semantics.

## Understanding Inductive Propositions 

### Stone game

```Coq
Inductive kind: Type :=
| previous_player_win (* 后手获胜 *)
| next_player_win. (* 先手获胜 *)

Inductive state_class: Z -> kind -> Prop :=
| neg_illegal: forall n,
    n < 0 ->
    state_class n next_player_win
| zero_win:
    state_class 0 previous_player_win
| winner_strategy_1: forall n,
    n > 0 ->
    state_class (n-1) previous_player_win ->
    state_class n next_player_win 
| winner_strategy_2: forall n,
    n > 0 ->
    state_class (n-2) previous_player_win ->
    state_class n next_player_win 
| winner_strategy_3: forall n,
    n > 0 ->
    state_class (n-3) previous_player_win ->
    state_class n next_player_win 
| loser_strategy: forall n,
    n > 0 ->
    state_class (n-1) next_player_win ->
    state_class (n-2) next_player_win ->
    state_class (n-3) next_player_win ->
    state_class n previous_player_win.
```

显然, 四的倍数都是后手获胜.

```Coq
Theorem ten_wins: state_class 10 next_player_win.
```

### Reflexive Transitive Closure

自反传递闭包
```Coq
Inductive clos_refl_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

Inductive clos_refl_trans_1n {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rt1n_refl : forall x, clos_refl_trans_1n R x x
    | rt1n_trans_1n : forall x y z,
          R x y ->
          clos_refl_trans_1n R y z ->
          clos_refl_trans_1n R x z.

Inductive clos_refl_trans_n1 {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rtn1_refl : forall x, clos_refl_trans_n1 R x x
    | rtn1_trans_n1 : forall x y z : A,
          R y z ->
          clos_refl_trans_n1 R x y ->
          clos_refl_trans_n1 R x z.
```

## 32-bit Evaluation Again

We redefine it again as an inductive predicate in Coq.

```Coq
Inductive signed32_eval: aexp -> state -> Z -> Prop :=
  | S32_ANum: forall (n: Z) st,
      min32 <= n <= max32 ->
      signed32_eval (ANum n) st n
  | S32_AId: forall (X: var) st,
      min32 <= st X <= max32 ->
      signed32_eval (AId X) st (st X)
  | S32_APlus: forall a1 a2 st v1 v2,
      signed32_eval a1 st v1 ->
      signed32_eval a2 st v2 ->
      min32 <= v1 + v2 <= max32 ->
      signed32_eval (APlus a1 a2) st (v1 + v2)
  | S32_AMinus: forall a1 a2 st v1 v2,
      signed32_eval a1 st v1 ->
      signed32_eval a2 st v2 ->
      min32 <= v1 - v2 <= max32 ->
      signed32_eval (AMinus a1 a2) st (v1 - v2)
  | S32_AMult: forall a1 a2 st v1 v2,
      signed32_eval a1 st v1 ->
      signed32_eval a2 st v2 ->
      min32 <= v1 * v2 <= max32 ->
      signed32_eval (AMult a1 a2) st (v1 * v2).
```

定义子表达式的方案

```Coq
Inductive sub_aexp: aexp -> aexp -> Prop :=
| sub_aexp_refl: forall e: aexp,
    sub_aexp e e
| sub_aexp_APlus1: forall e e1 e2: aexp,
    sub_aexp e e1 ->
    sub_aexp e (APlus e1 e2)
| sub_aexp_APlus2: forall e e1 e2: aexp,
    sub_aexp e e2 ->
    sub_aexp e (APlus e1 e2)
| sub_aexp_AMinus1: forall e e1 e2: aexp,
    sub_aexp e e1 ->
    sub_aexp e (AMinus e1 e2)
| sub_aexp_AMinus2: forall e e1 e2: aexp,
    sub_aexp e e2 ->
    sub_aexp e (AMinus e1 e2)
| sub_aexp_AMult1: forall e e1 e2: aexp,
    sub_aexp e e1 ->
    sub_aexp e (AMult e1 e2)
| sub_aexp_AMult2: forall e e1 e2: aexp,
    sub_aexp e e2 ->
    sub_aexp e (AMult e1 e2).
```

可以证明, eval32的子表达式也满足eval 32
```Coq
Theorem signed32_eval_sub_aexp: forall e1 e2 st,
  sub_aexp e1 e2 ->
  (exists v2, signed32_eval e2 st v2) ->
  (exists v1, signed32_eval e1 st v1).
```

## Loop-free Programs

Now, we prove that a loop free program always terminate.

```Coq
Inductive loop_free: com -> Prop :=
  | loop_free_skip:
      loop_free Skip
  | loop_free_asgn: forall X E,
      loop_free (CAss X E)
  | loop_free_seq: forall c1 c2,
      loop_free c1 ->
      loop_free c2 ->
      loop_free (c1 ;; c2)
  | loop_free_if: forall b c1 c2,
      loop_free c1 ->
      loop_free c2 ->
      loop_free (If b Then c1 Else c2 EndIf).

Theorem loop_free_terminate: forall c,
  loop_free c ->
  (forall st1, exists st2, ceval c st1 st2).
```

递归函数也是可以定义的, 但inductive定义的好处在于拓展性强, 如a finer loop_free

```Coq
Inductive loop_free': com -> Prop :=
  | loop_free'_skip:
      loop_free' Skip
  | loop_free'_asgn: forall X E,
      loop_free' (CAss X E)
  | loop_free'_seq: forall c1 c2,
      loop_free' c1 ->
      loop_free' c2 ->
      loop_free' (c1 ;; c2)
  | loop_free'_if: forall b c1 c2,
      loop_free' c1 ->
      loop_free' c2 ->
      loop_free' (If b Then c1 Else c2 EndIf)
  | loop_free'_if_then: forall b c1 c2,
      (forall st, beval b st) ->
      loop_free' c1 ->
      loop_free' (If b Then c1 Else c2 EndIf)
  | loop_free'_if_else: forall b c1 c2,
      (forall st, ~ beval b st) ->
      loop_free' c2 ->
      loop_free' (If b Then c1 Else c2 EndIf)
  | loop_free'_while_false: forall b c,
      (forall st, ~ beval b st) ->
      loop_free' (While b Do c EndWhile).
```

