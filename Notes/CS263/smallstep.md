---
title: 【Programming Language】Small Step Semantics
url: pl-smallstep
date: 2020-04-07 14:01:09
tags: 
- Programming Language

categories: 
- Courses

---

Week 6 of 2020 Spring

<!--more-->

[toc]

## Review of Assignment 3

整数类型表达式的左右翻转操作对常见的优化是否起作用？
In comparison, which one of the following is the better optimazation?
- do [fold_constants] directly;
- do [fold_constants] after [aexp_reverse].
Choose one correct statement:
1. They always generate results with the same length.
2. The first one always generates shorter (or equivalent) result and statement 0 is wrong.
3. The second one always generates shorter (or equivalent) result and statement 0 is wrong.
4. They are not comparable.

对程序语言语法树的理解。一颗子树是否能化简成一个常数，与翻转是没有关系的。因此都选[0]。

注意到：`reverse (X + 1 + 2) == (2 + (1 + X)) != (2 + 1 + X)`.

## General Idea: Small Step

霍尔语义对程序功能的描述更接近。小步语义是颗粒度更细的语义，更接近我们对程序执行过程的理解。但这并不意味着颗粒度更细是一个对于具体电子元器件操作的描述。

有关小步语义更多的知识和应用
- 类型安全（type safety）、progress and preservation。
- Python,C++20中的lambda表达式，对IMP语言的扩展。（evaluation context）

与大步相对（在某种程度上是指称语义的近义词，怎样的起始，到怎样的终止）。小步语义还关注中间过程。

In short, we will learn how to define a "small-step" relation that specifies, for a given program, how the "atomic steps" of computation are performed.

## Small Step Semantics for Expression Evaluation

我们还是用二元关系表示小步关系。

Given an expression `a`, we can compute its value as follows:
- Take `a` as the starting state of the machine.
- Repeatedly use the step relation to find a sequence of machine states, starting with `a`, where each state steps to the next.
- When no more forward step is possible, "read out" the final state of the machine as the result of computation.

我们定义表达式和表达式的二元关系。

```Coq
Definition aexp_halt (a: aexp): Prop :=
  match a with
  | ANum _ => True
  | _ => False
  end.

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum (st X))
  (* 加法表达式 *)
  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 -> （* 左边已化简结束，则化简右边 *）
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st  (*左右都化简，则左右都应该是常数，求值*)
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))
  ... 类似定义减法和乘法
```

我们也可以写成inference rule的形式。

```Coq
Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : state -> bexp -> bexp -> Prop :=
  (* 先化简左边，再化简右边，在计算 *)
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
  (* 类似有Le... *)

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

  (* 描述AND的短路求值优化现象 *)
  | BS_AndStep : forall st b1 b1' b2,
      bstep st b1 b1' -> (* 左边可以化简 就化简 *)
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st  (* 左边是False，就不再做任何操作 *)
       (BAnd BFalse b) BFalse.

(** Remark: when evaluating a conjunction of two boolean expression, we use short circuit evaluation. That is, the right hand side will not be evaluated if the left hand side is false. For example, when [X]'s value is 1, [X <= 0 && 0 < X + 10] will be evaluated by the following steps:
    X <= 0 && 0 <= X + 10
    --> 1 <= 0 && 0 <= X + 10
    --> False && 0 <= X + 10
    --> False.
*)
```

## Multi-step Relation

Some handy tactics.
- `induction_1n` and `induction_n1`;
- `transitivity_1n`, `transitivity_n1`, `etransitivity_1n` and `etransitivity_n1`;
- `unfold_with_1n` and `unfold_with_n1`.

The multi-step relations satisfy the congruence property. For example, the following theorem says:

$$
\begin{array}{c}
a_1 \rightarrow^{*} a_1' \\
\hline
a_1 + a_2 \rightarrow^{*} a_1' + a_2
\end{array}
$$

Why? Because for every single step from $a_1$ to $a_1'$, we can construct a corresponding step from $a_1 + a_2$ to $a_1' + a_2$. （By 对应构造）
```Coq
(*  a1   -->  b   -->  c   -->  d   -->   a1'
    a1+a2 --> b+a2 --> c+a2 --> d+a2 --> a1'+a2  *)
Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof. (* by induction_1n or induction_n1 + transitivity*)
Abort.

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').
```

We can prove similar properties for `AMinus`, `AMult`, `BEq`, `BLe`, `BNot` and `BAnd`. (i.p. `BAnd` only holds for left side)

## Small Step Semantics for Simple Imperative Programs

The semantics of commands is more interesting. For expression evaluation, the program states are stable. In other words, we only talked about how an expression will be reduced to another one on a _fixed_ program state. But for
program execution, the program states are modified. Thus, a ternary relation among the program state, the command to execute and the residue command after one step is not expressive enough to describe programs' behavior. A quaternary relation is needed.

与表达式求值不同，我们刻画程序的小步语义时，程序状态是改变的。程序的小步语义**既要包含程序的状态，也要包含程序**。

Specifically, we would like to define a predicate `cstep` such that

    cstep c1 st1 c2 st2

一般，我们将四元关系写作两个二元有序对(待运行的程序+当前的程序状态)之间的二元关系。

```Coq
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a', (* 赋值语句表达式化简 *)
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n, (* 赋值语句化简完成，修改程序状态 *)
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2, (* 顺序执行，做一步，可能是改c1，也可能是改st *)
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2, (* 顺序执行第一句执行完 *)
      cstep (Skip ;; c2, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2, (* IF 先对布尔表达式化简 *)
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2, (* 化简成True *)
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2, (* 化简成False *)
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c, (* 相当于展开成IF语句，出人意料的简单 *)
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).
```

Tricks：
- We use `Skip` as an "empty residue command".

  - An assignment command reduces to `Skip` (and an updated state).

  - The sequencing command waits until its left-hand subcommand has reduced to `Skip`, then throws it away so that reduction can continue with the right-hand subcommand.

- We reduce a `While` command by transforming it into a conditional followed by the same `While`.

定义完小步关系后，我们自然可以用自反传递闭包定义多步关系。
```Coq
Definition multi_cstep: com * state -> com * state -> Prop :=
  clos_refl_trans cstep.
```

也具有Congruence性质。（局部的多步关系可以决定程序整体的多步关系）注意，这里的st1'不一定会是终止状态，是任意的中间状态。（PF by induction on definition）

```Coq
Theorem multi_congr_CSeq: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (c1 ;; c2, st1) (c1';; c2, st1').

Theorem multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
    (If b Then c1 Else c2 EndIf, st)
    (If b' Then c1 Else c2 EndIf, st).
```
