---
title: 【Programming Language】Hoare Logic
url: pl-hoare4
date: 2020-03-12 08:02:33
tags: 
- Programming Logic

categories: 
- Courses

---

Week 2 of 2020 Spring. Use Hoare Logic to Prove Programs

**KeyWords**: Programming Logic, Hoare Logic

<!--more-->

[toc]

## Program correctness proof in Coq

Omitted. See Source File.
- assert_subst. 改写
- assert_simpl. `{[ X + U ]} -> {[X]} + {[U]}`


## Derived Proof Rules and Programmable Proof Tactics

用现有规则推出导出规则. 在Imp库中, 已经有
```Coq
Theorem derives_refl: forall P : Assertion, P |-- P
```
我们可以借此证明有关Consequence Rule的推论
```Coq
(** 只包含前条件的Consequence Rule. *)
Corollary hoare_consequence_pre: forall P P' Q c,
  P |-- P' ->
  {{ P' }} c {{ Q }} ->
  {{ P }} c {{ Q }}.
(** 只包含后条件的Consequence Rule. *)
Corollary hoare_consequence_post: forall P Q Q' c,
  {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  {{ P }} c {{ Q }}.
```

在Imp中, 我们有:
```Coq
Theorem AND_left1: forall P Q R : Assertion,
       P |-- R -> P AND Q |-- R
Theorem AND_left2: forall P Q R : Assertion,
       Q |-- R -> P AND Q |-- R
```
我们可以证明hoare_if的较弱版本:
```Coq
Corollary hoare_if_weak : forall P Q b c1 c2,
  {{P}} c1 {{Q}} ->
  {{P}} c2 {{Q}} ->
  {{P}} If b Then c1 Else c2 EndIf {{Q}}.
```

Derived Rules help us describe how we understand logic proofs. We use proof rules "combos".


## Decorated Program as informal Hoare Logic Proof
Hoare Logic is **compositional** (我们可以由部分程序的正确性推导出整个程序的正确性) and the structure of proofs exactly follows the program.

