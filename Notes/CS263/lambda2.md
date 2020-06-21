---
title: 【Programming Language】Lambda Calculus 2
url: pl-lambda2
date: 2020-06-02 14:14:47
tags: 
- Programming Language

categories: 
- Courses

---

Week 14 of 2020 Spring

<!--more-->

[toc]

## Review

Lambda expressions' types are defined inductived as a ternary relation among type contexts (类型环境), lambda expressions and types.
```
Gamma |- t \in T
```
Remark. In this setting, one expression may have different types, which seems not natural. In modern languages like C++ and ocaml, polymorphic types (like `forall T, T ~> T` ) are introduced so that each legal lambda expression has only one type, if enough type annotations are provided. Also, type inference algorithms are designed so that the compiler can deduce types from limited annotations. We will not include polymorphic types and type inferences in this course.

实际程序语言中，我们往往要求一个类型推导算法，使得我们可以借助代码中有限的类型标注，推导整个表达式的类型。简单起见，本节我们只做类型定义以及类型安全性质的证明（progress and preservation）。

## Properties Of Evaluation Results
```Coq
Lemma eval_result_bool : forall (t: tm),
  empty_context |- t \in TBool ->
  tm_halt t ->
  exists b: bool, t = b.

Lemma eval_result_int : forall (t: tm),
  empty_context |- t \in TInt ->
  tm_halt t ->
  exists n: Z, t = n.

Ltac deduce_int_bool_result H1 H2 :=
  first
    [ let n := fresh "n" in
      let H := fresh "H" in
      pose proof eval_result_int _ H1 H2 as [n H]
    | let b := fresh "b" in
      let H := fresh "H" in
      pose proof eval_result_bool _ H1 H2 as [b H]
    ].
```




## Progress

### halt not pending

tm_pend: 自己终止，且参数需要化简
tm_halt_not_pend: 自己终止，参数也不需要化简。

```Coq
Inductive halt_not_pend: tm -> Prop :=
  | HNP_and_false:
      halt_not_pend (app Oand false)
  | HNP_if1: forall b: bool,
      halt_not_pend (app Oifthenelse b)
  | HNP_if2: forall (b: bool) (t: tm),
      halt_not_pend (app (app Oifthenelse b) t).

Lemma base_pend_or_not_pend: forall t,
  tm_base_halt t ->
  tm_base_pend t \/ halt_not_pend t.

Lemma pend_or_not_pend: forall t,
  tm_halt t ->
  tm_pend t \/ halt_not_pend t.
```
### Theorem
```Coq
Theorem progress : forall t T,
  empty_context |- t \in T ->
  tm_halt t \/ exists t', step t t'.
Proof.
  intros t T Ht.
  remember empty_context as Gamma.
  induction Ht; subst Gamma.
```
虽然我们是对`has_type`命题归纳，但实际上我们应该理解成对`t`的语法树进行归纳。对function application：`app t1 t2`

1. `tm_halt t1`
   - `tm_pend t1`
     - `tm_halt t2`，加上函数与参数类型吻合，则可以往前step一步。（待证明）
     - `t2 --> t2'`，直接使用`S_app2`.
   - `tm_halt_not_pend t1`符合progress性质（待证明）
2. `t1 --> t1'`
   使用`S_app1`。

### Lemmas

我们为上面的证明加上如下引理。

```Coq
Lemma app_pending_halting_progress: forall t1 t2 T11 T12,
  empty_context |- t1 \in (T11 ~> T12) ->
  empty_context |- t2 \in T11 ->
  tm_pend t1 ->
  tm_halt t2 ->
  tm_halt (app t1 t2) \/ exists t', step (app t1 t2) t'.
```
讨论`t1`是什么
- abs显然，t2已经完成化简，可以直接用beta reduction，直接根据CBV性质。
- 常量，待证。（分为整数、布尔、算子），前两者与Arr类型推出矛盾。
  对算子：第一个参数T11要么是整数要么是布尔，因此我们可以通过对算子进行分类讨论，根据具体的算子推导出T11、T12分别是什么。
  e.g.:对OPlus: 可以推导出 t2是整数类型，且t2已经完成化简，因此t2一定是一个整数常量（引理）。替换后显然满足tm_halt性质。
- 根据基础类型额外定义的情况。对`tm_base_pend t1`进行inversion。方法类似。

后两者我们只需做简单的分类讨论就可以了。



```Coq
Lemma app_not_pending_progress: forall t1 t2 T11 T12,
  empty_context |- t1 \in (T11 ~> T12) ->
  empty_context |- t2 \in T11 ->
  halt_not_pend t1 ->
  tm_halt (app t1 t2) \/ exists t', step (app t1 t2) t'.
```

分类讨论，仅三种情况OK。

## Lambda Calculus With Reference

### Definition

```Coq
Inductive op : Type :=
  | Oplus
  | Ominus
  | Omult
  | Oeq
  | Ole
  | Onot
  | Oand
  | Oifthenelse
  | Ounitele
  | Oread (* new 读某个地址上的值 *)
  | Owrite (* new 写到某个地址上去 *)
  | Oalloc (* new 要求分配一块新的空间 *)
  .
```
Examples
```Coq
Definition ex1 : tm := app Oalloc 0. (* Alloc a new memory, 0 is stored there *)

Definition ex2 : tm := app (abs "p" (app (app Owrite "p") 1)) (app Oalloc 0).
(* 向新创建的地址空间写上1 *)

Definition ex3 : tm := app (abs "p" (app Oread"p")) (app Oalloc 0).
(* 读新创建的地址上的值 *)
```

问题：明确了操作，函数本身的值是什么？`Owrite`？只有操作而没有返回值，所以我们引入`Unit`作为类型，它只有一个元素`Ouitele`。

### Let expression

一般，我们认为let表达式是lambda表达式中语法的另一种形式。

```Coq
Definition letx (x: string) (t1 t2: tm): tm :=
  app (abs x t2) t1.

Notation "'\let' x '\be' t1 '\in' t2" :=
  (letx x t1 t2) (at level 20).
```

一些更复杂的例子
```Coq
Example get_and_add :=
  abs "p" (
    \let "x" \be (app Oread "p") \in   (* 把地址p中的值读到x中去 *)
    \let "_" \be (app (app Owrite "p") (app (app Oplus "x") 1)) \in
    "x").  (* 把x+1的值写到p中去，并且最后返回读p时的x *)

Example alloc_get :=
  \let "p" \be (app Oalloc 0) \in (* 先获得一块地址，里面存储的值是0 *)
  app get_and_add "p".  (* 对这块地址做get和add操作，返回值会是0，但地址中的值是1 *)

Example alloc_get3 :=
  \let "p" \be (app Oalloc 1) \in
  \let "x" \be (app get_and_add "p") \in (* p存了2，x=1 *)
  \let "y" \be (app get_and_add "p") \in (* p存了3，x=2 *)
  \let "z" \be (app get_and_add "p") \in (* p存了4，x=3 *)
  (100 * "x" + 10 * "y" + "z")%tm. (* 返回值123 *)

Print alloc_get3.

Example swap := 
  abs "p" (abs "q" (    (* p、q二元函数 *)
    \let "x" \be (app Oread "p") \in  (* 临时变量x，读p中的值 *)
    \let "_" \be (app (app Owrite "p") (app Oread "q")) \in (* 读q中的值写入p *)
    app (app Owrite "q") "x")).  (* x的值写入q *)

Example swap12 :=
  \let "p" \be (app Oalloc 1) \in
  \let "q" \be (app Oalloc 2) \in
  \let "_" \be (app (app swap "p") "q") \in
  (10 * (app Oread "p") + app Oread "q")%tm.

Example fact3 :=
  \let "p" \be (app Oalloc (abs "x" "x")) \in
  \let "fact" \be
     (abs "x" 
       (app (app (app Oifthenelse ("x" == 0)%tm)
          1)
          ("x" * (app (app Oread "p") ("x" - 1)))%tm)) \in
  \let "_" \be (app (app Owrite "p") "fact") \in
  app "fact" 3.

Example fact4 :=
  \let "p" \be (app Oalloc (abs "x" "x")) \in
  \let "fact" \be
     (abs "x" 
       (app (app (app Oifthenelse ("x" == 0)%tm)
          1)
          ("x" * (app (app Oread "p") ("x" - 1)))%tm)) \in
  \let "_" \be (app (app Owrite "p") "fact") \in
  app "fact" 4.
```

### State

现在我们的表达式有了side effect，需要引入程序状态。

下面我们把程序状态定义为一列lambda表达式。

```Coq
Definition state := list tm.

Fixpoint read_state (s: state) (p: addr): option tm :=
  match s, p with
  | t :: _, O => Some t
  | _ :: s', S p' => read_state s' p'
  | _, _ => None
  end.

Fixpoint write_state (s: state) (p: addr) (t: tm): option state :=
  match s, p with
  | _ :: s', O => Some (t :: s')
  | s0 :: s', S p' =>
      match write_state s' p' t with
      | Some s'' => Some (s0 :: s'')
      | None => None
      end
  | _, _ => None
  end.
```

新的小步语义是表达式和状态的二元组之间的二元关系
```Coq
Inductive step: tm * state -> tm * state -> Prop :=
  | S_base: forall t1 t2 s1 s2,
      base_step (t1, s1) (t2, s2) ->
      step (t1, s1) (t2, s2) (* 基础类型的化简定义 *)
  | S_beta: forall x t1 t2 s, (* beta reduction 不改变程序状态 *)
      tm_halt t2 ->
      step (app (abs x t1) t2, s) (t1 [ x |-> t2], s)
  | S_app1: forall t1 t1' t2 s s',
      step (t1, s) (t1', s') ->
      step (app t1 t2, s) (app t1' t2, s')
  | S_app2: forall t1 t2 t2' s s',
      tm_pend t1 ->
      step (t2, s) (t2', s') ->
      step (app t1 t2, s) (app t1 t2', s')
.
```
基础类型的化简定义：
```Coq
Inductive base_step: tm * state -> tm * state -> Prop :=
  | BS_plus: forall (n1 n2: Z) (s: state), (* 与此前一致，加上st而已 *)
      base_step (app (app Oplus n1) n2, s) (n1 + n2: tm, s) (* tm是notation的类型标注 *)
  ...
  | BS_read: forall (p: addr) (s: state) (t: tm),
      read_state s p = Some t ->
      base_step (app Oread p, s) (t, s)
  | BS_write: forall (p: addr) (t: tm) (s s': state),
      write_state s p t = Some s' ->
      base_step (app (app Owrite p) t, s) (Ounitele: tm, s')
  | BS_alloc: forall (t: tm) (s: state),
      base_step (app Oalloc t, s) (new_address s: tm, alloc_state s t)
.
```



## Typing
规定，只能malloc不能free。

一个简单的类型系统。可能有些程序在该类型系统下写不出来。

```Coq
Inductive ty : Type :=
  | TBool : ty
  | TInt : ty
  | TArrow : ty -> ty -> ty
  | TUnit : ty
  | TRef : ty -> ty (* new 表示某一类型的地址* *).

Notation "T1 ~> T2" := (TArrow T1 T2) (right associativity, at level 30).

Definition context := string -> option ty.

Definition empty_context: context := fun _ => None.

Definition context_update (Gamma : context) (x : string) (T : ty) :=
  fun x' => if string_dec x x' then Some T else Gamma x'.

Notation "x '|->' T ';' Gamma" := (context_update Gamma x T)
  (at level 100, T at next level, right associativity).

Definition state_ty := list ty.

Fixpoint addr_ty (ST: state_ty) (p: addr): option ty :=
  match ST, p with
  | T :: _, O => Some T
  | _ :: ST', S p' => addr_ty ST' p'
  | _, _ => None
  end.
```
现在的类型系统还要针对程序状态上的类型进行定义
```Coq
Inductive has_type: context -> state_ty -> tm -> ty -> Prop :=
  | T_var : forall Gamma ST x T,
      Gamma x = Some T ->
      has_type Gamma ST (var x) T
  | T_abs : forall Gamma ST x T11 T12 t12,
      has_type (x |-> T11 ; Gamma) ST t12 T12 ->
      has_type Gamma ST (abs x t12) (T11 ~> T12)
  | T_app : forall T11 T12 Gamma ST t1 t2,
      has_type Gamma ST t1 (T11 ~> T12) ->
      has_type Gamma ST t2 T11 ->
      has_type Gamma ST (app t1 t2) T12
  | T_con : forall T Gamma ST c,
      const_type ST c T ->
      has_type Gamma ST (con c) T
.
```

额外定义以下算子、常量类型
```Coq
Inductive op_type: op -> ty -> Prop :=
  | OT_plus: op_type Oplus (TInt ~> TInt ~> TInt)
  | OT_minus: op_type Ominus (TInt ~> TInt ~> TInt)
  | OT_mult: op_type Omult (TInt ~> TInt ~> TInt)
  | OT_eq: op_type Oeq (TInt ~> TInt ~> TBool)
  | OT_le: op_type Ole (TInt ~> TInt ~> TBool)
  | OT_not: op_type Onot (TBool ~> TBool)
  | OT_and: op_type Oand (TBool ~> TBool ~> TBool)
  | OT_if: forall T, op_type Oifthenelse (TBool ~> T ~> T ~> T)
  | OT_read: forall T, op_type Oread (TRef T ~> T)
  | OT_write: forall T, op_type Owrite (TRef T ~> T ~> TUnit)
  | OT_alloc: forall T, op_type Oalloc (T ~> TRef T)
.

Inductive const_type: state_ty -> constant -> ty -> Prop :=
  | CT_int: forall n ST, const_type ST (int_const n) TInt
  | CT_bool: forall b ST, const_type ST (bool_const b) TBool
  | CT_op: forall o ST T, op_type o T -> const_type ST (op_const o) T
  | CT_addr: forall p ST T,
      addr_ty ST p = Some T -> const_type ST (addr_const p) T
.
```

在当前定义下，这个类型系统是具有progress和preservation性质的。
why？关键在于我们借助了程序状态类型list，把一个表达式类型和程序状态联系起来了。
