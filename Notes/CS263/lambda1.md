---
title: 【Programming Language】Lambda Calculus
url: pl-lambda1
date: 2020-05-26 14:02:23
tags: 
- Programming Language

categories: 
- Courses

---

Week 14 of 2020 Spring.

<!--more-->

[toc]

## Lambda Expressions

### CPP lambda
```Cpp
#include <functional>
#include <iostream>
/*function<A(B)> : B -> A 函数对象*/
template <typename T>
std::function<T(T)> do_it_three_times (std::function<T(T)> f) {
    return [f](T x) { return f(f(f(x))); };
}
/* [f] T x { ... };
 ~ fun x:T => ... 
 方括号中指的是函数运行过程中用到的参数x以外的东西。
 */
```

同样用lambda表达式定义如下函数（add_one,square)
```cpp
int main() {
    std::function<int(int)> add_one = [](int x) {return x + 1; };
    std::function<int(int)> square = [](int x) {return x * x; };
    std::cout << do_it_three_times (add_one) (1);
    std::cout << std::endl;
    std::cout << do_it_three_times (square) (2);
    std::cout << std::endl;
    std::cout << do_it_three_times (do_it_three_times(add_one)) (0);
    std::cout << std::endl;
    // The following line does not work for C++,
    // because do_it_three_times is a function not an object
    // std::cout << do_it_three_times (do_it_three_times) (add_one) (0);
    std::function<std::function<int(int)>(std::function<int(int)>)>
      do_it_three_times_obj =
      [](std::function<int(int)> f) {return do_it_three_times (f); };
    std::cout << do_it_three_times (do_it_three_times_obj) (add_one) (0);
    /* 函数作用在参数obj/add_one上，形成一个新的函数 */
    std::cout << std::endl;
}
```




算子可以定义为常数，也可以不定义为常数。算子本质上也是值（函数）。
```Coq
Inductive op : Type :=
  | Oplus
  | Ominus
  | Omult
  | Oeq
  | Ole
  | Onot
  | Oand
  | Oifthenelse.

Inductive constant : Type :=
  | int_const (n: Z): constant
  | bool_const (b: bool): constant
  | op_const (o: op): constant.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> tm -> tm
  | con : constant -> tm.
```

## Operational Semantics

It is critical to see that lambda-calculus does not simply define math functions and values. It also defines how to compute. Lambda虽然也有对应的霍尔逻辑、指称语义（颗粒度较大），但也比较复杂，本课程主要讨论小步语义。


```
(lambda x: x*x + x + 1) 1
-> 1*1 + 1 + 1
-> 1 + 1 + 1
-> ... -> 3

(lambda x: x*x + x + 1) 1
-> (lambda x: 1*x + x + 1) 1
-> (lambda x: 1*1 + x + 1) 1
-> (lambda x: 1 + x + 1) 1
-> (lambda x: 1 + 1 + 1) 1
-> (lambda x: 3) 1
-> 3
```

实际编程语言中，我们通常采用第一种reduction。`[ app (abs x t1) t2 --> t1 [x |-> t2] ].`

- CBV 先化简再代入，C++,Python，OCaml
- CBN 先代入再化简，Haskell

化简方式对结果有区别吗？就我们目前定义的语法树而言，不同的化简结果不会产生区别。（算子没有副作用）

1. 先化简函数部分，再化简参数部分
2. 函数已经化简完了（到abs格式/算子常量），并且参数部分应该被化简（如短路求值），化简参数部分
3. 都完成化简，按照算子的含义进行化简
4. 如果函数部分完成化简，参数部分不需化简，则也进行替换。

```Coq
Notation "t [ x |-> s ]" := (subst x s t) (at level 10, x at next level).

Inductive step: tm -> tm -> Prop :=
  | S_base: forall t t',  (* 应该化简的情况，常数的加减等 *)
              base_step t t' -> step t t'
  | S_beta: forall x t1 t2,
              tm_halt t2 -> step (app (abs x t1) t2) (t1 [ x |-> t2])
  | S_app1: forall t1 t1' t2,
              step t1 t1' -> step (app t1 t2) (app t1' t2)
  | S_app2: forall t1 t2 t2',
              tm_pend t1 -> step t2 t2' -> step (app t1 t2) (app t1 t2')
.
```

一项化简完了：
```Coq
Inductive tm_base_halt: tm -> Prop :=
  | BH_plus: forall n: Z, tm_base_halt (app Oplus n)
  | BH_minus: forall n: Z, tm_base_halt (app Ominus n)
  | BH_mult: forall n: Z, tm_base_halt (app Omult n)
  | BH_eq: forall n: Z, tm_base_halt (app Oeq n)
  | BH_le: forall n: Z, tm_base_halt (app Ole n)
  | BH_and: forall b: bool, tm_base_halt (app Oand b)
  | BH_if1: forall b: bool, tm_base_halt (app Oifthenelse b)
  | BH_if2: forall (b: bool) (t: tm), tm_base_halt (app (app Oifthenelse b) t).
    (* 注意t是tm，表明我们会根据bool选择化简的方向 *)

Inductive tm_halt: tm -> Prop :=
  | H_abs: forall x t, tm_halt (abs x t)
  | H_con: forall c, tm_halt (con c)
  | H_base: forall t, tm_base_halt t -> tm_halt t.
```

希望下一项要化简：
```Coq
Inductive tm_pend: tm -> Prop :=
  | P_abs: forall x t, tm_pend (abs x t)
  | P_con: forall c, tm_pend (con c)
  | P_base: forall t, tm_base_pend t -> tm_pend t.

Inductive tm_base_pend: tm -> Prop :=
  | BP_plus: forall n: Z, tm_base_pend (app Oplus n)
  | BP_minus: forall n: Z, tm_base_pend (app Ominus n)
  | BP_mult: forall n: Z, tm_base_pend (app Omult n)
  | BP_eq: forall n: Z, tm_base_pend (app Oeq n)
  | BP_le: forall n: Z, tm_base_pend (app Ole n)
  | BP_and_true: tm_base_pend (app Oand true). (* 短路求值 *)
```

根据基础类型规定的化简：
```Coq
Inductive base_step: tm -> tm -> Prop :=
  | BS_plus: forall n1 n2: Z, base_step (app (app Oplus n1) n2) (n1 + n2)
  | BS_minus: forall n1 n2: Z, base_step (app (app Ominus n1) n2) (n1 - n2)
  | BS_mult: forall n1 n2: Z, base_step (app (app Omult n1) n2) (n1 * n2)
  | BS_eq_true: forall n1 n2: Z,
                  n1 = n2 -> base_step (app (app Oeq n1) n2) (true)
  | BS_eq_false: forall n1 n2: Z,
                  n1 <> n2 -> base_step (app (app Oeq n1) n2) (false)
  | BS_le_true: forall n1 n2: Z,
                  n1 <= n2 -> base_step (app (app Ole n1) n2) (true)
  | BS_le_false: forall n1 n2: Z,
                  n1 > n2 -> base_step (app (app Ole n1) n2) (false)
  | BS_not: forall b: bool, base_step (app Onot b) (negb b)
  | BS_and_true: forall b: bool, base_step (app (app Oand true) b) b
  | BS_and_false: forall t: tm, base_step (app (app Oand false) t) false (* 短路求值 *)
  | BS_if_true: forall t1 t2: tm, (* 先转化，再化简 *)
                  base_step (app (app (app Oifthenelse true) t1) t2) t1
  | BS_if_false: forall t1 t2: tm,
                  base_step (app (app (app Oifthenelse false) t1) t2) t2
.
```



## Goal
加上类型理论，确保不存在runtime error。

引入类型系统：

```Coq
Inductive ty : Type :=
  | TBool : ty
  | TInt : ty
  | TArrow : ty -> ty -> ty.

Notation "T1 ~> T2" := (TArrow T1 T2) (right associativity, at level 30).
```

首先给出基本常数的类型，算子的类型：
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
  (* 没有固定的类型，对应任意的类型T *)
.

Inductive const_type: constant -> ty -> Prop :=
  | CT_int: forall n, const_type (int_const n) TInt
  | CT_bool: forall b, const_type (bool_const b) TBool
  | CT_op: forall o T, op_type o T -> const_type (op_const o) T
.
```

注意：一个lambda表达式中存在变量，不同的变量会具有不同的意思，当我们探讨一个lambda表达式的类型时，我们会引入类型环境的概念(context)。

```Coq
Definition context := string -> option ty.

Definition empty_context: context := fun _ => None.

Definition context_update (Gamma : context) (x : string) (T : ty) :=
  fun x' => if string_dec x x' then Some T else Gamma x'.

Notation "x '|->' T ';' Gamma" := (context_update Gamma x T)
  (at level 100, T at next level, right associativity).

Inductive has_type: context -> tm -> ty -> Prop :=
  | T_var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (var x) T
  | T_abs : forall Gamma x T11 T12 t12,
      has_type (x |-> T11 ; Gamma) t12 T12 ->
      has_type Gamma (abs x t12) (T11 ~> T12)
  | T_app : forall T11 T12 Gamma t1 t2,
      has_type Gamma t1 (T11 ~> T12) ->
      has_type Gamma t2 T11 ->
      has_type Gamma (app t1 t2) T12
  | T_con : forall T Gamma c,
      const_type c T ->  (* 关注if-then-else的情况 *)
      has_type Gamma (con c) T
.

Notation "Gamma '|-' t '\in' T" := (has_type Gamma t T) (at level 40).
```

下面我们会利用现有的类型定义证明progress和preservation。