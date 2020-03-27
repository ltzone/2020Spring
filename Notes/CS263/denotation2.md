---
title: 【Programming Language】 Denotational Semantics 2
url: pl-deno2
date: 2020-03-26 08:11:48
tags: 
- Programming Language

categories: 
- Courses

---

Week 4 of 2020 Spring

<!--more-->

[toc]

## Assignment

```
{{ weakest-pre of (X::E) P}}
X ::= E
{{ P }}

{{ weakest-pre of (X::E) P}}
X ::= E
{{ strongest-post of (X::E) weakest-pre of (X::E) P}}
```

An example
```
X ::= 0
P = True
{{ weakest-pre of (X::E) P}} = True
{{ strongest-post of (X::E) weakest-pre of (X::E) P}}
  = EXISTS x, True AND {[X]} = {[0]} 
```

一定是后条件较原条件更强(严格的强或等价). 注意到, 上面的霍尔三元组和下面的霍尔三元组有一样的前条件和赋值语句, 但下面的霍尔三元组specifies后条件是最强的. 所以后条件一定更强.(严格的强或等价).


## Review
判断
- `X+1`和`1+X` 不是相同的表达式
- `X+1`和`1+X` 是等价的表达式
- `X*0`和`1*X` 根据alength有相同的代价.


## Higher-Order Thinking
```Coq
Check aeval.
(* aeval : state -> aexp -> Z *)
```
两种理解, 二元函数/given 状态, 表达式到值的映射.

我们也可以这样定义
```Coq
Fixpoint aeval (a : aexp) (st : state) : Z :=
  match a with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMinus a1 a2  => (aeval a1 st) - (aeval a2 st)
  | AMult a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.
```

两种理解, 二元函数/given 表达式, 状态到值的映射.

高阶函数: 当一个函数的参数本身是函数/高阶函数时, 这个函数被称为高阶函数.
```Coq
Definition add {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a + g a.

Definition sub {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a - g a.

Definition mul {A: Type} (f g: A -> Z): A -> Z :=
  fun a => f a * g a.
```

定义了高阶函数后, 我们可以用利用函数之间的操作, 更显式的方式写出第二种形式的指称语义.

```Coq
Definition constant_func {A: Type} (c: Z): A -> Z := fun _ => c.
Definition query_var (X: var): state -> Z := fun st => st X.

Fixpoint aeval (a : aexp) : state -> Z :=
  match a with
  | ANum n => constant_func n
  | AId X => query_var X
  | APlus a1 a2 => (aeval a1 + aeval a2)%Func (* 两个指称语义函数的和 *)
  | AMinus a1 a2  => (aeval a1 - aeval a2)%Func
  | AMult a1 a2 => (aeval a1 * aeval a2)%Func
  end.
```

这样的定义与我们之前给出的有关指称语义的两种定义是等价的.

> In hand written math, we sometimes use f(x) to represent a function and sometimes use f(x) to represent a specific value: the result of applying function f to a specific value x. Moreover, we write f(x) + g(x) to represent the sum of two functions, or two values, which is usually unambiguous from context. In comparison, (f+g) is not used very often. In Coq, f x + g x is the sum of two numbers while fun x ⇒ f x + g x is the sum of two functions.


## More Higher-order Objects

### Do-it-three-times

```Coq
Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Definition minustwo (x: Z): Z := x - 2.
```

```
Goal doit3times minustwo 9 = 3.
Goal doit3times minustwo (doit3times minustwo 9) = -3.
Goal doit3times (doit3times minustwo) 9 = -9.
Goal (doit3times doit3times) minustwo 9 = -45.
(* = (doit3times (doit3times (doit3times minus2))) 9
   = (doit3times (doit3times minus6)) 9
   = minus54 9 = -45
*)
Goal doit3times (fun n => n * n) 2 = 256.
Goal doit3times (Func.add minustwo) (fun x => x * x) 4 = 22.
(* = minustwo + minustwo + minustwo + (fun x => x*x)
   = 4 - 2 + 4 - 2 + 4 - 2 + 4 * 4 *)
Goal doit3times ((fun x y => y * y - x * y + x * x) 1) 1 = 1.
```


### Computing sets from functions

we can use `A -> Prop` to represent subsets of `A`

```Coq
Definition test_eq {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a = g a.

Definition test_le {A: Type} (f g: A -> Z): A -> Prop :=
  fun a => f a <= g a.
```

除了可以由函数定义的集合, 我们还可以定义**函数之间的关系**.

```Coq
Definition equiv {A: Type} (f g: A -> Z): Prop :=
  forall a, f a = g a.

Definition le {A: Type} (f g: A -> Z): Prop :=
  forall a, f a <= g a.
```

我们还可以定义**集合之间的关系**
```Coq
Definition equiv {A: Type} (X Y: A -> Prop): Prop :=
  forall a, X a <-> Y a.
```

证明有关集合, 函数的一些性质


加法保持等价性
```Coq
Lemma Func_add_equiv_naive: forall A (f1 f2 g1 g2: A -> Z),
  Func.equiv f1 f2 ->
  Func.equiv g1 g2 ->
  Func.equiv (f1 + g1)%Func (f2 + g2)%Func.
Proof.
Abort.

(** Coq suggests you use [Proper] to describe such preservation theorems. *)

Lemma Func_add_equiv: forall A,
  Proper (@Func.equiv A ==> @Func.equiv A ==> @Func.equiv A) Func.add.
```

Why using `Proper` is better than `Func_add_equiv_naive`? Coq supports rewriting via `Proper`!

```Coq
Existing Instances Func_equiv_refl
                   Func_equiv_sym
                   Func_equiv_trans
                   Func_add_equiv
                   Func_sub_equiv
                   Func_mul_equiv.
```

我们希望说明的是: 我们可以通过高阶性质的定义和证明, 很简洁地将抽象复杂的证明直观地描述清楚.

## Evaluating Boolean Expressions

定义集合运算
```Coq
Definition full {A: Type}: A -> Prop := fun _ => True.

Definition empty {A: Type}: A -> Prop := fun _ => False.

Definition intersect {A: Type} (X Y: A -> Prop) := fun a => X a /\ Y a.

Definition complement {A: Type} (X: A -> Prop) := fun a => ~ X a.
```

Recall bexp的syntax tree `b ::= true | false | a == a | a <= a | ! b | b && b`

由此我们可以定义布尔表达式的语义

```Coq
Fixpoint beval (b : bexp) : state -> Prop :=
  match b with
  | BTrue       => Sets.full
  | BFalse      => Sets.empty
  | BEq a1 a2   => Func.test_eq (aeval a1) (aeval a2)
  | BLe a1 a2   => Func.test_le (aeval a1) (aeval a2)
  | BNot b1     => Sets.complement (beval b1)
  | BAnd b1 b2  => Sets.intersect (beval b1 ) (beval b2)
  end.
```

## Evaluating Command

下面我们进入程序语义的定义.

一种办法: 程序语义是从起始状态到终止状态的函数, 但由于程序语言存在循环, 起始状态不一定有终止状态. 所以, 通常在程序语言中, 我们用一对对程序状态的程序对来构造程序语义.

Specifically, if a program state pair `(st1, st2)` is an element of `S`, then executing `c` from state `st1` may terminate with state `st2`. In other words, the denotation of a program has type `state → state → Prop` in Coq. 

Remark: this is different from Hoare triples. Hoare triples are about assertion pairs but a program's denotation is about program state pairs. 指称语义中给出的是起始状态+终止状态. 霍尔逻辑讨论的是前条件,后条件(起始状态的集合与终止状态的集合)

我们定义一些二元关系(有序对的集合)的性质.

```Coq
Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition empty {A B: Type}: A -> B -> Prop := fun a b => False.

Definition concat {A B C: Type} (r1: A -> B -> Prop) (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

Definition filter1 {A B: Type} (f: A -> Prop): A -> B -> Prop :=
  fun a b => f a.
(* 后一个元素不影响 *)

Definition filter2 {A B: Type} (f: B -> Prop): A -> B -> Prop :=
  fun a b => f b.
(* 前一个元素不影响 *)

Definition union {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b \/ r2 a b.

Definition intersection {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b /\ r2 a b.
```

