---
title: 【Programming Language】Pointer And Address
url: pl-pointer
date: 2020-05-21 08:06:23
tags: 
- Programming Language

categories: 
- Courses

---

Week 13 of 2020 Spring


<!--more-->

[toc]

## A Language With Addresses And Pointers

In this lecture, we consider a typical programming language, extending the simple imperative language with addresses (地址) and pointers (指针). We still use their indices to represent variables and add two operators to the programming language: dereference and address-of.

Dereferece is like the "*" operator in C, e.g. `x = * y`; . Address-of is like the "&" operator in C, e.g. `y = & x`.

```Coq
Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADeref (a1: aexp)            (* <-- new *)
  | AAddr (a1: aexp).            (* <-- new *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAss (a1 a2 : aexp)          (* <-- new *)
  (* 不仅可以给变量赋值，还可以给某个地址上的值赋值，整数类型表达式a1表达了地址 *)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
```


这带来的问题，赋值语句如何描述？赋值符号左边的表达式，光说出它的值时没有用的，我们还要确定它是一个变量/地址。注意，不是所有整数表达式都是地址/变量，如`(AId X) + 1`
```
Example com_sample1: com :=
  CAss (ADeref (AId X)) (APlus (ADeref (AId X)) (ANum 1)).
  (* It is like the C program: [ ( * x ) ++; ]. *)
```
In order to define a denotational semantics, we define two functions for expression evaluation: `aevalR` and `aevalL`. They define expressions' rvalue (右值) and lvalue (左值). Rvalues are the values for computation and lvalues are the addresses for reading and writing. We introduce aevalR and aevalL by a mutually inductive definition.

首先引入什么是程序状态：
```Coq
Definition var2addr (X: var): Z := Z.of_nat X + 1.

Definition state: Type := Z -> option Z.
```
我们要求第n号程序变量，对应地址在n+1上。0可以认为是空地址。程序状态是地址到值的部分函数。


```Coq
Inductive aevalR : aexp -> state -> Z -> Prop := (* 表达式的值 *)
  (* 若出现运行时错误，则在该aexp上没有三元组成立 *)
  | E_ANum n st:
      aevalR (ANum n) st n
  | E_AId X st n:
      st (var2addr X) = Some n -> （* 变量的值就是它对应地址上的值*）
      aevalR (AId X) st n
  | E_APlus (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2) :
      aevalR (APlus e1 e2) st (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2) :
      aevalR (AMinus e1 e2) st (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aevalR e1 st n1)
      (H2 : aevalR e2 st n2) :
      aevalR (AMult e1 e2) st (n1 * n2)
  | E_ADeref (e1: aexp) (n1 n2: Z) st  (* <--- new *)
      (H1 : aevalR e1 st n1)
      (H2 : st n1 = Some n2) :
      aevalR (ADeref e1) st n2
  | E_AAddr (e1: aexp) (n1: Z) st      (* <--- new *)
      (H1 : aevalL e1 st n1):
      aevalR (AAddr e1) st n1  (* e1 表达式的RValue等于取地址前的LValue*)
      (* RValue (AAddr e1) = LValue e1 *)
with aevalL : aexp -> state -> Z -> Prop := (* 表达式的地址 *)
  | EL_AId X st:
      aevalL (AId X) st (var2addr X)
  | EL_ADeref (e1: aexp) (n1: Z) st
      (H1 : aevalR e1 st n1) :
      aevalL (ADeref e1) st n1.
      (* LValue (ADeref e1) = RValue e1 *)
```

LValue和RValue是通过Addr和Deref操作相互定义的。
- RValue (AAddr e1) = LValue e1
- LValue (ADeref e1) = RValue e1


```Coq
Inductive beval : bexp -> state -> bool -> Prop.
(* use aevalR*)
```

## Programs' Denotations

与带Runtime Error类似，顺序执行、If、While先讨论Error，再执行，与前面定义的一致。

```Coq
Inductive ceval : com -> state -> option state -> Prop :=
  | E_Skip st:
      ceval CSkip st (Some st)
  | E_AssSucc st1 st2 E E' n n'                            (* <-- new *)
      (H1: aevalL E st1 n)
      (H2: aevalR E' st1 n')
      (H3: st1 n <> None)                              (* 保证赋值合法 *)
      (H4: st2 n = Some n')                                (* 描述状态 *)
      (H5: forall n'', n <> n'' -> st1 n'' = st2 n''):     
      ceval (CAss E E') st1 (Some st2)
  | E_AssFail1 st1 E E'                                    (* <-- new *)
      (H1: forall n, ~aevalL E st1 n):
      ceval (CAss E E') st1 None
  | E_AssFail2 st1 E E'                                    (* <-- new *)
      (H1: forall n', ~aevalR E' st1 n'):
      ceval (CAss E E') st1 None
  | E_AssFail3 st1 E E' n                                  (* <-- new *)
      (H1: aevalL E st1 n)
      (H2: st1 n = None):
      ceval (CAss E E') st1 None
```

赋值语句有三种情况可能会出错，三个环节，分别对应AssFail1~3.
- 求地址，`aevalL`可能会得不到结果
- 求右值，`aevalR`可能会得不到结果
- 地址求出来了，但没有读写权限`state -> None`


## Small Step Semantics for Expression Evaluation

与指称语义类似，小步语义也要定义作为地址和作为值的化简小步。
```Coq
Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astepR : state -> aexp -> aexp -> Prop :=
  | ASR_Id : forall st X n,
      st (var2addr X) = Some n ->
      astepR st
        (AId X) (ANum n)

  | ASR_Plus1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      astepR st
        (APlus a1 a2) (APlus a1' a2)
  | ASR_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      astepR st
        (APlus a1 a2) (APlus a1 a2')
  | ASR_Plus : forall st n1 n2,
      astepR st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  (* Plus Minus Mult 与原来完全一致 *)

  | ASR_DerefStep : forall st a1 a1',
      astepR st
        a1 a1' ->
      astepR st
        (ADeref a1) (ADeref a1')
  | ASR_Deref : forall st n n',
      st n = Some n' ->
      astepR st
        (ADeref (ANum n)) (ANum n')

  | ASR_AddrStep : forall st a1 a1',
      astepL st
        a1 a1' ->         (* 注意，Addr中的化简是当做左值的化简 *)
      astepR st
        (AAddr a1) (AAddr a1')
  | ASR_Addr : forall st n,
      astepR st
        (AAddr (ADeref (ANum n))) (ANum n)
with astepL : state -> aexp -> aexp -> Prop := 
  (* 只有这两类表达式表示存储在某个地址上的值，可以进行地址求值 *)
  | ASL_Id: forall st X,
      astepL st
        (AId X) (ADeref (ANum (var2addr X)))

  | ASL_DerefStep: forall st a1 a1',
      astepR st
        a1 a1' ->         (* 注意，Deref中的化简是当做右值的化简 *)
      astepL st           (* Deref a1 是一个地址，但a1本身是值*)
        (ADeref a1) (ADeref a1')
.
```
注意，当使用ASL_DerefStep把LValue化简完后，终止状态是`(ADeref (ANum x))`，接下来就可以利用`ASR_AddrStep`化归成`RValue`的进一步化简。



```Coq
Inductive bstep : state → bexp → bexp → Prop
```

## Small Step Semantics for Program Execution

先求左值，再求右值。如果顺利求值（得到常数值），若有读写权限，赋值完成。
```Coq
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep1 st E1 E1' E2                                (* <-- new *)
      (H1: astepL st E1 E1'):
      cstep (CAss E1 E2, st) (CAss E1' E2, st)
  | CS_AssStep2 st n E2 E2'                                 (* <-- new *)
      (H1: astepR st E2 E2'):
      cstep (CAss (ADeref (ANum n)) E2, st) (CAss (ADeref (ANum n)) E2', st)
  | CS_Ass st1 st2 n1 n2                                    (* <-- new *)
      (H1: st1 n1 <> None)
      (H2: st2 n1 = Some n2)
      (H3: forall n, n1 <> n -> st1 n = st2 n):
      cstep (CAss (ADeref (ANum n1)) (ANum n2), st1) (CSkip, st2)
```


## Discussion: Type Safety

Is this programming language a safe one? Definitely no. There are several kinds of errors that may happen.
The first is illegal assignments. In the C language, `x + 1 = 0` is an illegal assignment. In our language, the corresponding syntax tree is
- `CAss (APlus (AId X) (ANum 1)) (ANum 0)`.
- 因为左边一定不是左值，因为左值一定是Deref或Var
- 同样，对取Address的左值也进行一定的判断。  

It causes error because its left hand side is not an lvalue. We do not want to call it a run-time-error because it should be detected at compile time.

The second is illegal dereferece. When we want to read or write on address n but this address is not accessible, it is a run time error. It is hard to completely get rid of this kind of errors at compile time.
- `p = p -> next`肯定不是我们希望在Compile阶段排除的，但确实不能保证在所有情况下安全运行。