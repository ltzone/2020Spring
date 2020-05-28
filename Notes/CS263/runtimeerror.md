---
title: 【Programming Language】Run Time Error
url: pl-runtimeerror
date: 2020-05-14 08:01:38
tags: 
- Programming Language

categories: 
- Courses

---

Week 12 of 2020 Spring

<!--more-->

[toc]

## Review: Control Flow

Control Flow：
指称语义：改为起始状态、终止状态、终止类型的三元关系。
霍尔逻辑：后条件改为三个不同终止状态应满足的后条件。
小步语义：Virtul Loop or Control Stack


## Run Time Error in Expression Evaluation

```Coq
Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <-- New *)
```

原本：一个整数表达式的语义是从程序状态到整数值的映射。
现在：可能在计算过程中产生运行时错误——借助`option` Type定义。

### Denotation as Function

We can use`Some` cases of `option` types to represent "defined" and use
`None` cases of `option` types to represent "undefined".

```Coq
Definition add {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 => Some (v1 + v2)
    | _, _ => None
    end.
```

```Coq
Definition div {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 =>
        if Z.eq_dec v2 0
        then None
        else Some (v1 / v2)
    | _, _ => None
    end.
```

### Rule-based Definition

Another reasonable formalization is to define the denotation relationally. In other words, we would use `aeval a st v` as a proposition to say that the evaluation of `a` is `v` on program state `st`.


```Coq
Inductive aeval : aexp -> state -> Z -> Prop :=
  | E_ANum n st:
      aeval (ANum n) st n
  | E_AId X st:
      aeval (AId X) st (st X)
  | E_APlus (e1 e2: aexp) (n1 n2: Z) st
      (H1 : aeval e1 st n1) (* 可以合法求值 *)
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
```

### 32-bit Evaluation
In principle, both definitions make sense here. But the relational version is more flexible in adding side conditions. Here is another example.

```Coq
Inductive signed32_eval: aexp -> state -> Z -> Prop :=
  ...
  | E32_ADiv a1 a2 st v1 v2
      (H1: signed32_eval a1 st v1)
      (H2: signed32_eval a2 st v2)
      (H3: v2 <> 0)
      (H4: v2 <> -1 \/ v1 <> min32):
      signed32_eval (ADiv a1 a2) st (v1 / v2).
```

### Summary

In summary, if we use option types to formalize expressions' denotations:
- `aeval a st = Some v` when evaluation succeeds;
- `aeval a st = None` when evaluation fails.
If we use relations to formaliza expressions' denotations:
- `aeval a st v` when evaluation succeeds;
- there is no `v` such that `aeval a st v` when evaluation fails.


## Small-Steps Semantics

```Coq
Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astep : state -> aexp -> aexp -> Prop :=
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
        (ADiv (ANum n1) (ANum n2)) (ANum (n1 / n2))
.
```

Notice that there are two situations that no further evaluation step can
happen.
- Evaluation terminates.
- Evaluation arrives at an error state.

通常来说，定义了小步关系后，我们就可以定义多步关系。对之前的定义，我们能写出小步语义和指称语义的对应关系：`aeval a st = n <-> multi_astep st a (ANum n)`.

现在，对我们新设定的程序语义，求值过程合法的情况`aeval a st = Some n <-> multi_astep st a (ANum n)`. 和**求值过程不合法的情况** `aeval a st = Some n <-> ~ exists n, multi_astep st a (ANum n)` (简单：不存在任何正常的终止状态)

有时候，我们也可以说确实到达了一个error state， 首先定义一个错误状态：`Error st a = ~ aexp_halt a /\ (~ exists a', astep st a a')`.


`aeval a st = None<-> exists a', multi_astep st a a' /\ Error st a'`.


### Boolean Expressions

现在不再是两种情况，多了ERROR状态，因此我们不再用`Prop`定义bexp，而是使用`state -> bool -> Prop`

For boolean expressions' denotations, we use Coq's `bool` type in a
relational definition.

The small step semantics of bexp is not interesting at all. Although run time error may occur inside internal integer expression's evaluation, we just need to copy-paste our original small step definition for bexp.

由于整数表达式的error state是即不能进一步化简，也没有到达终止状态，因此在布尔表达式对应的小步中也不能进一步化简，error state得到了传递。

## Original Commands

下面我们刻画程序语句的指称和小步语义。

### Denotational Semantics

Intuitively，我们可以定义这样的语义：

- `ceval c st1 st2` when executing `c` from state `st1` is safe and will terminate in program state `st2`;
- there is no `st2` such that `ceval c st1 st2` when executing `c` from  state `st1` will cause run time error.
但这样的定义无法区分不终止的运行和出错的运行。

我们同样引入`None`标记Error

- `ceval c st1 (Some st2)` when executing `c` from state `st1` is safe
  and will terminate in program state `st2`;

- `ceval c st1 None` when executing `c` from state `st1` will cause run
  time error;

- there is no way that ` ceval c st1 _ ` may hold when executing `c` from
  state `st1` is safe but will not terminate.


在这一设定下，我们可以开始如下定义（rule-based）：
```Coq
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
      (H1: beval b st true)                          (* must be valid *)
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
```


### Small Step Semantics

小步语义不存在死循环的状态，因此可以按照原来的形式写出。这是因为cstep基于的astep和bstep已经发生了变化，当出现Error时，cstep所基于的astep无法执行化简。当astep到达error state时，整个c语句也就无法继续化简了。


Using multi-step relation, we can classify different execution traces:

- 安全运行并正常终止：`multi_cstep (c, st1) (CSkip, st2)`, if executing `c` from state `st1` is safe and will terminate in program state `st2`;

- 执行到某个状态出现运行时错误 `multi_cstep (c, st1) (c', st')` and there is no `c''` and `st''` such that `cstep (c', st') (c'', st'')`, if executing `c` from state `st1` will cause run time error;

- for any `c'` and `st'`, if `multi_cstep (c, st1) (c', st')` then there exists `c''` and `st''` such that `cstep (c', st') (c'', st'')` -- this condition tells that executing `c` from state `st1` is safe but will not terminate.


## Nondeterminism

小步语义和指称语义都可以定义非确定性程序的语义，特别是当我们用关系定义时。

```Coq
Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CChoice (c1 c2: com).                     (* <-- new *)
```


```Coq
Inductive ceval : com -> state -> option state -> Prop :=
  | E_ChoiceLeft st o c1 c2                        (* <-- new *)
      (H1: ceval c1 st o):
      ceval (CChoice c1 c2) st o
  | E_ChoiceRight st o c1 c2                       (* <-- new *)
      (H1: ceval c2 st o):
      ceval (CChoice c1 c2) st o.
  | E_SeqSafe c1 c2 st st' o
      (H1: ceval c1 st (Some st'))
      (H2: ceval c2 st' o):
      ceval (CSeq c1 c2) st o
  | E_SeqCrush c1 c2 st
      (H1: ceval c1 st None):
      ceval (CSeq c1 c2) st None
```
现在一个程序在一个程序状态上运行可能有多种结果，可能正常，可能error，因此在顺序执行方面，现在的语义是：若c1**可能**正常运行，那么顺序执行**可能**正常运行。如果c1**可能**运行时错误错误，那么顺序执行**可能**产生运行时错误。

但这不是一个理想的定义，因为这种定义无法说明程序是否**可能不终止**。只能说确定不终止的情况。但如果我们再用小步语义，可以做更细致的分类。

小步语义在原有定义的基础上加上了下面两条。

```Coq
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_CChoiceLeft st c1 c2:
      cstep (CChoice c1 c2, st) (c1, st)
  | CS_CChoiceRight st c1 c2:
      cstep (CChoice c1 c2, st) (c2, st).
```

当然，含义依然变了，这里的二元关系描述的是一个可能的二元关系。这种情况下，虽然程序运行的可能是树状的，但我们依然可以定义自反传递闭包，也同样可以用上面的三种情况描述正常、运行时错误、和可能不终止。

实际中，语言标准中有很多非确定性的规范，如加法二元计算的先后顺序，函数执行的先后等，但我们也能在程序语言理论中引入Choice。


## Hoare Logic

修改霍尔三元组的含义：

Originally, we use a Hoare triple  `{{ P }}  c  {{ Q }}`  to claim: if command `c` is started in a state satisfying assertion `P`, and if `c` eventually terminates, then the ending state will satisfy assertion `Q`. Now, since run-time-error and nondeterminism are taken into consideration, we modify its meaning as follows:
> If command `c` is started in a state satisfying assertion `P`, its execution is always safe. In addition, if it terminates, the ending state should satisfy `Q`.
There are two key points in this statement. 
1. As long as the precondition holds, the execution is run-time-error free, no matter what choices are made at every nondeterministic point. 2. As long as the precondition holds and the execution terminates, the ending state satisfies the postcondition, no matter what choices are made at every nondeterministic point.

### Unchanged

```Coq
Axiom hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1;;c2 {{R}}.

Axiom hoare_skip : forall P,
  {{P}} Skip {{P}}.

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.
```

语义checked。

### Changed

如果在不safe的情况下`{{P AND [[b]]}}`，是未定义的，在技术实现上可以evaluate到任意真值。下面的写法可以根据实际需要做格式上的变化。Safe的含义是evaluate的过程中不会产生运行时错误。

```Coq
Axiom hoare_if : forall P Q b c1 c2,
  {{ P AND {[b]} }} c1 {{ Q }} ->
  {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  {{ P AND Safe(b) }} If b Then c1 Else c2 EndIf {{ Q }}.

Axiom hoare_while : forall P b c,
  P |-- Safe(b) ->
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

Axiom hoare_while' : forall P b c,
  {{ P AND {[b]} }} c {{P AND Safe(b)}} ->
  {{P AND Safe(b)}} While b Do c EndWhile {{ P AND NOT {[b]} }}.


Axiom hoare_asgn_fwd : forall P (X: var) E,
  {{ P AND Safe(E) }}
      X ::= E
  {{ EXISTS x, P [X |-> x] AND
               {[X]} == {[ E [X |-> x] ]} }}.

Axiom hoare_asgn_bwd : forall P (X: var) E,
  {{ P [ X |-> E] AND Safe(E) }} X ::= E {{ P }}.
```


## Type Safe Language

在C语言中，空指针、内存管理、并发数据访问冲突常常会使用户写出运行时错误。后来的程序语言中，有希望在语言层面尽量避免这样的错误的设计思想。

类型安全语言：如果一个程序在编译阶段类型都是正确的，就不会产生运行时错误，（对算数另外规定）

下面用一个简单的小例子介绍类型安全的概念。

这里只探讨表达式的求值，考虑如下混合表达式。


### Definitions

```Coq
Definition var: Type := nat.

Definition state: Type := var -> Z.

Open Scope Z.

Inductive mexp : Type :=
  | MNum (n : Z)
  | MId (X : var)
  | MPlus (a1 a2 : mexp)
  | MMinus (a1 a2 : mexp)
  | MMult (a1 a2 : mexp)
  | MTrue
  | MFalse
  | MEq (a1 a2 : mexp)
  | MLe (a1 a2 : mexp)
  | MNot (b : mexp)
  | MAnd (b1 b2 : mexp)
.
```

Extra Assumptions
- boolean values will be cast to 0 and 1 when necessary;
- integers cannot be treated as booleans.


变量的值：
```Coq
Inductive val: Type :=
| Vint (n: Z)
| Vbool (b: bool).

Definition val2Z (v: val): Z :=
  match v with
  | Vint n => n
  | Vbool true => 1
  | Vbool false => 0
  end.
```

### Denotations

eval函数
```Coq
Inductive meval : mexp -> state -> val -> Prop :=
  | E_MNum n st:
      meval (MNum n) st (Vint n)
  | E_MId X st:
      meval (MId X) st (Vint (st X))
  | E_MPlus (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2) :
      meval (MPlus e1 e2) st (Vint (val2Z v1 + val2Z v2))
  | E_MMinus (e1 e2: mexp) (v1 v2: val) st  (* 分别计算成整数值 *)
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2) :
      meval (MMinus e1 e2) st (Vint (val2Z v1 - val2Z v2))
  | E_MMult (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2) :
      meval (MMult e1 e2) st (Vint (val2Z v1 * val2Z v2))
  | E_MTrue st:
      meval MTrue st (Vbool true)
  | E_MFalse st:
      meval MFalse st (Vbool false)
  | E_MEqTrue (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 = val2Z v2) :
      meval (MEq e1 e2) st (Vbool true)
  | E_MEqFalse (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 <> val2Z v2) :
      meval (MEq e1 e2) st (Vbool false)
  | E_MLeTrue (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 < val2Z v2) :
      meval (MLe e1 e2) st (Vbool true)
  | E_MLeFalse (e1 e2: mexp) (v1 v2: val) st
      (H1 : meval e1 st v1)
      (H2 : meval e2 st v2)
      (H3 : val2Z v1 >= val2Z v2) :
      meval (MLe e1 e2) st (Vbool false)
  | E_MNot (e: mexp) (b: bool) st
      (H1 : meval e st (Vbool b)):
      meval (MNot e) st (Vbool (negb b))
  | E_MAnd (e1 e2: mexp) (b1 b2: bool) st
      (H1 : meval e1 st (Vbool b1))
      (H2 : meval e2 st (Vbool b2)):
      meval (MAnd e1 e2) st (Vbool (andb b1 b2))
      .
```

由于指称语义要描述正常终止、运行时错误终止、不终止，甚至非确定性，因此很多情况下不适用于类型安全的描述，我们通常采用小步语义。

### Small Steps


Auxiliary Definitions: casting-step。
```Coq
Inductive mexp_halt: mexp -> Prop :=
  | MH_num : forall n, mexp_halt (MNum n)
  | MH_true: mexp_halt MTrue
  | MH_false: mexp_halt MFalse.

Inductive bool2Z_step: mexp -> mexp -> Prop :=
  | BZS_True: bool2Z_step MTrue (MNum 1)
  | BZS_False: bool2Z_step MFalse (MNum 0).
```
```Coq
Inductive mstep : state -> mexp -> mexp -> Prop :=
  | MS_Id : forall st X,
      mstep st
        (MId X) (MNum (st X))

  | MS_Plus1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MPlus a1 a2) (MPlus a1' a2)
  | MS_Plus2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MPlus a1 a2) (MPlus a1 a2')
  | MS_Plus3 : forall st a1 a1' a2,       (* <-- new casting step *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MPlus a1 a2) (MPlus a1' a2)
  | MS_Plus4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MPlus (MNum n1) a2) (MPlus (MNum n1) a2')
  | MS_Plus : forall st n1 n2,
      mstep st
        (MPlus (MNum n1) (MNum n2)) (MNum (n1 + n2))

  | MS_Minus1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MMinus a1 a2) (MMinus a1' a2)
  | MS_Minus2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MMinus a1 a2) (MMinus a1 a2')
  | MS_Minus3 : forall st a1 a1' a2,                   (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MMinus a1 a2) (MMinus a1' a2)
  | MS_Minus4 : forall st n1 a2 a2',                   (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MMinus (MNum n1) a2) (MMinus (MNum n1) a2')
  | MS_Minus : forall st n1 n2,
      mstep st
        (MMinus (MNum n1) (MNum n2)) (MNum (n1 - n2))

  | MS_Mult1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MMult a1 a2) (MMult a1' a2)
  | MS_Mult2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MMult a1 a2) (MMult a1 a2')
  | MS_Mult3 : forall st a1 a1' a2,                    (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MMult a1 a2) (MMult a1' a2)
  | MS_Mult4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MMult (MNum n1) a2) (MMult (MNum n1) a2')
  | MS_Mult : forall st n1 n2,
      mstep st
        (MMult (MNum n1) (MNum n2)) (MNum (n1 * n2))

  | MS_Eq1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MEq a1 a2) (MEq a1' a2)
  | MS_Eq2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MEq a1 a2) (MEq a1 a2')
  | MS_Eq3 : forall st a1 a1' a2,                    (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MEq a1 a2) (MEq a1' a2)
  | MS_Eq4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MEq (MNum n1) a2) (MEq (MNum n1) a2')
  | MS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      mstep st
        (MEq (MNum n1) (MNum n2)) MTrue
  | MS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      mstep st
        (MEq (MNum n1) (MNum n2)) MFalse

  | MS_Le1 : forall st a1 a1' a2,
      mstep st
        a1 a1' ->
      mstep st
        (MLe a1 a2) (MLe a1' a2)
  | MS_Le2 : forall st a1 a2 a2',
      mexp_halt a1 ->
      mstep st
        a2 a2' ->
      mstep st
        (MLe a1 a2) (MLe a1 a2')
  | MS_Le3 : forall st a1 a1' a2,                    (* <-- new *)
      mexp_halt a2 ->
      bool2Z_step a1 a1' ->
      mstep st
        (MLe a1 a2) (MLe a1' a2)
  | MS_Le4 : forall st n1 a2 a2',                    (* <-- new *)
      bool2Z_step a2 a2' ->
      mstep st
        (MLe (MNum n1) a2) (MLe (MNum n1) a2')
  | MS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      mstep st
        (MLe (MNum n1) (MNum n2)) MTrue
  | MS_Le_False : forall st n1 n2,
      n1 > n2 ->
      mstep st
        (MLe (MNum n1) (MNum n2)) MFalse

  | MS_NotStep : forall st b1 b1',
      mstep st
        b1 b1' ->
      mstep st
        (MNot b1) (MNot b1')
  | MS_NotTrue : forall st,
      mstep st
        (MNot MTrue) MFalse
  | MS_NotFalse : forall st,
      mstep st
        (MNot MFalse) MTrue

  | MS_AndStep : forall st b1 b1' b2,  (* 短路求值的版本 *)
      mstep st
        b1 b1' ->
      mstep st
       (MAnd b1 b2) (MAnd b1' b2)
  | MS_AndTrue : forall st b,
      mstep st
       (MAnd MTrue b) b
  | MS_AndFalse : forall st b,
      mstep st
       (MAnd MFalse b) MFalse.
```


到目前为止，我们没有引入新的东西，只是根据新的表达式格式定义了语义。

注意，我们引入了一类新的运行时错误——类型错误。`S + (X == Y)`是永远合法的，但`X && (X == 0)`是不合法的。这里的运行时错误完全是由类型错误造成的（上一次的运行时错误是除数为零造成的）。因此，我们完全可以在编译阶段（根据语法树，判断表达式的类型）进行消除。


### Type-Checking

```Coq
Inductive type_check_result:Type :=
| TCR_int
| TCR_bool
| TCR_illegal.
```

```Coq
Fixpoint type_check (m: mexp): type_check_result :=
  match m with
  | MNum _
  | MId _          =>

        TCR_int

  | MPlus m1 m2
  | MMinus m1 m2
  | MMult m1 m2    =>

        match type_check m1, type_check m2 with
        | TCR_illegal, _ => TCR_illegal
        | _, TCR_illegal => TCR_illegal
        | _, _           => TCR_int
        end

  | MTrue
  | MFalse         =>

        TCR_bool

  | MEq m1 m2
  | MLe m1 m2      =>

        match type_check m1, type_check m2 with
        | TCR_illegal, _ => TCR_illegal
        | _, TCR_illegal => TCR_illegal
        | _, _           => TCR_bool
        end

  | MNot m1        =>

        match type_check m1 with
        | TCR_bool => TCR_bool
        | _        => TCR_illegal
        end

  | MAnd m1 m2     =>

        match type_check m1, type_check m2 with
        | TCR_bool, TCR_bool => TCR_bool
        | _, _               => TCR_illegal
        end

  end
.
```

我们想要的结果：对任何表达式，如果类型检查结果是int或bool，它能合法完成求值，如果是illega，它不能合法完成求值。
只要类型检查结果（编译阶段）是合法，那么一个表达式就是类型安全的。

- JAVA通过去除指针，避免悬空指针的状态。
- 函数式语言通过类型消除了函数指针的运行时错误
- Rust进行了更加激进的类型设定，但思想上还是在沿类型安全往前推进


## Progress

How to justify that every mexp expression that passes type_check is safe to evaluate? There are two important theorems: progress and preservation.
> "Progress" says every mexp that passes type_check will either take a step to evaluate or is already a constant.


```Coq
Lemma mexp_halt_fact: forall m,
  mexp_halt m ->
  exists n, bool2Z_step m (MNum n) \/ m = MNum n.


Lemma mexp_halt_bool_fact: forall m,
  mexp_halt m ->
  type_check m = TCR_bool ->
  m = MTrue \/ m = MFalse.

Theorem Progress: forall m st,
  type_check m <> TCR_illegal ->
  (exists m', mstep st m m') \/ mexp_halt m.
```

- 常数，OK，halt
- 表达式，下一步(MNum (st X))
- 加法表达式 `H: type_check (MPlus m1 m2) <> illegal`
  - 先证明`m1`,`m2`必须合法。反证，若illegal，代入H，推出矛盾。
  - 可以用归纳假设，`exists m1', m1 --> m1' \/ halt m1`, `exists m2', m2 --> m2' \/ halt m2`.
  - 对结论，一定是下一步走的分支，不可能illegal。下面分四种情况，用对应的规则构造小步语义。omitted
  - 对bool的cast情况，应用`mexp_halt_fact`引理。
- 类似可证减法、乘法等情况


## Preservation

> "Preservation" says: if an mexp type checks then it will only step to type-checked another expression.
小步语义走一步，走之前合法，走之后则合法。证明一个更强的结论：小步语义执行一步，走之前与走之后的类型检查结果一致。

```Coq
Lemma bool2Z_step_fact: forall m1 m2,
  bool2Z_step m1 m2 ->
  type_check m1 = TCR_bool /\ type_check m2 = TCR_int.
Proof.
  intros.
  inversion H; subst.
  + split; reflexivity.
  + split; reflexivity.
Qed.

Lemma Preservation_aux: forall st m1 m2,
  mstep st m1 m2 ->
  type_check m1 <> TCR_illegal ->
  type_check m1 = type_check m2.
```

**Proof.**

思路1：为什么`m1 --> m2`，对小步做归纳证明，在这种情况下讨论`m1`是否合法。

思路2：`m1`是什么，对`m1`做归纳证明。

只需类似的，从`type_check (MPlus a1 a2) <> illegal`推出`type_check a1 <> illegal`和`type_check a2 <> illegal`即可。

