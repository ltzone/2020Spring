---
title: 【Programming Language】Denotation VS Triples 2
url: pl-denovshoare2
date: 2020-04-16 08:15:18
tags: 
- Programming Language

categories: 
- Courses

---

Week 7 of 2020 Spring

<!--more-->

[toc]

## Review


- We use syntax trees to describe assertions. Assertions describe properties of program states and logical variables via expressions (`aexp` and `bexp`) and **terms**.

- Syntactic substitution is recursively defined. When quantifiers (forall and exists) are involved, renaming should be done beforehand. E.g. `(EXISTS x, {[X]} = 2 * x) [X |-> x] `should be `EXISTS y, {[x]} = 2 * y` instead of `EXISTS x, {[x]} = 2 * x`.

- A Hoare triple is _provable_ (可证) if we can prove it from our Hoare logic proof rules, written as `|-- {{ P }} c {{ Q }}`. In these two weeks, we will pick backward assignment rule in our proof theories.

- An _interpretation_ (解释) is a pair of _program state_ and _logical variable assignment_. When an interpretation _satisfies_ (满足) an assertion is defined by recursively on the assertion's syntax tree. We write `J |= P` if `J` satisfies `P`.

- A Hoare triple `{{ P }} c {{ Q }}` is _valid_ (有效) when for any beginning state `st1`, assignment `La` and ending state `st2`, if `(st1, La) |= P` and `(st1, st2)` is in the denotation of `c`, then `(st2, La) |= Q`, written as `|== {{ P }} c {{ Q }}`.

> Example:
> Assume st(X) = 0, st(Y) = 1; La(x) = 2.
> Consider `{{Y]} = x - 1 AND EXISTS x, {[X]} = 2 * x`
> `(st,La) |== {[Y]} = x - 1 AND EXISTS x, {[X]} = 2 * x }`
> $\iff$ `(st,La) |=={[Y]} = x - 1 ` and `(st,La) |==  EXISTS x, {[X]} = 2 * x }`
> 
> 对前半部分, 
> ```
> term_denote (st,La) ({[Y]}) = aexp'_denote (st,La) Y = st(Y) = 1
> term_denote (st,La) (x - 1) = La(x) - 1 = 1
> ```
> 
> Hence `{{Y]} = x - 1` 成立
> 
> 对后半部分
> 
> 选定`v = 0`的一个指派,
> ```
> |== (Interp_Lupdate J x 0) (EXISTS x, {[X]} = 2 * x)
> <==> term_denote (st,La') ({[X]}) = aexp'_denote (st,La) X = st(X) = 0
>    = term_denote (st,La') (2 * x) = 2 * La'(x) = 2 * 0 = 0
> ```

在大多数情况下, 我们会要求前条件下和后条件下的逻辑变量是一致的. 由于我们**问题中的指派是任意的**, 它足以用来描述霍尔三元组的性质. 大部分前后逻辑变量不一致的霍尔三元组都是无效的.

- `{{ {[X]} = m }} X::= X+1 {{ {[X]} = x }}` Fails to be valid because m and x can be arbitrary.

当然,对于有效的三元组,我们的定义也足以描述这样的性质.
- `{{ {[X]} = m }} X::= 0 {{ {[X]} = x - x }}` is valid because it holds for arbitrary m and x.



## Soundness 

We will prove Hoare logic's soundness today. Recall that a Hoare logic is
sound when all provable Hoare triples are valid.
```Coq
Definition hoare_sound (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |-- {{ P }} c {{ Q }} -> (* Inductively defined proof tree *)
    |== {{ P }} c {{ Q }}.
```

我们需要证明, Pf tree的构造依然保持"有效"这一性质.

```Coq
Lemma hoare_seq_sound : forall (P Q R: Assertion) (c1 c2: com),
  |== {{P}} c1 {{Q}} ->
  |== {{Q}} c2 {{R}} ->
  |== {{P}} c1;;c2 {{R}}.
```
**Proof.**
We should prove if `(st1, La) |== P` and `ceval (c1;;c2) st1 st3`, we should know `(st3, La) |== R`.
根据指称语义, 一定存在`st2`, 使得`ceval c1 st1 st2`, `ceval c2 st2 st3`.
那么根据`(st1, La) |== P`, `ceval c1 st1 st2` 和`H1`(对任意的指派,终止状态), 我们就可以得到`(st2,La) |== Q`.
进一步,根据`(st2,La) |== Q`, `ceval c2 st2 st3` 和`H2`的有效性, 我们就可以推出`(st3, La) |== R`.

```Coq
Lemma hoare_skip_sound : forall P,
  |== {{P}} Skip {{P}}.
```
**Proof.**
根据Skip的定义, 状态和指派这一有序对在前后条件中都是不变的, 那么自然符合相同的一个条件P.

```Coq
Lemma hoare_if_sound : forall P Q (b: bexp) c1 c2,
  |== {{ P AND {[b]} }} c1 {{ Q }} ->
  |== {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.
```
**Proof.**
H1: `|== {{ P AND {[b]} }} c1 {{ Q }}`
H2: `|== {{ P AND NOT {[b]} }} c2 {{ Q }}`
Given `(st1, La) |== P` and `(st1, st2)` is in the denotation of `If b Then c1 Else c2 EndIf`, we should prove `(st2, La) |== Q`.

Recall`ceval (If b Then c1 Else c2 EndIf)` = `union (concat (test_rel (beval b)) c1)  (concat (test_rel (beval (BNot b))) c2)`.

Case 1:
- `(st1, st2)` is in the denotation of `(concat (test_rel (beval b)) c1)`. in other words `beval b st1` and `ceval c1 st1 st2`.
- H1 is equivalent to say `forall La st1 st2, if (st1, La) |== P AND [[b]], ceval c1 st1 st2, then (st2,La) |== Q`.
- By apply H1, we just need to prove `(st1, La) |== P AND [[b]]`, which by definition is equivalent to `(st1, La) |== P` and `(st1, La) |== [[b]]`.

Case 2 follows a similar proof pattern.

```Coq
Lemma hoare_while_sound : forall P (b: bexp) c,
  |== {{ P AND {[b]} }} c {{P}} ->
  |== {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.
```
**Proof.**
H: `{{ P AND [[b]] }} c {{P}}`
Given `(st1, La) |== P`, and `ceval (While b Do c EndWhile) st1 st2`. We should prove `(st2, La) |== P AND NOT [[b]]`

Recall  `ceval (While b Do c EndWhile) st1 st2 = (iter_loop_body b (ceval c) n st1 st2)`. We perform induction on n.

Case 1 (base step): n = 0.
- `iter_loop_body b (ceval c) n = tesl_rel (beval (! b))`.
- Thus `st1 = st2, ~ beval b st1`. The result follows directly.

Case 2: n = n' + 1
- IH: forall `st1, st2`, if  `(st1, La) |= P` and `iter_loop_body (ceval c) n' st1 st2`, then `(st2, La) |== P AND NOT {[b]}` (st1,st2 here are not the same as the problem)
- Assumptions:
  - `(st1, La) |== P`
  - `iter_loop_boday b (ceval c) (n'+1) st1 st2`
- `iter_loop_body b (ceval c) (n' + 1)` =
  `concat (test_rel (beval b)) (concat (ceval c) (iter_loop_boday b (ceval c) n')`
- The definition tells us that
  - `beval b st1`
  - `ceval c st1 st`
  - `iter_loop_body b (ceval c) n' st st2`
- Using H and definition of valid we know that `(st, La) |== P`
- By IH, `(st2, La) |== P AND NOT {[b]}`


```Coq
Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp),
  |== {{ P [ X |-> E] }} X ::= E {{ P }}.
```
> 替换之后, 怎样的_解释_能满足替换的要求? 我们给出一个语法替换后程序状态应维持的性质, 不作证明.
> 
> ```Coq
> Assertion_sub_spec
>      : forall (st1 : state) (st2 : var -> Z) (La : Lassn) 
>      (P : Assertion) (X : var) (E : aexp'), (* 如果正向赋值,允许E中有逻辑变量 *)
>        st2 X = aexp'_denote (st1, La) E ->   (* 程序状态st2中, X的值被替换 *)
>        (forall Y : var, X <> Y -> st1 Y = st2 Y) -> (* 其他值不变替换 *)
>        (st1, La) |== P [X |-> E] <-> (st2, La) |== P
> ```
**Proof.**
Assumption `(st1, La) |== P [X |-> E]` is equivalent to
- for any `st`. if `st(X) = aexp'_denote (st1, La) E, st(Y) = st1(Y)`, then `(st, La) |== P`
- `aexp'_denote (st1, La) E = aeval E st1`
Assumption `(st1, st2)` is in the denotation of `(X::=E)` is equivalent to
- st2(X) = aeval E st1
- st2(Y) = st(Y)
Putting these together, `(st2, La) |== P`.

```Coq
Lemma hoare_consequence_sound : forall (T: FirstOrderLogic) (P P' Q Q' : Assertion) c,
  FOL_sound T ->
  P |-- P' ->  |== {{P'}} c {{Q'}} ->
  Q' |-- Q ->  |== {{P}} c {{Q}}.
```

> 关键是看一阶逻辑中`P |-- P'`是什么性质. 因此我们引入一个一阶逻辑可靠的概念.
> 
> ```Coq
> Definition FOL_valid (P: Assertion): Prop :=
>   forall J: Interp, J |== P.
> 
> Definition FOL_sound (T: FirstOrderLogic): Prop :=
>   forall P: Assertion, FOL_provable P -> FOL_valid P.
> ```
> 
> **一阶逻辑的可靠性**: 如果P能推出P'(比如通过Proof Tree, 在我们这里的证明中实际上只是一个由FOL_provable性质定义的集合.), 那么所有符合P的状态都符合P'(语义上的满足性).


**Proof.**
Assumption `{{P'}} c {{Q'}}` gives:
- if `(st1, La) |== P'` and `ceval c st1 st2` then `(st2, La) |= Q'`

With `P |-- P'`, `Q' |-- Q` and the soundness of FOL, we can prove
- `(st1, La) |== P` $\rightarrow$ `(st2, La) |== Q'` $\rightarrow$ `(st2, La) |== Q`