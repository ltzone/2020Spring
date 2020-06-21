---
title: 【Programming Language】Concurrency
url: pl-concurrency
date: 2020-06-11 09:06:56
tags: 
- Programming Language

categories: 
- Courses

---

Week 15 of 2020 Spring

<!--more-->

[toc]


## Language
```Coq
Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CPar (c1 c2: com) (* <- new *)
  .
```

## Small Step Semantics

```Coq
Module SmallStepSemantics.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2,
      cstep (Skip ;; c2, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st)
  | CS_ParLeft: forall st st' c1 c1' c2,
      cstep (c1, st) (c1', st') ->
      cstep (CPar c1 c2, st) (CPar c1' c2, st')
  | CS_ParRight: forall st st' c1 c2 c2',
      cstep (c2, st) (c2', st') ->
      cstep (CPar c1 c2, st) (CPar c1 c2', st')
  | CS_Par: forall st,
      cstep (CPar Skip Skip, st) (Skip, st).

End SmallStepSemantics.
```

## Denotational Semantics
```Coq
Inductive abs_thread :=
| LOCAL
| ENVIR.

Definition trace_set := state -> list (abs_thread * state) -> state -> Prop.

Inductive environ_trace: trace_set :=
| environ_trace_nil: forall st, environ_trace st nil st
| environ_trace_cons: forall st1 st2 st3 tr,
    environ_trace st2 tr st3 ->
    environ_trace st1 ((ENVIR, st2) :: tr) st3.
```
注意，environ_trace在不做约束的情况下 can be anything。

顺序执行、分支执行、循环若干次执行的语义如下。
```Coq
Definition seq_sem (d1 d2: trace_set): trace_set :=
  fun st1 tr st3 =>
    exists tr1 tr2 st2,
      d1 st1 tr1 st2 /\ d2 st2 tr2 st3 /\ tr = tr1 ++ tr2.

Definition union_sem (d d': trace_set): trace_set :=
  fun st1 tr st2 =>
    d st1 tr st2 \/ d' st1 tr st2.

Definition omega_union_sem (d: nat -> trace_set): trace_set :=
  fun st1 tr st2 => exists n, d n st1 tr st2.
```


The most interesting case is to define parallel compositions' behavior.

对并发线程，要求trace长度一样，且两个线程之间，要么全部是环境步骤组合成环境步骤，要么一个环境步骤一个本地步骤，组合成一个本地步骤。
```Coq
Inductive interleave_trace:
  list (abs_thread * state) ->
  list (abs_thread * state) ->
  list (abs_thread * state) ->
  Prop :=
| interleave_nil: interleave_trace nil nil nil
| interleave_cons_l: forall tr1 tr2 tr3 st,
    interleave_trace tr1 tr2 tr3 ->
    interleave_trace ((LOCAL, st) :: tr1) ((ENVIR, st) :: tr2) ((LOCAL, st) :: tr3)
| interleave_cons_r: forall tr1 tr2 tr3 st,
    interleave_trace tr1 tr2 tr3 ->
    interleave_trace ((ENVIR, st) :: tr1) ((LOCAL, st) :: tr2) ((LOCAL, st) :: tr3)
| interleave_cons_env: forall tr1 tr2 tr3 st,
    interleave_trace tr1 tr2 tr3 ->
    interleave_trace ((ENVIR, st) :: tr1) ((ENVIR, st) :: tr2) ((ENVIR, st) :: tr3).

Definition par_sem (d1 d2: trace_set): trace_set :=
  fun st1 tr st2 =>
    exists tr1 tr2,
      d1 st1 tr1 st2 /\ d2 st1 tr2 st2 /\ interleave_trace tr1 tr2 tr.
```
### Coarse-Grained Denotational Semantics

假设求值和赋值一步完成。

```Coq
Module DenotationalSemantics_MiddleStepTrace.
  
Definition skip_sem: state -> list (abs_thread * state) -> state -> Prop :=
  environ_trace.

Definition local_asgn_sem (X: var) (E: aexp): trace_set :=
  fun st1 tr st2 =>
    st2 X = aeval E st1 /\
    (forall Y, X <> Y -> st1 Y = st2 Y) /\
    tr = (LOCAL, st2) :: nil.

Definition asgn_sem (X: var) (E: aexp): trace_set :=
  seq_sem environ_trace (seq_sem (local_asgn_sem X E) environ_trace).

Definition local_test_sem (X: state -> Prop): trace_set :=
  fun st1 tr st2 =>
    st1 = st2 /\ tr = (LOCAL, st1) :: nil /\ X st1.

Definition if_sem (b: bexp) (d1 d2: trace_set): trace_set :=
  union_sem
    (seq_sem environ_trace (seq_sem (local_test_sem (beval b)) d1))
    (seq_sem environ_trace (seq_sem (local_test_sem (beval (! b))) d2)).

Fixpoint iter_loop_body (b: bexp) (loop_body: trace_set) (n: nat): trace_set :=
  match n with
  | O => local_test_sem (beval (! b))
  | S n' => seq_sem
              (local_test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: trace_set): trace_set :=
  seq_sem
    environ_trace
    (seq_sem (omega_union_sem (iter_loop_body b loop_body)) environ_trace).

Fixpoint ceval (c: com): trace_set :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | CPar c1 c2 => par_sem (ceval c1) (ceval c2)
  end.

End DenotationalSemantics_MiddleStepTrace.
```


### Finer-Grained Denotational Semantics

以上的定义中，我们假定所有的赋值和条件测试都是一瞬间完成的。有时我们会认为这样的假设是不合理的，（与此前我们定义的小步语义不对应）下面我们考虑另一种指称语义，即赋值过程中要对程序变量的值做读取。因此，我们现在不仅需要重新定义程序的语义，还需要定义整数类型表达式和布尔类型表达式**求值过程的语义**。因为它还可能受到其他线程的影响。

注意：我们不能单用一个路径表示整数类型表达式求值的语义，它应该是一个整数值和路径的有序对的集合，因为我们要求整数表达式最后结果是一个值，而值可能因为求值过程的不同而不同。我们规定，整数表达式求值是一个整数值到求值过程的集合**映射**。（从计算结果**计算**求值过程集合的函数，当然trace的集合可能是一个空集）

```Coq
Fixpoint aeval (a: aexp): Z -> trace_set :=
  match a with
  | ANum n => ANum_sem n
  | AId X => AId_sem X
  | APlus a1 a2 => APlus_sem (aeval a1) (aeval a2)
  | AMinus a1 a2 => AMinus_sem (aeval a1) (aeval a2)
  | AMult a1 a2 => AMult_sem (aeval a1) (aeval a2)
  end.

Definition ANum_sem (n: Z): Z -> trace_set :=
  fun res st1 tr st2 =>
    environ_trace st1 tr st2 /\ res = n.
    (* 路径全部是本地操作，且返回值是整数常数n*)

Definition local_AId_sem (X: var): Z -> trace_set :=
  fun res st1 tr st2 =>
    st1 = st2 /\ tr = (LOCAL, st1) :: nil /\ res = st1 X.
    (* AuxDef 本地读取 *)

Definition AId_sem (X: var): Z -> trace_set :=
  fun res =>
    seq_sem environ_trace (seq_sem (local_AId_sem X res) environ_trace).
    (* 以res为返回值的变量读取：环境步骤+本地读取+环境步骤 *)

Definition APlus_sem (d1 d2: Z -> trace_set): Z -> trace_set :=
  fun res st1 tr st2 =>
    exists res1 res2,
      seq_sem (d1 res1) (d2 res2) st1 tr st2 /\ res = res1 + res2.
    (* 先算前一个表达式，再算后一个表达式，假定它们分别会终止计算出res1和res2，再加起来，
       加起来没有在trace中体现为LOCAL，因为没有和程序状态做交互，这个设定是合理的 *)
```

类似的，定义布尔表达式的语义为布尔值到执行路径集合的映射
```Coq
Definition BEq_sem (d1 d2: Z -> trace_set): bool -> trace_set :=
  fun res st1 tr st2 =>
    exists res1 res2,
      seq_sem (d1 res1) (d2 res2) st1 tr st2 /\ (res = true <-> res1 = res2).
  (* 先计算，再判定*)

Definition BLe_sem (d1 d2: Z -> trace_set): bool -> trace_set.

Definition BTrue_sem: bool -> trace_set :=
  fun res st1 tr st2 =>
    environ_trace st1 tr st2 /\ res = true.
  (* 本地不执行LOCAL，全部是环境路径，再判定*)

Definition BFalse_sem: bool -> trace_set.

Definition BNot_sem (d: bool -> trace_set) : bool -> trace_set :=
  fun res st1 tr st2 =>
    exists res',
      d res' st1 tr st2 /\ res = negb res'.

Definition BAnd_sem (d1 d2: bool -> trace_set) : bool -> trace_set :=
  fun res st1 tr st2 =>
    (d1 false st1 tr st2 /\ res = false) \/ (* 注意：如果前半是false，就执行结束了 *)
    (seq_sem (d1 true) (d2 res) st1 tr st2). (* 注意：短路求值 *)
  

Fixpoint beval (b: bexp): bool -> trace_set :=
  match b with
  | BEq a1 a2 => BEq_sem (aeval a1) (aeval a2)
  | BLe a1 a2 => BLe_sem (aeval a1) (aeval a2)
  | BTrue => BTrue_sem
  | BFalse => BFalse_sem
  | BNot b0 => BNot_sem (beval b0)
  | BAnd b1 b2 => BAnd_sem (beval b1) (beval b2)
  end.
```



回到ceval，我们发现赋值、条件、循环语义中由于含有求值过程，需要改写语义
```Coq
Fixpoint ceval (c: com): trace_set :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | CPar c1 c2 => par_sem (ceval c1) (ceval c2)
  end.
```

```Coq
Definition skip_sem: state -> list (abs_thread * state) -> state -> Prop :=
  environ_trace.

Definition local_asgn_sem (X: var) (n: Z): trace_set :=
  fun st1 tr st2 =>
    st2 X = n /\
    (forall Y, X <> Y -> st1 Y = st2 Y) /\
    tr = (LOCAL, st2) :: nil.

Definition asgn_sem (X: var) (E: aexp): trace_set :=
  fun st1 tr st2 =>
    exists n,
      seq_sem (aeval E n) (seq_sem (local_asgn_sem X n) environ_trace) st1 tr st2.
  (* 增加了本地asgn的过程，存在整数n使表达式求值结果为n，这个n对应着一个求值过程的trace set
     即任何路径如果合法，一定是这几步的连接 *)

Definition if_sem (b: bexp) (d1 d2: trace_set): trace_set :=
  union_sem
    (seq_sem (beval b true) d1)
    (seq_sem (beval b false) d2).
  (* 要么是true，要么是false求值后，执行对应分支路径 *)

Fixpoint iter_loop_body (b: bexp) (loop_body: trace_set) (n: nat): trace_set :=
  match n with
  | O => beval b false
  | S n' => seq_sem
              (beval b true)
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition loop_sem (b: bexp) (loop_body: trace_set): trace_set :=
  omega_union_sem (iter_loop_body b loop_body).
```

注意有关环境步骤的一致性，比如`AId_sem`之后的环境步骤，和`asgn_sem`中先求值后赋值之间的环境步骤，是否都有填充到位。

## Hoare Logic

For axiomatic semantics, we introduce an extension of Hoare logic here, the logic of rely-guanrantee (依赖保证逻辑). Sometimes we write RG for simplicity. In short, rely is a set of actions that the environment may take. Guanrantee is a promise that the local thread make: "I will only take these actions."

> rely: 本线程对其他线程的假设
> guarantee：本线程对其他线程的保证

```Coq
Reserved Notation "R :; G |-- {{ P }}  c  {{ Q }}"
  (at level 90, G at next level, P at next level, c at next level, Q at next level).
```

具体而言：R or G**是可以执行操作的集合（action set）**,操作是一个程序状态到另一个程序状态的二元组构成的集合。环境所有可能做的操作都在R之内，本线程做的所有操作都在G这一范围内。霍尔三元组的语义：**在R和G（允许操作的程序状态二元组集合）的假设和约束下，如果起始状态满足`P`，执行`c`终止的情况下（其中还可能有环境线程在操作），结果会能满足`Q`。**

特例：R为空集，G为全集。即环境线程什么都不做，本地线程什么都可以做，就退化到单线程程序了。

```Coq
Class Actions : Type := {
  action_set: Type;
  action_union: action_set -> action_set -> action_set;
  stable: Assertion -> action_set -> Prop;
  permit: Assertion -> var -> aexp -> action_set -> Prop
}.

Inductive hoare_triple {A: Actions}: Type :=
| Build_hoare_triple
    (R: action_set)
    (G: action_set)
    (P: Assertion)
    (c: com)
    (Q: Assertion).
```

在后面的定义中，我们发现我们需要加入新的两个概念
> stable: 断言和操作集的二元关系，对任意程序状态，如果满足这些断言，对状态进行任意操作后，依然满足这些断言，我们就称断言相对这些操作是稳定的。
如，SKIP语句：
```Coq
| hoare_skip : forall R G P,
    stable P R ->
    R :; G |-- {{P}} CSkip {{P}}
```
从起始状态到终止状态，其他线程也有可能改变程序状态，由于存在`stable R G`的附加条件，无论环境线程怎么变，当前程序状态都会符合`P`，因此该三元组成立。

利用Rely和Guarantee，我们可以写出如下定义：
```Coq
  | hoare_seq : forall R G (P1 P2 P3: Assertion) (c1 c2: com),
      R :; G |-- {{P1}} c1 {{P2}} ->
      R :; G |-- {{P2}} c2 {{P3}} ->
      R :; G |-- {{P1}} (CSeq c1 c2) {{P3}}
  | hoare_if : forall R G P Q (b: bexp) c1 c2,
      R :; G |-- {{ P AND {[b]} }} c1 {{ Q }} ->
      R :; G |-- {{ P AND NOT {[b]} }} c2 {{ Q }} ->
      R :; G |-- {{ P }} CIf b c1 c2 {{ Q }}
```
- 额外说明：布尔表达式的求值，我们只有默认是在一瞬间完成的，当前规则才成立，不然我们还需要一些其他的额外条件
- 会不会，b判定完之后，开始c1之前，外部把b改了？
  - 不影响，因为b判定完后，依然是从符合`R :; G |-- {{ P AND {[b]} }} c1 {{ Q }}`的三元组推出的。
  - 不然，`P AND b`相对于rely的状态是不稳定的，后面会看到这是不可能的。

```Coq
  | hoare_while : forall R G P (b: bexp) c,
      stable (P AND NOT {[b]}) R ->
      R :; G |-- {{ P AND {[b]} }} c {{P}} ->
      R :; G |-- {{P}} CWhile b c {{ P AND NOT {[b]} }}
```
- 程序执行完一定是一次while判定为False，我们要求环境步骤此时不可以破坏它，所以加上了stable的限制。

> permit: 保证所有本地线程的操作都符合guarantee。在_程序状态_符合某断言的前提下，对某变量进行赋值_操作_（一瞬间完成），满足guarantee的要求

```Coq
  | hoare_asgn_bwd : forall R G P (X: var) (E: aexp),
      stable (P [ X |-> E ]) R ->
      stable P R ->
      permit (P [ X |-> E ]) X E G ->
      R :; G |-- {{ P [ X |-> E] }} CAss X E {{ P }}
  | hoare_par : forall G1 G2 R P c1 c2 Q,
      action_union G2 R :; G1 |-- {{ P }} c1 {{ Q }} ->
      action_union G1 R :; G2 |-- {{ P }} c2 {{ Q }} ->
      R :; action_union G1 G2 |-- {{ P }} CPar c1 c2 {{ Q }}
```

并行程序应符合的性质：
- 两个线程的前后条件一样。
- 对外有R依赖，c1允许执行G1，c2允许执行G2，因此合在一起允许执行的操作就是G1和G2
- 对c1线程而言，内部保证是G1，外部依赖是R和G2的并集
- 同样，对c2线程而言，内部保证是G2，外部依赖是R和G1的并集

```Coq
  | hoare_consequence : forall R G (P P' Q Q' : Assertion) c,
      stable P R ->
      stable Q R ->
      P |-- P' ->
      R :; G |-- {{P'}} c {{Q'}} ->
      Q' |-- Q ->
      R :; G |-- {{P}} c {{Q}}
```
要求，新增加的更强前条件和更弱后条件得是稳定的。