---
title: 【Programming Language】Control Flow
url: pl-controlflow
date: 2020-05-12 14:02:48
tags: 
- Programming Language

categories: 
- Courses

---

Week 11 of 2020 Spring.

<!--more-->

[toc]

## The language

```Coq
Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CBreak                       (* <--- new *)
  | CCont                        (* <--- new *)
  .
```

## Denotational Semantics

考虑Skip和Break语句，在功能上显然是不一样的。但如果只站在起始状态和终止状态的角度上，他们都是同一个状态对的指称。因此我们原有的指称语义描述方式，不足以描述两个行为不同的语义。

我们不仅需要定义起始状态和中止状态的二元关系，还要指出终止状态的**终止方式**，三元关系。

```Coq
Inductive exit_kind: Type :=
  | EK_Normal
  | EK_Break
  | EK_Cont.
```
### Skip and Asgn

下面尝试定义不同语句的指称语义,Original Commands
```Coq
Definition skip_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Normal.

Definition asgn_sem (X: var) (E: aexp): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    ek = EK_Normal.
```

### Break & Continue

```
Definition break_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Break.

Definition cont_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Cont.
(* 某种意义上，循环体本身终止了。*)
```
### Seq

在Sequence和循环语义中，需要对Control flow定义额外的支持。

```Coq
Definition seq_sem (d1 d2: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st3 =>
    (exists st2, d1 st1 EK_Normal st2 /\ d2 st2 ek st3) (* 除了正常情况外 *) \/
    (d1 st1 ek st3 /\ ek <> EK_Normal). (* 还有一种可能，
      前半段程序已经break或continue了，后半段程序没有机会执行 *)
```

For sequential composition, the second command will be executed if and only if the first one terminates normally. 

### If
```Coq
Definition test_sem (X: state -> Prop): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ X st1 /\ ek = EK_Normal.

Definition union_sem (d d': state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    d st1 ek st2 \/ d' st1 ek st2.

Definition if_sem (b: bexp) (d1 d2: state -> exit_kind ->state -> Prop)
  : state -> exit_kind ->state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).
```

### Loop
原定义：
```Coq
Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> exit_kind -> state -> Prop)
  (n: nat)
  : state -> exit_kind -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.
```

现在，在loop_body中，可能有break和continue发生，因此，我们不能这样定义**恰好执行了n次**。（根据seq的定义，不管是break还是continue，`iter_loop_body b loop_body n'`都不会执行）。

我们需要修改`seq_sem`的定义，要求如果前半部分是普通中止或**continue中止**，继续执行，如果前半部分是**break中止**，则不再执行。现在`iter_loop_body n`的语义：恰好执行n次，以普通中止；或者在小于等于n次执行下以break中止。

又注意到，若前面循环体是break中止，那么作为整个循环来说，应当改成普通中止。

```Coq
Definition seq_sem' (d1 d2:state -> exit_kind -> state -> Prop) :=
  fun st1 ek st3 =>
    (exists st2, d1 st1 EK_Normal st2 /\ d2 st2 ek st3) \/
    (exists st2, d1 st1 EK_Cont st2 /\ d2 st2 ek st3) \/
    (d1 st1 EK_Break st3 /\ ek = EK_Normal).
```

```Coq
Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> exit_kind -> state -> Prop)
  (n: nat)
  : state -> exit_kind -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem'
              (test_sem (beval b))
              (seq_sem' loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 => exists n, d n st1 ek st2.

Definition loop_sem (b: bexp) (loop_body: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> exit_kind -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | CBreak => break_sem
  | CCont => cont_sem
  end.
```


## Hoare Logic

与指称语义类似，我们要设置不同的后条件声明不同中止状态下程序状态应符合的性质。

### IDEA
```Coq
Parameter hoare_triple: Assertion ->
                         com ->
                         Assertion *  (* Normal Postcondition *)
                         Assertion *  (* Break  Postcondition *)
                         Assertion ->  (* Continue Condition *)
                         Prop.

Notation "{{ P }}  c  {{ Q }} {{ QB }} {{ QC }}" :=
  (hoare_triple
     P
     c
     (Q%assert: Assertion, QB%assert: Assertion, QC%assert: Assertion))
  (at level 90, c at next level).
```

改进示例：
```Coq
Axiom hoare_seq : forall (P Q R RB RC: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} {{RB}} {{RC}} ->
  {{Q}} c2 {{R}} {{RB}} {{RC}} ->
  {{P}} CSeq c1 c2 {{R}} {{RB}} {{RC}}.
```

### Examples

通过理解`hoare_skip`理解另两个后条件的作用：不可能通过break、continue中止。
```Coq
Axiom hoare_skip : forall P,
  {{P}} CSkip {{P}} {{False}} {{False}}.

Axiom hoare_asgn_fwd : forall P (X: var) E,
  {{ P }}
  CAss X E
  {{ EXISTS x, P [X |-> x] AND
               {[AId X]} = {[ E [X |-> x] ]} }}
  {{False}}
  {{False}}.

Axiom hoare_if : forall P Q QB QC b c1 c2,
  {{ P AND {[b]} }} c1 {{Q}} {{QB}} {{QC}} ->
  {{ P AND NOT {[b]} }} c2 {{Q}} {{QB}} {{QC}} ->
  {{ P }} CIf b c1 c2 {{Q}} {{QB}} {{QC}}.

Axiom hoare_consequence : forall (P P' Q Q' QB QB' QC QC' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} {{QB'}} {{QC'}}->
  Q' |-- Q ->
  QB' |-- QB ->
  QC' |-- QC ->
  {{P}} c {{Q}} {{QB}} {{QC}}.
```
注意到seq、if等规则都要求break/continue的后条件都一定要求相同，我们需要consequence rule进行调整。



### Break
```Coq
Axiom hoare_break : forall P,
  {{P}} CBreak {{False}} {{P}} {{False}}.

Axiom hoare_cont : forall P,
  {{P}} CCont {{False}} {{False}} {{P}}.

Axiom hoare_while : forall I P b c, (*基于循环不变量i和程序符合的brek性质P*)
  {{ I AND {[b]} }} c {{I}} {{P}} {{I}} ->
  {{ I }} CWhile b c {{ P OR (I AND NOT {[b]}) }} {{False}} {{False}}.
```

问题：在怎样的前提下，我们可以推出循环作为整体的信息——拓展循环不变量。

循环不变量的语义：在循环体每次执行完**as normal or as continue**以后需要符合的条件，这一条件也是下一次循环开始时需要符合的条件。


> 在VST中，abbreviate中隐藏了各类不同的终止后条件。只有在证明需要接触到的时候才会展开。
> 理论上引入的复杂性从工程的角度来说，是可以解决的。


## Small Step Semantics With Virtual Loop Commands

We demonstrate two versions of small step semantics, one based on virtual loops and one based on control stack.

在小步执行的意义上，我们引入control flow之后，产生实质影响的只会是While指令。

Recall
```Coq
CS_While : forall st b c, 
    cstep
      (While b Do c EndWhile, st)
      (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).
```

现在，由于`c`中存在break和continue，这样的转换是不等价的。

### Virtual Loop Command

解决方案，记录当前还有哪些指令没有执行：

```Coq
Inductive com' : Type :=
  | CSkip'
  | CAss' (X: var) (a : aexp)
  | CSeq' (c1 c2 : com')
  | CIf' (b : bexp) (c1 c2 : com')
  | CWhile' (c1: com') (b : bexp) (c : com')  (* <--- the real change *)
  | CBreak'
  | CCont'
  .
```
`CWhile'`表示当前循环体还有`c1`这个指令还没执行完。
Of course we can easily define an injection from real programs' syntax trees to these auxiliary syntax trees. 建立对新语法树的映射。
```Coq
Fixpoint com_inj (c: com): com' :=
  match c with
  | CSkip => CSkip'
  | CAss X a => CAss' X a
  | CSeq c1 c2 => CSeq' (com_inj c1) (com_inj c2)
  | CIf b c1 c2 => CIf' b (com_inj c1) (com_inj c2)
  | CWhile b c => CWhile' CSkip' b (com_inj c)
  | CBreak => CBreak'
  | CCont => CCont'
  end.
```

```Coq
CS_While : forall st1 st2 c b c1 c2,
  cstep
    (c1, st1)
    (c2, st2) ->
  cstep
    (CWhile' c1 b c, st1)
    (CWhile' c2 b c, st2)
(* 循环体执行一步，整个while执行一步 *)
CS_WhileNormal : forall st b c,
  cstep
    (CWhile' CSkip' b c, st)
    (CWhile' (CIf' b c CBreak') b c, st).
(* 当前执行完了，用Break说明整个循环执行完了 *)
```

Break怎么办？
```Coq
CS_Break_False :
    forall b c st,
      cstep
        (CWhile' CBreak' b c, st)
        (CSkip', st)
(** CounterExample:
  (IF X == 0 Then Break Else Skip) ;; (X ::= X - 1)
  -->* Break ;; X ::= X - 1
  -->* ? *)
```
注意到，当我们到达了Break，要抹去的不只是break，还有break后面的所有语句

引入如下辅助定义
```Coq
Inductive start_with_break: com'-> Prop :=
| SWB_Break: start_with_break CBreak'
| SWB_Seq: forall c1 c2,
             start_with_break c1 ->
             start_with_break (CSeq' c1 c2).
```


```Coq
Inductive cstep : (com' * state) -> (com' * state) -> Prop :=
  | ......
  | CS_While : forall st1 st2 c b c1 c2,          (* <-- new 执行循环 *)
      cstep
        (c1, st1)
        (c2, st2) ->
      cstep
        (CWhile' c1 b c, st1)
        (CWhile' c2 b c, st2)
  | CS_WhileNormal : forall st b c,               (* <-- new 循环结束 *)
      cstep
        (CWhile' CSkip' b c, st)
        (CWhile' (CIf' b c CBreak') b c, st)
  | CS_WhileBreak : forall st b c_break c,        (* <-- new *)
    (* 循环体剩下的部分是Break开头的 *)
      start_with_break c_break ->
      cstep
        (CWhile' c_break b c, st)
        (CSkip', st)
  | CS_WhileCont : forall st b c_cont c,          (* <-- new *)
      start_with_break c_cont ->
      cstep
        (CWhile' c_cont b c, st)
        (CWhile' (CIf' b c CBreak') b c, st)
.
```



### Control Stack

基于控制栈定义的小步语义。

Now we turn to a control-stack-based definition. Here, every element in a control stack describe a loop (loop condition and loop body) and an after-loop command.

如C++中，允许循环体内定义局部变量，部分编译器会利用栈实现这一特性处理重名。

```Coq
Definition cstack: Type := list (bexp * com * com).
```
定义控制栈：循环条件，循环体，循环执行后要执行的事情。

```Coq
Inductive start_with_loop: com -> bexp -> com -> com -> Prop :=
| SWL_While: forall b c, start_with_loop (CWhile b c) b c CSkip (* 本身是循环 *)
| SWL_Seq: forall c1 b c11 c12 c2,
             start_with_loop c1 b c11 c12 ->
             start_with_loop (CSeq c1 c2) b c11 (CSeq c12 c2).
  (* 顺序执行，把c1当中剩下的语句放入剩余操作去 *)
```


现在是带上control stack三元组的二元关系。

```Coq
Inductive cstep : (com * cstack * state) -> (com * cstack * state) -> Prop :=
  | CS_AssStep : forall st s X a a',
      astep st a a' ->
      cstep (* 赋值语句的进一步化简 *)
        (CAss X a, s, st)
        (CAss X a', s, st)
  | CS_Ass : forall st1 st2 s X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (* 修改变量 *)
        (CAss X (ANum n), s, st1)
        (CSkip, s, st2)
  | CS_SeqStep : forall st s c1 c1' st' c2,
      cstep
        (c1, s, st)
        (c1', s, st') ->
      cstep
        (CSeq c1 c2, s, st)
        (CSeq c1' c2, s, st')
  | CS_Seq : forall st s c2,
      cstep
        (CSeq CSkip c2, s, st)
        (c2, s, st)
  | CS_IfStep : forall st s b b' c1 c2,
      bstep st b b' ->
      cstep
        (CIf b c1 c2, s, st)
        (CIf b' c1 c2, s, st)
  | CS_IfTrue : forall st s c1 c2,
      cstep
        (CIf BTrue c1 c2, s, st)
        (c1, s, st)
  | CS_IfFalse : forall st s c1 c2,
      cstep (* 以上命令都是在我们原有小步语义上带上控制栈*)
        (CIf BFalse c1 c2, s, st)
        (c2, s, st)
  | CS_While : forall st s c b c1 c2,                 (* <-- new *)
      start_with_loop c b c1 c2 -> (* 程序c以循环开始 *)
      cstep
        (c, s, st) (* 压入新的一层控制栈 *)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Skip : forall st s b c1 c2,                    (* <-- new *)
      cstep (* 过去CSkip是终止整个程序，但在有控制栈的情况下*)
            (* 这里CSkip是说循环最内层执行完了，要返回外层 *)
        (CSkip, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Break : forall st s b c1 c2 c,                 (* <-- new *)
      start_with_break c ->
      cstep (* 出栈，直接退出 *)
        (c, (b, c1, c2) :: s, st)
        (c2, s, st)
  | CS_Cont : forall st s b c1 c2 c,                  (* <-- new *)
      start_with_cont c ->
      cstep (* 取栈头，重新开始测试、循环 *)
        (c, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
.
```

