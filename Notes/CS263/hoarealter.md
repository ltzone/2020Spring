---
title: 【Programming Language】Alternative Hoare Logic
url: pl-hoarealter
date: 2020-04-23 08:07:43
tags: 
- Programming Language

categories: 
- Courses

---

Week 8 of 2020 Spring

<!--more-->

[toc]

我们能否选择一组不同的霍尔逻辑推理规则（如Assignment Rule），我们已经证明了选用backward rule的霍尔逻辑是可靠且完全的。

## Choice of Proof Rules

霍尔逻辑需要依靠断言推导的一阶逻辑可靠性、完全性，我们以定义的形式给出。

```Coq
Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition FOL_sound (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_provable P -> FOL_valid P.

Definition FOL_complete (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_valid P -> FOL_provable P.

Variable T: FirstOrderLogic.

Hypothesis T_sound: FOL_sound T.

Hypothesis T_complete: FOL_complete T.

Theorem TrivialFOL_complete_der: forall P Q,
  FOL_valid (P IMPLY Q) ->
  P |-- Q.

Theorem TrivialFOL_sound_der: forall P Q,
  P |-- Q ->
  FOL_valid (P IMPLY Q).


Theorem derives_refl: forall P, P |-- P.

Theorem AND_derives: forall P1 Q1 P2 Q2,
  P1 |-- P2 ->
  Q1 |-- Q2 ->
  P1 AND Q1 |-- P2 AND Q2.
```

### Soundness of the forward assignment rule

Recall：可靠性的证明是对推理规则的证明树做结构归纳：每一条推理规则都可以保持霍尔逻辑的可靠性，证明正向赋值语句规则，我们其实是在证明这样一件事情。
```Coq
Lemma hoare_asgn_fwd_sound : forall P (X: var) (x: logical_var) (E: aexp),
  assn_free_occur x P = O -> 
  (* 从语法树的角度看待断言，必须要考虑逻辑变量x本身不能在P中出现 *)
  |== {{ P }}
        X ::= E
      {{ EXISTS x, P [X |-> x] AND
                   {[X]} = {[ E [X |-> x] ]} }}.
```

**Proof Sketch.**
  展开valid定义，得到`st1`起始满足P，`st2`终止。
  考虑赋值语句的指称语义，作用在`ceval (X::=E) st1 st2`上
  
  展开EXISTS, AND等的语法树
  即 替换之后的st2其实就是st1。
  后断言中x的值，其实就是起始状态上`X`的值，EXISTS (st1 X)。
  The rest of proof follows by definition. For two branches of AND
  - 替换后的P在st2有效；Recall:语法替换与模型替换的语义相等（`Assertion_sub_spec`）
  - 替换后的aexp与st1上的X相等 （`aexp_sub_spec`）

### Soundness of sequential composition's associativity

我们可以论证，加入顺序执行的结合律后，霍尔逻辑的有效性不受影响。

辅助性质，指称语义的结合律。

```Coq
Lemma concat_assoc: forall R1 R2 R3: state -> state -> Prop,
  Rel.equiv
    (concat (concat R1 R2) R3)
    (concat R1 (concat R2 R3)).

Lemma seq_assoc : forall c1 c2 c3,
  com_equiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
```

```Coq
Lemma seq_assoc_sound : forall P c1 c2 c3 Q,
  |== {{ P }} c1 ;; c2 ;; c3 {{ Q }} <->
  |== {{ P }} (c1 ;; c2) ;; c3 {{ Q }}.
```
**Proof.** 展开valid定义，利用指称语义的等价性，直接得证。


> 还有很多规则可以引入，原则上，**从可靠性的角度**，我们只需证明这些新的逻辑能否从有效的霍尔三元组推出。


### Deriving single-sided consequence rules

Recall,霍尔逻辑中，我们有单侧的霍尔逻辑consequence rule。当时我们的证明是基于**可证**的角度
```Coq
Lemma hoare_consequence_pre: forall P P' c Q,
  P |-- P' ->
  |-- {{ P' }} c {{ Q }} ->
  |-- {{ P }} c {{ Q }}.

Lemma hoare_consequence_post: forall P c Q Q',
  |-- {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  |-- {{ P }} c {{ Q }}.
```

这说明，我们在原有的霍尔逻辑中增加这两条是没问题的，因为他们本身就是霍尔逻辑可导出的规则。

> 我们有两种角度说明新的规则引入是否会破坏可靠性：①是否可靠，②是否可导出（+完全性，原有的规则已经够了）

我们就根据这两条原则研究forward assignment rule

### Deriving the forward assignment rule

```Coq
Lemma hoare_asgn_fwd_der : forall P (X: var) (x: logical_var) (E: aexp),
  assn_free_occur x P = O ->
  |-- {{ P }}
        X ::= E
      {{ EXISTS x, P [X |-> x] AND
                   {[X]} = {[ E [X |-> x] ]} }}.
```
调用bwd_seq，我们得到如下Proof Goal。
```Coq
P |-- (EXISTS x, P [X |-> x] AND {[X]} = {[E [X |-> x]]}) [X |-> E]
```

两种证明思路：语法替换/语义替换。

语法替换上：对` P [X |-> x]`做二次替换，得到`P [X |-> x]`本身，`{[X]}`替换得到`{[E]}`，对`{[E [X |-> x]]}`，类似的相当于没有做替换。
那么取`x = {[X]}`，代入，配合一阶逻辑的推理，可证。

语义替换上，只需证明，对任意程序状态，满足左边则满足右边，把语法替换应用到状态变量上的替换。替换两次。

结论：正向的霍尔逻辑一定可以由反向霍尔逻辑规则和consequence rule推出。

### Inversion of Sequence Rule

那么 Sequence Rule的结合律是否可以导出？注意到，这个引理的形式不是组合得到的（非局部推到整体），它不是一条导出规则。但我们依然可以证明，这条规则在现有霍尔逻辑规则中可证。

```Coq
Lemma seq_assoc_der : forall P c1 c2 c3 Q,
  |-- {{ P }} c1 ;; c2 ;; c3 {{ Q }} <->
  |-- {{ P }} (c1 ;; c2) ;; c3 {{ Q }}.
```
如果我们有证明方法证明（构造）前者，那我们就有方法证明后者。（该规则也不会引入新的信息）

```Coq
Lemma hoare_seq_inv: forall P c1 c2 R,
  |-- {{ P }} c1 ;; c2 {{ R }} ->
  exists Q, (|-- {{ P }} c1 {{ Q }}) /\ (|-- {{ Q }} c2 {{ R }}).
```

证明：考虑`{{ P }} c1 ;; c2 {{ R }}`的最后一步，不仅可能是sequence rule，也可能是consequence rule。对后者，我们总能继续寻找，由于树的高度是有限的，所以必然有sequence rule用到。
思路：对proof tree 做归纳证明。

利用上述引理拆出中间状态满足的条件，我们就可以完成证明。

### If And Sequence
```Coq
Lemma hoare_if_inv: forall P b c1 c2 Q,
  |-- {{P}} If b Then c1 Else c2 EndIf {{Q}} ->
  (|-- {{ P  AND {[b]} }} c1 {{Q}}) /\
  (|-- {{ P  AND NOT {[b]} }} c2 {{Q}}).
```
类似的，最后一步用if或最后一步用consequence，归纳证明。
对Consequence的情况：
Assumption:
1. `|-- {{P}} If b Then c1 Else c2 EndIf {{Q}} `
2. `P |-- P'`
3. `Q' |-- Q`
IH：
1. `|-- {{P' AND [[b]]}} c1 {{Q'}}`
2. `|-- {{P' AND NOT [[b]]}} c2 {{Q'}}`
我们需要证明的是：
1. `|-- {{P AND [[b]]}} c1 {{Q}}`
2. `|-- {{P AND NOT [[b]]}} c2 {{Q}}`
显然的。

```Coq
Lemma if_seq_der : forall P b c1 c2 c3 Q,
  |-- {{ P }} If b Then c1 Else c2 EndIf;; c3 {{ Q }} ->
  |-- {{ P }} If b Then c1;; c3 Else c2;; c3 EndIf {{ Q }}.
```

> 总结：
> 新规则不会增加新的有效三元组，都可以从现有规则导出（直接导出or前提可证则结论可证）


## General First Order Logic

前面说到，一阶逻辑可靠，则霍尔逻辑可靠。一阶逻辑完全，则霍尔逻辑完全。问题是：常见的一阶逻辑有哪些规则？为什么是可靠的，为什么是完全的。

**A first order language consists of logical symbols and nonlogical symbols (relation symbols and function symbols**

一阶逻辑的term：要么是一个逻辑变量，要么是一个（确定项数）的函数+若干项。
一阶逻辑的命题：相等、多元关系、命题常量、命题组合
```Coq
P ::= t = t
    | R t t .. t
    | TRUE
    | FALSE
    | P IMPLY P
    | P AND P
    | P OR P
    | NOT P
    | FORALL v P
    | EXISTS v P
```
**每选择一组不同的常量符号、关系符号，我们就确定了一个一阶逻辑**
霍尔逻辑中：函数符号（+,-,*,变量取值），关系符号（<=, ==）

定义一阶逻辑的符号集。
```Coq
Class Symbol: Type := {
  RS: Type; (* Relation symbol *)
  FS: Type; (* Function symbol *)
  R_ary: RS → nat;
  F_ary: FS → nat
}.
```

```Coq
Definition logical_var: Type := nat.

Inductive term {s: Symbol}: Type :=
| term_var (v: logical_var): term
| term_constr (t: unfinished_term O): term
with unfinished_term {s: Symbol}: nat -> Type :=
| func (f: FS): unfinished_term (F_ary f)
| fapp {n: nat} (f: unfinished_term (S n)) (x: term): unfinished_term n.
```

定义原子命题：
```Coq
Inductive unfinished_atom_prop {s: Symbol}: nat -> Type :=
| rel (r: RS): unfinished_atom_prop (R_ary r)
| rapp {n: nat} (r: unfinished_atom_prop (S n)) (x: term): unfinished_atom_prop n.

Inductive prop {s: Symbol}: Type :=
| PEq (t1 t2: term): prop
| PAtom (P: unfinished_atom_prop O): prop
| PTrue: prop
| PFalse: prop
| PNot (P: prop): prop
| PImpl (P Q: prop): prop
| PAnd (P Q: prop): prop
| POr (P Q: prop): prop
| PForall (x: logical_var) (P: prop): prop
| PExists (x: logical_var) (P: prop): prop.
```

From now on, we will only use one simple first order language for convenience. This language does not have any function symbol and only has one binary relation symbol.
```Coq
P ::= v = v
    | R v v
    | FALSE
    | P IMPLY P
    | FORALL v P
```

我们定义的这个语言虽然足够小，但表达力也足够强。
```Coq
Definition PTrue: prop := PImpl PFalse PFalse.
Definition PNot (P: prop): prop := PImpl P PFalse.
Definition PAnd (P Q: prop): prop := PNot (PImpl P (PNot Q)). 
Definition POr (P Q: prop): prop := PImpl (PNot P) Q. 
Definition PExists (x: logical_var) (P: prop): prop :=
  PNot (PForall x (PNot P)).
```

i.p. 集合论的基础，二元关系定义为属于关系
e.g. "X is an empty set" = forall x, NOT x in X


### Provable FOL

哪些命题可证？
```Coq
Inductive provable: prop -> Prop :=
| PImply_1: forall P Q, provable (P IMPLY (Q IMPLY P))
| PImply_2: forall P Q R, provable
   ((P IMPLY Q IMPLY R) IMPLY
    (P IMPLY Q) IMPLY
    (P IMPLY R))
| Modus_ponens: forall P Q,
    provable (P IMPLY Q) ->
    provable P ->
    provable Q
| PFalse_elim: forall P,
    provable (PFalse IMPLY P)
| Excluded_middle: forall P,
    provable (NOT P OR P)
| PForall_elim: forall x t P,
    provable ((FORALL x, P) IMPLY (P [x |-> t]))
| PForall_intros: forall x P Q,
    prop_free_occur x P = O ->
    provable (P IMPLY Q) ->
    provable (P IMPLY FORALL x, Q)
| PEq_refl: forall t,
    provable (t = t)
| PEq_sub: forall P x t t',
    provable (t = t' IMPLY P[x |-> t] IMPLY P[x |-> t']).

Notation "|--  P" := (provable P) (at level 91, no associativity): FOL_scope.
```

注意到有关关系的推理规则中，出现了语法替换的概念，用整数项替换逻辑变量。定义方法类似。


类似的，要证明可靠性，我们要定义有效性(永真)，随后需要定义“满足”，而定义满足，需要定义“解释”=二元关系+逻辑变量的解释，论域(domain)

```Coq
Inductive Interp: Type :=
| Build_Interp (D: Type) (Rel: D -> D -> Prop) (La: logical_var -> D) : Interp.

Fixpoint satisfies (J: Interp) (d: prop): Prop :=
    match d with
    | PEq t1 t2   => (term_denote J t1 = term_denote J t2)
    | PRel t1 t2  => Rel_of J (term_denote J t1) (term_denote J t2)
    | PFalse      => False
    | PImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | PForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity): FOL_scope.

Definition valid (P: prop): Prop :=
  forall J: Interp, J |== P.

Notation "|==  P" := (valid P) (at level 91, no associativity): FOL_scope.
```


```Coq
Definition sound: Prop :=
  forall P: prop, |-- P -> |== P.

Definition complete: Prop :=
  forall P: prop, |== P -> |-- P.
```

有关可靠性的证明，只需根据语义进行检验。
The soundness proof is easy — we only need to do induction over the proof tree. The only interest cases are about those two proof rules for universal quantifiers. We need the following lemmas.
```Coq
Lemma prop_sub_spec: forall J (P: prop) (x: logical_var) (t: term),
  J |== P[ x |-> t] <->
  Interp_Lupdate J x (term_denote J t) |== P.
Admitted.

Lemma no_occ_satisfies: forall J P x v,
  prop_free_occur x P = O ->
  (J |== P <-> Interp_Lupdate J x v |== P).
Admitted.
```
