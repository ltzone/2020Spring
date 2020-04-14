---
title: 【Programming Language】 Denotations VS Triples 1
url: pl-denovshoare
date: 2020-04-14 14:01:49
tags: 
- Programming Language

categories: 
- Courses

---

Week 7 of 2020 Spring

<!--more-->

[toc]

基于指称语义与基于霍尔逻辑, 三元组都能够得到解释. 本节我们探讨两者的关系.

## Review Hoare

```Coq
Module HoareLogic.

Import Concrete_Pretty_Printing.

Axiom hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1;;c2 {{R}}.

Axiom hoare_skip : forall P,
  {{P}} Skip {{P}}.

Axiom hoare_if : forall P Q b c1 c2,
  {{ P AND {[b]} }} c1 {{ Q }} ->
  {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.

Axiom hoare_while : forall P b c,
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

Axiom hoare_asgn_fwd : forall P `(X: var) E,
  {{ P }}
  X ::= E
  {{ EXISTS x, P [X |-> x] AND
               {[X]} = {[ E [X |-> x] ]} }}.

Axiom hoare_asgn_bwd : forall P `(X: var) E,
  {{ P [ X |-> E] }} X ::= E {{ P }}.

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.

End HoareLogic.
```


### Assertion Language as Syntax Tree

我们现在要探讨霍尔逻辑和指称语义的关系, 要探讨的是霍尔逻辑的本质. 而不是如何使用霍尔逻辑证明程序. 我们需要了解如何刻画一个逻辑和语义之间的关系.

Assertion Language(断言) 既可以是语法树,也可以是符合程序状态的集合. 我们下面从语法树的形式进行讨论.
每一个逻辑变量都有各自的编号.
```Coq
Definition logical_var: Type := nat.
```
断言中可以通过量词引入逻辑变量
```Coq
EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]}.
```

那么表达式的语法树也要引入逻辑变量.
```Coq
Inductive aexp' : Type :=
  | ANum' (n : Z)
  | AId' (X : var)
  | ALid (x: logical_var)
  | APlus' (a1 a2 : aexp')
  | AMinus' (a1 a2 : aexp')
  | AMult' (a1 a2 : aexp').
```

但当我们想通过一阶逻辑证明如下推导时

```Coq
{[Y]} = {[X]} * 2 + 1 |-- EXISTS z, {[(Y + 1) - 2 * z]} = 0
----------------------
{[Y]} = {[X]} * 2 + 1 |-- {[(Y + 1) - 2 * ({[X]} + 1) ]} = 0
```

这里, `{[X]} + 1`是一个整数项, 而非整数`Z`. 我们希望这样定义: 所有的整数项都被认为是常数, 出现在表达式中.

```Coq
Inductive aexp' : Type :=
  | ANum' (t : term)
  | AId' (X: var)
  | APlus' (a1 a2 : aexp')
  | AMinus' (a1 a2 : aexp')
  | AMult' (a1 a2 : aexp')
with term : Type :=
  | TNum (n : Z)
  | TId (x: logical_var)
  | TDenote (a : aexp')
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term).
```

我们完成了**可变的整数定义表达式.**, 类似地定义`bexp'`

```Coq
Inductive bexp' : Type :=
  | BTrue'
  | BFalse'
  | BEq' (a1 a2 : aexp')
  | BLe' (a1 a2 : aexp')
  | BNot' (b : bexp')
  | BAnd' (b1 b2 : bexp').
```

显然, 我们原本定义的整数表达式也可以映射变化成为可变的整数表达式.
```Coq
Fixpoint ainj (a: aexp): aexp' :=
  match a with
  | ANum n        => ANum' (TNum n)
  | AId X         => AId' X
  | APlus a1 a2   => APlus' (ainj a1) (ainj a2)
  | AMinus a1 a2  => AMinus' (ainj a1) (ainj a2)
  | AMult a1 a2   => AMult' (ainj a1) (ainj a2)
  end.
```

当我们给出一个整数类型表达式, 我们希望把它当做可变类型时, 即希望写`a`而不用`ainj a`. 我们使用Coq的Coercion机制.

```Coq
Coercion ainj: aexp >-> aexp'.
Coercion binj: bexp >-> bexp'.

Module example.

Example coercion_ex: ainj (APlus (ANum 0) (ANum 1)) = APlus' (ANum' 0) (ANum' 1).

End example.
```

我们可以完成断言的语法树定义.

```Coq
Inductive Assertion : Type :=
  | AssnLe (t1 t2 : term)
  | AssnLt (t1 t2 : term)
  | AssnEq (t1 t2 : term)
  | AssnDenote (b: bexp')
  | AssnOr (P1 P2 : Assertion)
  | AssnAnd (P1 P2 : Assertion)
  | AssnImpl (P1 P2 : Assertion)
  | AssnNot (P: Assertion)
  | AssnExists (x: logical_var) (P: Assertion)
  | AssnForall (x: logical_var) (P: Assertion).

Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assert.
```

Based on these definitions, we are already able to write assertions and triples. 这里com可能是hoare的程序指令,也可能是指称的程序指令.

```Coq
Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion).
```

### Syntactic Substitution

当我们定义赋值语句的推理规则时我们必须要定义语法替换. 即把程序变量替换成一个表达式. 这是一个在语法树上的递归操作. 以可变整数类型表达式`aexp'`的替换为例, 这是一个相互递归定义.

```Coq
Fixpoint aexp_sub (X: var) (E: aexp') (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_sub X E t)
      (* 常数中可能包含逻辑变量, 也可能包含某个整数类型表达式的值 *)
    | AId' X' =>
         if Nat.eq_dec X X' (* 判断变量的编号是否相同 *)
         then E
         else AId' X'
    | APlus' a1 a2 => APlus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMinus' a1 a2 => AMinus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMult' a1 a2 => AMult' (aexp_sub X E a1) (aexp_sub X E a2)
    end
with term_sub (X: var) (E: aexp') (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x => TId x
    | TDenote a => TDenote (aexp_sub X E a) 
      (* 借用aexp的递归定义 *)
    | TPlus t1 t2 => TPlus (term_sub X E t1) (term_sub X E t2)
    | TMinus t1 t2 => TMinus (term_sub X E t1) (term_sub X E t2)
    | TMult t1 t2 => TMult (term_sub X E t1) (term_sub X E t2)
    end.
```

注意到, 在Assertion层面, 定义替换的操作是不显然的.

```Coq
Module Assertion_Sub_Attempt.

Fixpoint assn_sub (X: var) (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe (term_sub X E t1) (term_sub X E t2)
    | AssnLt t1 t2   => AssnLt (term_sub X E t1) (term_sub X E t2)
    | AssnEq t1 t2   => AssnEq (term_sub X E t1) (term_sub X E t2)
    | AssnDenote b   => AssnDenote (bexp_sub X E b)
    | AssnOr P1 P2   => AssnOr (assn_sub X E P1) (assn_sub X E P2)
    | AssnAnd P1 P2  => AssnAnd (assn_sub X E P1) (assn_sub X E P2)
    | AssnImpl P1 P2 => AssnImpl (assn_sub X E P1) (assn_sub X E P2)
    | AssnNot P      => AssnNot (assn_sub X E P)
    | AssnExists x P => AssnExists x (assn_sub X E P)
    | AssnForall x P => AssnForall x (assn_sub X E P)
    end.

End Assertion_Sub_Attempt.
```
> 自由出现与约束出现的逻辑变量
> - 没有受到量词约束的: free variable
> - 约束出现: bound variable
> 
> 在d中约束出现,而在E中自由出现的逻辑变量是不能直接替换的.

What's wrong? Consider the following substitution,
```Coq
(Exists x, {[X]} = x + 1) [X |-> x]
```
Theoretically, the correct substition result should be: 
```Coq
(Exists x, {[X]} = x + 1) [X |-> x]    ===>
(Exists y, {[X]} = y + 1) [X |-> x]    ===>
Exists y, {[x]} = y + 1.
```
我们要先重命名,再做替换. But the definition above says:
```Coq
(Exists x, {[X]} = x + 1) [X |-> x]    ===>
Exists x, {[x]} = x + 1
```
which does not make sense. The lesson that we learnt from this failure is that we need to define logical variable's renaming first. 

### Renaming Logical Variables

首先定义整数类型表达式、整数项、布尔类型表达式的重命名, 递归定义把x替换成y的操作.

```Coq
Fixpoint aexp_rename (x y: logical_var) (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_rename x y t)
    | AId' X => AId' X
    | APlus' a1 a2 => APlus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMinus' a1 a2 => AMinus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMult' a1 a2 => AMult' (aexp_rename x y a1) (aexp_rename x y a2)
    end
with term_rename (x y: logical_var) (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    | TDenote a => TDenote (aexp_rename x y a)
    | TPlus t1 t2 => TPlus (term_rename x y t1) (term_rename x y t2)
    | TMinus t1 t2 => TMinus (term_rename x y t1) (term_rename x y t2)
    | TMult t1 t2 => TMult (term_rename x y t1) (term_rename x y t2)
    end.
```

我们只对自由出现的变量进行重命名, 如果出现了约束出现的变量, 那么约束范围内的那个变量名就不再是我们想要替换的变量了.

```Coq
Fixpoint assn_rename (x y: logical_var) (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2    => AssnLe (term_rename x y t1) (term_rename x y t2)
    | AssnLt t1 t2    => AssnLt (term_rename x y t1) (term_rename x y t2)
    | AssnEq t1 t2    => AssnEq (term_rename x y t1) (term_rename x y t2)
    | AssnDenote b    => AssnDenote (bexp_rename x y b)
    | AssnOr P1 P2    => AssnOr (assn_rename x y P1) (assn_rename x y P2)
    | AssnAnd P1 P2   => AssnAnd (assn_rename x y P1) (assn_rename x y P2)
    | AssnImpl P1 P2  => AssnImpl (assn_rename x y P1) (assn_rename x y P2)
    | AssnNot P       => AssnNot (assn_rename x y P)
    | AssnExists x' P => if Nat.eq_dec x x'
(* 被替换的是约束变量 *)   then AssnExists x' P
(* 被替换的是自由变量 *)   else AssnExists x' (assn_rename x y P)
    | AssnForall x' P => if Nat.eq_dec x x'
                         then AssnForall x' P
                         else AssnForall x' (assn_rename x y P)
    end.
```

重命名策略: 求出最大编号+1. 定义`new_var`:

```Coq
Fixpoint aexp_max_var (a: aexp'): logical_var :=
    match a with
    | ANum' t => term_max_var t
    | AId' X => O
    | APlus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMinus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMult' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    end
with term_max_var (t: term): logical_var :=
    match t with
    | TNum n => O
    | TId x => x
    | TDenote a => aexp_max_var a
    | TPlus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMinus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMult t1 t2 => max (term_max_var t1) (term_max_var t2)
    end.

Definition new_var (P: Assertion) (E: aexp'): logical_var :=
  S (max (assn_max_var P) (aexp_max_var E)).
```

替换分两步走: 先做所有的重命名, 将`P`中所有子断言检验是否需要重命名. 再做`naive_sub`即上文的简单替换.

```Coq
Fixpoint aexp_occur (x: logical_var) (a: aexp'): nat :=
    match a with
    | ANum' t => term_occur x t
    | AId' X => O
    | APlus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMinus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMult' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    end
with term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TNum n => O
    | TId x' => if Nat.eq_dec x x' then S O else O
    | TDenote a => aexp_occur x a
    | TPlus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMinus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMult t1 t2 => (term_occur x t1) + (term_occur x t2)
    end.

Fixpoint rename_all (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe t1 t2
    | AssnLt t1 t2   => AssnLt t1 t2
    | AssnEq t1 t2   => AssnEq t1 t2
    | AssnDenote b   => AssnDenote b   (*保持不变*)
    | AssnOr P1 P2   => AssnOr (rename_all E P1) (rename_all E P2)
    | AssnAnd P1 P2  => AssnAnd (rename_all E P1) (rename_all E P2)
    | AssnImpl P1 P2 => AssnImpl (rename_all E P1) (rename_all E P2)
    | AssnNot P      => AssnNot (rename_all E P) (*递归定义*)
    | AssnExists x P => match aexp_occur x E with (*数出现次数*)
    (* x不出现, 直接递归 *)  | O => AssnExists x (rename_all E P)
    (* x出现, rename处理 *)  | _ => AssnExists
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    | AssnForall x P => match aexp_occur x E with
                        | O => AssnForall x (rename_all E P)
                        | _ => AssnForall
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    end.
```


```Coq
Definition assn_sub (X: var) (E: aexp') (P: Assertion): Assertion :=
  naive_sub X E (rename_all E P).

Notation "P [ X |-> E ]" := (assn_sub X E ((P)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a [ X |-> E ]" := (aexp_sub X E ((a)%vimp)) (at level 10, X at next level) : vimp_scope.
```

In logic text books, substitution in a quantifed assertion is defined as renaming first followed by recursive substitution. In formally,
```Coq
    (EXISTS x, P) [X |-> E]    ===>
    EXISTS y, P [x |-> y] [X |-> E]
```

### Hoare logic's Proof System

递归定义, 由下面这些规则可以推出的霍尔三元组是可证的.
```Coq
Module Attempt1.

Inductive provable: hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable ({{P}} c1 {{Q}}) ->
      provable ({{Q}} c2 {{R}}) ->
      provable ({{P}} c1;;c2 {{R}})
  | hoare_skip : forall P,
      provable ({{P}} Skip {{P}})
  | hoare_if : forall P Q (b: bexp) c1 c2,
      provable ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while : forall P (b: bexp) c,
      provable ({{ P AND {[b]} }} c {{P}}) ->
      provable ({{P}} While b Do c EndWhile {{ P AND NOT {[b]} }})
  | hoare_asgn_fwd : forall P (X: var) E (x: logical_var),
      provable (
        {{ P }}
        X ::= E
        {{ EXISTS x, P [X |-> x] AND
                     {[X]} = {[ E [X |-> x] ]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }}).
(*
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      P |-- P' ->
      provable ({{P'}} c {{Q'}}) ->
      Q' |-- Q ->
      provable ({{P}} c {{Q}}).
*)

End Attempt1.
```

我们发现, 我们还没有定义过assertion之间的推出关系.

一种办法, 把断言推导的一阶逻辑作为霍尔逻辑的参数.

```Coq
Module Attempt2.

Inductive provable (D: Assertion -> Assertion -> Prop): hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable D ({{P}} c1 {{Q}}) ->
      provable D ({{Q}} c2 {{R}}) ->
      provable D ({{P}} c1;;c2 {{R}})
  | hoare_skip : forall P,
      provable D ({{P}} Skip {{P}})
  | hoare_if : forall P Q (b: bexp) c1 c2,
      provable D ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable D ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable D ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while : forall P (b: bexp) c,
      provable D ({{ P AND {[b]} }} c {{P}}) ->
      provable D ({{P}} While b Do c EndWhile {{ P AND NOT {[b]} }})
  | hoare_asgn_fwd : forall P (X: var) E (x: logical_var),
      provable D (
        {{ P }}
        X ::= E
        {{ EXISTS x, P [X |-> x] AND
                     {[X]} = {[ E [X |-> x] ]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable D ({{ P [ X |-> E] }} X ::= E {{ P }})
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      D P P' -> (* P |-- P' *)
      provable D ({{P'}} c {{Q'}}) ->
      D Q' Q -> (* Q' |-- Q *)
      provable D ({{P}} c {{Q}}).

End Attempt2.
```

We use Coq's type class to turn on notations for assertion derivation.

```Coq
Class FirstOrderLogic: Type := {
  FOL_provable: Assertion -> Prop
}.

Definition derives {T: FirstOrderLogic} (P Q: Assertion): Prop :=
  FOL_provable (P IMPLY Q).

Notation "P '|--' Q" :=
  (derives ((P)%assert) ((Q)%assert)) (at level 90, no associativity).

Inductive provable {T: FirstOrderLogic}: hoare_triple -> Prop :=
(* ... *)
```

> 我们的霍尔三元组是否成立, 本质上定义的是能通过一个推理规则系统证明出来的性质. provable~可证. 
> A Hoare triple is called provable if we can prove it in the Hoare logic within finite steps. Thus, "provable" can be defined in Coq as an inductive predicate.


## Hoare Triples' Semantic Meaning Via Denotations

霍尔三元组的语义也可以用指称语义表达出来. 即`{{P}} c {{Q}}`中, 符合P,Q的有序对`st,st'`在`c`的指称中.

注意: 断言P当中,除了程序状态变量外, 还包含了**自由出现的逻辑变量**, 因此它们也描述了逻辑变量值的性质. 因此, 我们需要引入指派这一概念. Thus, when we define the satisfaction relation, it is a relation between program states and assertions under a specific assignment (指派) of logical variables.
```Coq
Definition Lassn: Type := logical_var -> Z.

Definition Lassn_update (La: Lassn) (x: logical_var) (v: Z): Lassn :=
  fun y => if (Nat.eq_dec x y) then v else La y.
```
In summary, an interpretation (解释) of program variables and logical variables is a pair of program state and logical variable assignment. 解释是程序状态与逻辑变量指派的二元组. 定义解释是否符合一个断言.

```Coq
Definition Interp: Type := state * Lassn.

Definition Interp_Lupdate (J: Interp) (x: logical_var) (v: Z): Interp :=
  (fst J, Lassn_update (snd J) x v).

(** We first define the meaning (or the denotations) of variable expressions.*)

(* 整数项/表达式在一个解释上的值 *)
Fixpoint aexp'_denote (J: Interp) (a: aexp'): Z :=
    match a with
    | ANum' t => term_denote J t
    | AId' X => (fst J) X
    | APlus' a1 a2 => aexp'_denote J a1 + aexp'_denote J a2
    | AMinus' a1 a2 => aexp'_denote J a1 - aexp'_denote J a2
    | AMult' a1 a2 => aexp'_denote J a1 * aexp'_denote J a2
    end
with term_denote (J: Interp) (t: term): Z :=
    match t with
    | TNum n => n
    | TId x => (snd J) x
    | TDenote a => aexp'_denote J a
    | TPlus t1 t2 => term_denote J t1 + term_denote J t2
    | TMinus t1 t2 => term_denote J t1 - term_denote J t2
    | TMult t1 t2 => term_denote J t1 * term_denote J t2
    end.

Fixpoint bexp'_denote (J: Interp) (b: bexp'): Prop :=
    match b with
    | BTrue' => True
    | BFalse' => False
    | BEq' a1 a2 => aexp'_denote J a1 = aexp'_denote J a2
    | BLe' a1 a2 => (aexp'_denote J a1 <= aexp'_denote J a2)%Z
    | BNot' b => ~ bexp'_denote J b
    | BAnd' b1 b2 => bexp'_denote J b1 /\ bexp'_denote J b2
    end.

Fixpoint satisfies (J: Interp) (d: Assertion): Prop :=
    match d with
    | AssnLe t1 t2 => (term_denote J t1 <= term_denote J t2)%Z
    | AssnLt t1 t2 => (term_denote J t1 < term_denote J t2)%Z
    | AssnEq t1 t2 => (term_denote J t1 = term_denote J t2)%Z
    | AssnDenote b => bexp'_denote J b
    | AssnOr P1 P2 => (satisfies J P1) \/ (satisfies J P2)
    | AssnAnd P1 P2 => (satisfies J P1) /\ (satisfies J P2)
    | AssnImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | AssnNot P => ~ (satisfies J P)
    | AssnExists x P => exists v, satisfies (Interp_Lupdate J x v) P
    (* 对解释做修改之后, P成立. *)
    | AssnForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.
```


逻辑上, 我们一般使用$\models$表示满足关系

```Coq
Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity).
```

霍尔三元组"有效"的定义 (可证:针对推理系统, 满足/有效:语义上的概念)
```Coq
Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q =>
      forall La st1 st2,
        (st1, La) |== P  (* 起始状态解释满足P *)
        -> ceval c st1 st2  (* 存在终止状态 *)
        -> (st2, La) |== Q  (* 终止状态解释满足Q *)
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).
```

Traditionally, a single turnstile $\vdash$ is used to represent a proof-theory related concept, like "provable" and "derivable". But a double turnstile $\models$ is used to represent a semantic concept like "satisfaction relation", "valid" and "consequence relation".


## Hoare Logic Versus Denotational Semantics

霍尔逻辑推理系统中一个霍尔三元组是否可证, 与指称语义定义的一个霍尔三元组是否有效, 我们现在有两种方式定义一个霍尔三元组是否"成立".

```Coq
Definition hoare_sound (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |-- {{ P }} c {{ Q }} ->
    |== {{ P }} c {{ Q }}. (*可靠性:所有可证的都有效?*)

Definition hoare_complete (T: FirstOrderLogic): Prop :=
  forall P c Q,
    |== {{ P }} c {{ Q }} ->
    |-- {{ P }} c {{ Q }}. (*完备性:所有有效的都可证?*)
```

Remember, we are not talking about one Hoare logic but a series of Hoare logics. Every different first order logic for assertion derivation defines a different Hoare logic. Thus, we would ask more specifically: for what kind of assertion derivation logics, their corresponding Hoare logics are sound and complete? A short answer is:
- if the assertion derivation logic is sound, the corresponding Hoare logic is sound;
- if the assertion language is expressive enough and the assertion derivation logic is complete, the corresponding Hoare logic is complete.