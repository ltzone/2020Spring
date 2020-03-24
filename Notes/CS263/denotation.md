---
title: 【Programming Language】Denotational Semantics
url: pl-deno
date: 2020-03-24 14:00:23
tags: 
- Programming Language

categories: 
- Courses

---

Week 4 of 2020 Spring. 指称语义

**KeyWords**: 

<!--more-->

[toc]

霍尔逻辑定义的是针对一类起始状态、一类中止状态进行讨论。本节介绍的指称语义针对一个固定的起始状态和一个固定的中止状态之间的关系。未来我们介绍的小步语义定义的是程序过程中发生的事情，更接近于编译器的实现。三种语义的颗粒度从大到小。

## Expression Evaluation

Recall 整数表达式的语法树
```
a ::= Z
    | var
    | a + a
    | a - a
    | a * a
```
我们在霍尔逻辑中描述的是表达式符合的性质，我们在指称语义中，我们需要定义对给定的程序状态`st`（变量名到值的函数），问表达式`a`的值是什么。

表达式`a`具有树形结构（语法树），因此我们可以根据树结构将求值函数进行递归定义。我们在Coq中严谨地写出。
```Coq
Variable st: state.

Fixpoint aeval (a : aexp) : Z :=
  match a with
  | ANum n -> n
  | AId X -> st X (st是程序状态：id->Z)
  | APlus a1 a2 -> (aeval a1) + (aeval a2)
  | AMinus a1 a2 -> (aeval a1) - (aeval a2)
  | AMult a1 a2 -> (aeval a1) * (aeval a2)
  end.
```

我们定义了整数表达式求值。

## Expression Equivalence

在任何程序状态上，两个表达式的值都相等，那么两个表达式等价。
```Coq
Definition aexp_equiv (a1 a2: aexp): Prop :=
  forall st, aeval st a1 = aeval st a2.

Declare Scope DSem.
Local Open Scope DSem.

Notation "a1 '=a=' a2" :=
  (aexp_equiv (a1:aexp) (a2:aexp)) (at level 69, no associativity): DSem.
```

## Inductive types and recursive functions

recall 关于整数表达式的求值我们是**递归定义**的，有时证明时我们需要对递归函数作证明，一个常用的方法是**归纳证明**。

我们可以定义一棵二叉树
```Coq
Inductive tree: Type :=
| Leaf: tree
| Node (l: tree) (v: Z) (r: tree): tree.
```
我们可以定义树到数的函数
```Coq
Fixpoint tree_height (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => Z.max (tree_height l) (tree_height r) + 1
  end.
Fixpoint tree_size (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => tree_size l + tree_size r + 1
  end.
```

我们可以定义树的翻转操作，树到树的函数。
```Coq
Fixpoint tree_reverse (t: tree): tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_reverse r) v (tree_reverse l)
  end.
```

### Structure Induction
对二叉树进行结构归纳法。如果我们要证明性质P对所有二叉树成立
- P对所有空树成立
- P对所有的`Node l v r`成立，如果P对`l`成立且P对`r`成立能推出。

我们也可以递归地定义性质。
```Coq
Fixpoint tree_ele_le (ub: Z) (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => tree_ele_le ub l /\ k <= ub /\ tree_ele_le ub r
  end.

Fixpoint tree_ele_ge (lb: Z) (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => tree_ele_ge lb l /\ k >= lb /\ tree_ele_ge lb r
  end.
```

我们还可以基于递归的性质定义其他性质。如二叉树符合从左到右，从小到大的二叉查找性质。

```Coq
Fixpoint low2high (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => low2high l /\ l <== k /\ r >== k /\ low2high r
  end.

Fixpoint high2low (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => high2low l /\ l >== k /\ r <== k /\ high2low r
  end.
```

我们用归纳证明如下引理。
```Coq
Lemma reverse_low2high: forall t,
  low2high t ->
  high2low (tree_reverse t).
```

归纳证明中，我们发现需要证明有关上下界的性质

```Coq
Lemma reverse_le: forall n t,
  t <== n -> tree_reverse t <== n.
Lemma reverse_ge: forall n t,
  t >== n -> tree_reverse t >== n.
```
如果我们的所有证明都是命题推理，可以用`tauto`证明。

### Case analysis

```Coq
Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
```
分类讨论
- t若是空树，discriminate
- t若非空，化简前提后，我们会得到
```Coq
H: Node (tree_reverse t2') v (tree_reverse t1') = Node t1 k t2
```
`rewrite`后跟`!`表示多次改写。
```Coq
injection H as ? ? ?.
rewrite <- H, <- H0, <- H1.
rewrite ! reverse_involution.
```

### Strengthing an Induction Hypothesis

我们看一个nontrivial的归纳法证明。Coq支持同时对两个变量进行pattern_matching. 用不到的参数可以用下划线表示，下面的性质用递归的方法描述了两个二叉树有相同的结构。

```Coq
Fixpoint same_structure (t1 t2: tree): Prop :=
  match t1, t2 with
  | Leaf, Leaf => True
  | Leaf, Node _ _ _ => False
  | Node _ _ _, Leaf => False
  | Node l1 _ r1, Node l2 _ r2 => same_structure l1 l2 /\ same_structure r1 r2
  end.
```

尝试证明这个性质
```Coq
Lemma same_structure_same_height: forall t1 t2,
  same_structure t1 t2 ->
  tree_height t1 = tree_height t2.
```
产生了这样的IH
```Coq
H: same_structure (Node t1_1 v t1_2) t2
IHt1_1: same_structure t1_1 t2 -> tree_height t1_1 = tree_height t2
IHt1_2: same_structure t1_2 t2 -> tree_height t1_2 = tree_height t2
```
这里关于t1的性质其实是在说，**对于给定的t2**，如果t1左右子树和这个给定的t2有same structure,那么t1和t2有same height.

我们希望性质中，t2是任意的。`revert t2 H.`


## Analyzing Syntax Trees

定义aexp的长度（运算次数）
```Coq
Fixpoint alength (a : aexp) : Z :=
  match a with
  | ANum n => 1
  | AId X => 1
  | APlus a1 a2 => (alength a1) + (alength a2) + 1
  | AMinus a1 a2  => (alength a1) + (alength a2) + 1
  | AMult a1 a2 => (alength a1) + (alength a2) + 1
  end.
```

### Constant-Folding Transformation

可以想象， 这是编译优化的工作。比如我们在代码中写4*100，编译器在编译时就可以直接写400。
```Coq
Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | APlus a1 a2  =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | ANum n1, ANum n2 => ANum (n1 + n2)
    | _, _ => APlus (fold_constants_aexp a1) (fold_constants_aexp a2)
    end
  | AMinus a1 a2 =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | ANum n1, ANum n2 => ANum (n1 - n2)
    | _, _ => AMinus (fold_constants_aexp a1) (fold_constants_aexp a2)
    end
  | AMult a1 a2  =>
    match fold_constants_aexp a1, fold_constants_aexp a2 with
    | ANum n1, ANum n2 => ANum (n1 * n2)
    | _, _ => AMult (fold_constants_aexp a1) (fold_constants_aexp a2)
    end
  end.
```

我们要证明这样的操作是合法的，只需证明 by `induction a`.
```Coq
Theorem fold_constants_aexp_sound : forall a,
  fold_constants_aexp a =a= a.
```

我们还可以证明，编译优化不会把问题弄得更糟，即化简之后的程序长度会更短。
```Coq
Lemma fold_constants_aexp_improve : forall a,
  alength (fold_constants_aexp a) <= alength a.
```

### 32-bit Evaluation
虽然简单的程序语言是没有边界的，但我们仍然可以探讨表达式的求值过程是否在边界范围内。即a本身结果在范围内，它内部子表达式的所有结果都在32位之内。

定义这一命题
```Coq
Definition max32: Z := 2^31 -1.
Definition min32: Z := - 2^31.

Fixpoint signed32_eval (st: state) (a: aexp): Prop :=
  min32 <= aeval st a <= max32 /\
  match a with
  | ANum n => True
  | AId X => True
  | APlus a1 a2 => signed32_eval st a1 /\ signed32_eval st a2
  | AMinus a1 a2  => signed32_eval st a1 /\ signed32_eval st a2
  | AMult a1 a2 => signed32_eval st a1 /\ signed32_eval st a2
  end.
```

我们可以证明常数folding后，如果化简前可以保证32位，化简后也能保证32位（反之非然）。
```Coq
Lemma fold_constants_aexp_signed32: forall st a,
  signed32_eval st a ->
  signed32_eval st (fold_constants_aexp a).
```

