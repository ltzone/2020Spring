---
title: 【Programming Language】Denotational Semantics 3
url: pl-deno3
date: 2020-03-31 14:02:09
tags: 
- Programming Language

categories: 
- Courses

---

Week 5 of 2020 Spring.

<!--more-->

[toc]

## Review: Programs Denotaton

我们用**状态的二元关系表达程序的语义** (defined by `ceval (c:com):state -> state -> Prop`)

```Coq
Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (intersection then_branch (filter1 (beval b)))
    (intersection else_branch (filter1 (beval (BNot b)))).
```

```Coq
Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile _ _ => empty
  end.
```
引入记号帮助理解.
```Coq
Notation "'The_pair_(' st1 , st2 ')_is_in_{[' c  ]}" := (ceval c st1 st2) (at level 45, no associativity).
```

将高阶的定义展开, 我们可以得到以下定义:
```Coq
Lemma ceval_skip: forall st1 st2,
  The_pair_( st1 , st2 )_is_in_{[ Skip ]} <->
  st1 = st2.

Lemma ceval_seq: forall st1 st3 c1 c2,
  The_pair_( st1 , st3 )_is_in_{[ c1;; c2 ]} <->
  exists st2,
    The_pair_( st1 , st2 )_is_in_{[ c1 ]} /\
    The_pair_( st2 , st3 )_is_in_{[ c2 ]}.

Lemma ceval_if: forall st1 st2 b c1 c2,
  The_pair_( st1 , st2 )_is_in_{[ If b Then c1 Else c2 EndIf ]} <->
  The_pair_( st1 , st2 )_is_in_{[ c1 ]} /\ beval b st1 \/
  The_pair_( st1 , st2 )_is_in_{[ c2 ]} /\ ~ beval b st1.
```

## Loop's Denotations

`While b Do c EndWhile`如何理解?两种:
1. 先检查`b`的真值, 如果为假则什么都不做, 如果为真则执行`c`,在重新执行`While b Do c EndWhile`
2. 循环体恰好被执行了0,1,2,...若干次, 次数由`b`和`c`共同决定.

在这里我们采用第二种, 因为第一种采用了循环定义的方式. `c;; While b Do c EndWhile`. 我们可以用定义2证明符合1的性质.

我们对自然数做递归定义. (先定义一个辅助概念: 恰好循环n次)
```Coq
Fixpoint iter_loop_body (b: bexp)
                        (loop_body: state -> state -> Prop)
                        (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         intersection
           id  (* 前后状态不变 *)
           (filter1 (beval (BNot b))) 
           (* 前状态中b的eval值为假 filter把state的集合变成state的二元关系*)
  | S n' =>
            intersection
              (concat
                loop_body
                (iter_loop_body b loop_body n'))
              (filter1 (beval b))
    (* 考虑n'+1次, 相当于第一次的起始状态符合布尔表达式为真, 再执行1次, 在执行n'次*)
  end.
```

我们再引入一个高阶的定义, 用`rs`表示一个二元关系可数列, 取他们的并集.
```Coq
Definition omega_union {A B: Type} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.
```

用`omega_union`定义循环体语义.
```Coq
Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  omega_union (iter_loop_body b loop_body).
```

定义程序的语义
```Coq
Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (intersection then_branch (filter1 (beval b)))
    (intersection else_branch (filter1 (beval (BNot b)))).

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.
```

我们避开`filter`和`intersection`的混用, 定义一个`test_rel`, 类似`filter`和`id`的交集

```Coq
Definition test_rel {A} (X: A -> Prop): A -> A -> Prop :=
  fun st1 st2 => st1 = st2 /\ X st1.
```
由此写出if和循环的定义, 类似把"如果"抽象成一步. 和后面的语句concat起来
```Coq
Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (concat (test_rel (beval b)) then_branch)
    (concat (test_rel (beval (BNot b))) else_branch).

Fixpoint iter_loop_body (b: bexp)
                        (loop_body: state -> state -> Prop)
                        (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         test_rel (beval (BNot b))
  | S n' =>
         concat
           (test_rel (beval b)) (* 先检查 *)
           (concat
              loop_body         (* 再执行 *)
              (iter_loop_body b loop_body n'))
  end.
```

```Coq
Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop):
  state -> state -> Prop :=
  omega_union (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.
```

> Coq证明中, 我们尽量不用`simpl.`化简`ceval`. 我们一般使用`rewrite`进行化简.

```Coq
Lemma ceval_CSkip: ceval CSkip = id.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CAss: forall X E,
  ceval (CAss X E) =
    fun st1 st2 =>
      st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y.
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CSeq: forall c1 c2,
  ceval (c1 ;; c2) = concat (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CIf: forall b c1 c2,
  ceval (CIf b c1 c2) = if_sem b (ceval c1) (ceval c2).
Proof. intros. simpl. reflexivity. Qed.

Lemma ceval_CWhile: forall b c,
  ceval (While b Do c EndWhile) = loop_sem b (ceval c).
Proof. intros. simpl. reflexivity. Qed.
```

## Application of Denotational Semantics

```
While true Do X::= X + 1 EndWhile
```
如何说明不终止?
1. by Hoare, `{{True}} c {{False}}` holds
2. by denoation, `ceval c` is empty.

说明程序终止? Hoare fails, 用指称语义: $\forall$ st1, $\exists$ st2 s.t. `ceval c st1 st2`.


## Semantic Equivalence

### An Equivalence Between Integer Expressions

基于高阶理解, 重新定义等数之间的表达式.

- Recall Two expressions `a1` and `a2` are equivalent if evaluating them on `st` has the same result for every program state `st`.
我们可以同样用高阶函数写出
- Two expressions `a1` and `a2` are equivalent if their denotations are equivalent functions

```Coq
Definition aexp_equiv (a1 a2: aexp): Prop :=
  Func.equiv (aeval a1) (aeval a2).
```

等价关系的定义可以由`Func.equiv`的等价性推出.

Moreover, it is a congruence (同余关系:两个大的表达式的等价性可以有局部的等价性推出). 表达式的运算也保持等价性. That is, the equivalence of two subexpressions implies the equivalence of the larger expressions in which they are embedded.

The main idea is that the congruence property allows us to replace a small part of a large expression with an equivalent small part and know that the whole large expressions are equivalent without doing an explicit proof about the non-varying parts — i.e., the **"proof burden"** of a small change to a large expression is proportional to the size of the change, not the expression.

可以由`Func.equv`的性质推出.

### An Equivalence Between Boolean Expressions

```Coq
Definition bexp_equiv (b1 b2: bexp): Prop :=
  Sets.equiv (beval b1) (beval b2).
```

### An Equivalence Between Programs

For program equivalence, we need to define equivalence between relations first.

```Coq
Definition equiv {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b <-> r2 a b.

Definition le {A B: Type} (r1 r2: A -> B -> Prop): Prop :=
  forall a b, r1 a b -> r2 a b.
```

同样可以证明等价性, test_rel, concat, union的congruence性质

对omega_union的congruence, 我们证明"对应"等价保持等价关系
```
Lemma Rel_equiv_omega_union: forall A B (r1 r2: nat -> A -> B -> Prop),
  (forall n, Rel.equiv (r1 n) (r2 n)) ->
  Rel.equiv (omega_union r1) (omega_union r2).
```

完成以上高阶定义和证明后, 我们就可以将两个程序指称相同定义为程序的等价.
```
Definition com_equiv (c1 c2: com): Prop :=
  Rel.equiv (ceval c1) (ceval c2).
```

### loop_unrolling

recall 两种while的语义. 我们尝试证明等价性. 
```Coq
Theorem loop_unrolling : forall b c,
  com_equiv
    (While b Do c EndWhile)
    (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf).
Proof.
  intros.
  unfold com_equiv.
(*
  Rel.equiv (loop_sem b (ceval c))
  (if_sem b (concat (ceval c) (loop_sem b (ceval c))) id)
*)
  Abort.


Lemma loop_sem_unrolling: forall b (R: state -> state -> Prop),
  Rel.equiv (loop_sem b R) (if_sem b (concat R (loop_sem b R)) id).

Theorem loop_unrolling : forall b c,
  com_equiv
    (While b Do c EndWhile)
    (If b Then (c ;; While b Do c EndWhile) Else Skip EndIf).
Proof.
  intros.
  unfold com_equiv.
  rewrite ceval_CIf, ceval_CSeq, ceval_CSkip.
  rewrite ceval_CWhile.
  apply loop_sem_unrolling.
Qed.
```

Note: `loop_unrolling`也是一个重要的编译优化.

## Bourbaki-Witt Theorem

不动点是定义循环语义的一种普遍方式. For $f: X \mapsto X$, $x\in X$ is a fixpoint of $f$ when $x = f(x)$. 我们证明的等价性本质是这样一个等式
```
X = (if_sem b (concat R X) id) .
```
此外, 这也是该变换的最小不动点. i.e. 循环语义是根据符合该二元关系的最小不动点定义的.


### Partial Order

A partial order (偏序) on a set $A$ is a binary relation $R$ (usually written as ≤) which is reflexive (自反), transitive (传递), and antisymmetric (反对称). Formally,

$$
\begin{array}{l}
  \forall x\in A, x \le x; \\
  \forall x,y,z \in A, x \le y \rightarrow y \le z x \le z ; \\
  \forall x,y \in A, x \le y \rightarrow y\le x \rightarrow x = y.
\end{array}
$$

此外,还要有最小元性质
$$\forall x\in A, bot \le x$$
i.p. for 二元关系, 空关系就是它的最小元.

### Chain

A subset of elements in A is called a chain w.r.t. a partial order $\le$ if any two elements in this subset are comparable. 考虑自然数之间的二元关系, 集合之间的包含关系, 但我们总能选出一列. For example, if a sequence xs: nat → A is monotonically increasing:

$$\forall n \in N, xs(n) \le xs(n+1)$$

A partial order ≤ is called complete if every chain has its least upper bound lub and greatest lower bound glb. In short, the set A (companied with order ≤) is called a complete partial ordering, CPO (完备偏序集). 偏序关系的任何一条链都有上确界就是一个完备集. Some text books require chains to be nonempty. We do not put such restriction on chain's definition here. Thus, the empty set is a chain. Its least upper bound is the least element of A, in other words, bot.

自然数上的大小关系不是完备偏序列.
集合的包含关系是完备偏序集. (任意一群集合链的并集,就是最小上确界). 类似, 二元关系也是完备偏序集.

### Monotonic and Continuous Functions
Given two CPOs $A$, $\le_{A}$ and $B$, $\le_{B}$, a function $F: A \rightarrow B$ is called monotonic (单调) if it preserves order. Formally,
$$\forall x,y\in A, x\le_{A} y \rightarrow F(x) \le_{B} F(y) $$

A function $F: A \rightarrow B$ is called continuous (连续) if it preserves $\text{lub}$. Formally,
$$\forall xs \in \text{chain}(A), \text{lub}(F(xs)) = F(\text{lub}(xs))$$
Here, the $\text{lub}$ function on the left hand side means the least upper bound defined by $B$ and the one on the right hand side is defined by $A$.
The definition of continuous does not require the preservation of $\text{glb}$ becasue CPOs are usually defined in a direction that larger elements are more defined .


### Least fixpoint
Given a CPO A, we can always construct a sequence of elements as follows:
```
bot, F(bot), F(F(bot)), F(F(F(bot))), ...
```

Obviously, `bot <= F(bot)` is true due to the definition of `bot]. If `F` is
monotonic, it is immediately followed by `F(bot) <= F(F(bot))`. Similarly,

    F(F(bot)) <= F(F(F(bot))), F(F(F(bot))) <= F(F(F(F(bot)))) ...

In other words, if `F` is monotonic, this sequence is a chain.

Main theorem: given a CPO `A`, if it has a least element, then every monotonic
continuous function `F` has a fixpoint and the least fixpoint of `F` is:

    lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...].

Proof.

On one hand, this least upper bound is a fixpoint:

    F (lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...]) =
    lub [F(bot), F(F(bot)), F(F(F(bot))), F(F(F(F(bot)))), ...] =
    lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...].

The first equality is true because `F` is continuous. The second equality is
true because `bot` is less than or equal to all other elements in the sequence.

On the other hand, this fixpoint is the least one. For any other fixpoint `x`,
in other words, suppose `F(x) = x`. Then,

    bot <= x

Thus,

    F(bot) <= F(x) = x

due to the fact that `F` is monotonic and `x` is a fixpoint. And so on,

    F(F(bot)) <= x, F(F(F(bot))) <= x, F(F(F(F(bot)))) <= x, ...

That means, `x` is an upper bound of `bot, F(bot), F(F(bot)), ...`. It must be
greater than or equal to

    lub [bot, F(bot), F(F(bot)), F(F(F(bot))), ...].

QED.

我们完成了最小不动点的证明, 下面我们说明
```
X = (if_sem b (concat R X) id) .
```
存在最小不动点

### Denotation of Loops as Bourbaki-Witt Fixpoint
Our definition `loop_sem` is actually a Bourbaki-Witt fixpoint of the recursive equation defined by `loop_sem_unrollong`. In this case, set `A` is the set of binary relations between program stats, i.e. `A := state -> state -> Prop`.
The equivalence relation defined on `A` is `Rel.equiv`. The partial order defined on `A` is the subset relation, i.e. `Rel.le`. This partial ordering is a CPO. The least upper bound, $\text{lub}$, of a chain is the union of all binary relations in the chain. **Specifically, `omega_union` defines the lub of a sequence of relations.**
In the end, the function that maps `X` to `if_sem b (concat R X) id)` is monotonic and continuous. And `loop_sem` is exactly the Bourbaki-Witt fixpoint of this function.

- 单调性: `if_sem`,`concat`保持`Rel.le`性质
- 连续型: `concat`、`union`等都能保持连续性