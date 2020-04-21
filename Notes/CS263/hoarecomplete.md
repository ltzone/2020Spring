---
title: 【Programming Language】Completeness of Hoare Logic
url: pl-hoarecomplete
date: 2020-04-21 14:25:10
tags: 
- Programming Language

categories: 
- Courses

---

Week 8 of 2020 Spring

<!--more-->

[toc]

Recall:
- 可证：可以由推理规则推出
- 有效：前后条件满足指称语义，（由于可能存在逻辑变量，引入前后一致的指派）

若可证，则有效（soundness）
若有效，则可证（complete）

## Weakest Precondition

### Definition

我们首先引入一阶逻辑的有效性的定义，以及最弱前条件的定义。

```Coq
Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition wp' (P: Assertion) (c: com) (Q: Assertion): Prop :=
  (|== {{ P }} c {{ Q }}) /\
  (forall P', (|== {{ P' }} c {{ Q }}) -> FOL_valid  (P' IMPLY P)).
```

一个条件是最弱前条件，if：它是**有效的前条件**，且它是最弱的（对任意其他有效的P’，那么P’比P强）。

如果我们证明了c和Q的最弱前条件都可证，那么我们就证明了completeness，（因为可以其他任意前条件都可以由consequence rule推出）

在接下来的证明中，我们还会用到最弱前条件的一个等价定义（原定义没有说出怎样的指派、怎样的程序状态会满足最弱前条件），最弱前条件=“某一个状态和指派的集合满足最弱前条件”。

```Coq
Definition wp (P: Assertion) (c: com) (Q: Assertion): Prop :=
  forall st La,
    (st, La) |== P <->
    (forall st', ceval c st st' -> (st', La) |== Q).
```

### Equivalent between two definitions of Weakest Precondition

这两个定义是不是一样的？是的，我们今天暂时证明`wp P -> wp' P`。
```Coq
Lemma wp_wp': forall P c Q,
  wp P c Q -> wp' P c Q.
Proof.
  intros.
  unfold wp in H; unfold wp'.
  split.
  (* 定义2的任意P，确实是使霍尔三元组有效的一个前条件。 *)
  + unfold valid.  (* |== {{P}} c {{Q}} defined by denotation, trivial *)
    intros.
    specialize (H st1 La).
    firstorder.
  (* 定义2的任意P，确实是使霍尔三元组最弱前条件。
     idea: 对任意指派，要么成立，要么不成立 *)
  + intros.
    unfold FOL_valid; simpl.
    intros.
    destruct J as [st La].
    rewrite H.
    unfold valid in H0. (* H0 说的是 |== {{P'}} c {{Q}}，展开是一样的 *)
    specialize (H0 La st). (* 代入given arbitrary variable *)
    pose proof classic ((st, La) |== P').
    destruct H1; [right | left; exact H1].
    firstorder.
Qed.
```

### Roadmap

Work to be Done:
```Coq
Definition expressive: Prop := (* 最弱前条件存在 *)
  forall c Q, exists P, wp P c Q.

Definition wp_provable (T: FirstOrderLogic): Prop :=
  (* 最弱前条件构成的三元组可证 *)
  forall P c Q, wp P c Q -> |-- {{ P }} c {{ Q }}.
```

如果以上两点成立+一阶逻辑的完全性，我们就可以得到霍尔逻辑的完全性。
```
Proposition Hoare_complete_main_proof: forall T: FirstOrderLogic,
  expressive ->
  wp_provable T ->
  FOL_complete T ->
  hoare_complete T.
```

## Proof of Expressiveness

Recall：看待断言的方式：语法树/符合命题的程序状态集合。如果用后者看待断言，那expressive是必然成立的，directly from wp definition。为了证明的完整性，我们本节看作语法树，对表达力进行证明。相比之下，上文给出的第二个命题是更核心的内容。

By induction over the syntax tree of c.

### Skip

Let `P` be `Q`. Then for given `st` and `La`, it is obvious that `(st, La) |== P` is equivalent to
```Coq
forall st', ceval c st st' -> (st, La) |== Q
```
since `c = Skip` and `P = Q`.

### Assignment

Recall：语法替换本质上等于程序状态做替换。显然的。

### Sequence

IH1: for any assertion `Q`, there is another assertion `P` such that `wp P c1 Q`.
IH2: for any assertion `Q`, there is another assertion `P` such that `wp P c2 Q`.

构造：针对给定的Q，先由IH2找P1，再由IH1根据P1找P2。P2就是了。

是不是后半部分最弱前条件的最弱前条件就是整个sequence的最弱前条件？是的：
```Coq
(st, La) |== P iff for any st', if ceval c1 st st', then (st', La) |== Q0;
(st, La) |== Q0 iff for any st', if ceval c2 st st', then (st', La) |== Q.
----------------
(st, La) |== P iff for any st' st'',
    if ceval c1 st st' and ceval c2 st' st'', then (st'', La) |== Q.
```

### If, else

IH1: for any assertion `Q`, there is another assertion `P` such that `wp P c1 Q`.
IH2: for any assertion `Q`, there is another assertion `P` such that `wp P c2 Q`.

构造：`(P1 /\ b) \/ (P2 /\ ~ b)`，与顺序执行十分类似。

### While

较为困难：一部分原因，我们的断言太简单了，能说（构造）的东西太少了，难以构造。理论>实际。

IH: for any assertion `Q'`, there is another assertion `P'` such that `wp P' c1 Q'`


```Coq
(st(0), La) |== P if and only if
  for any natural number n,
    for any program states st(1), ..., st(n),
    if for any 0 <= i < n,
          (A) beval b st(i)
          (B) ceval c1 st(i) st(i+1)
          (* st0 -> st1 -> b -> st2 -> ... -> st_n *)
    then either (beval b st(n)) or (st(n), La) |== Q.
    (* 对 st_n 要么还能跑（布尔成立），要么终止了，满足后条件Q *)
```

某种意义上，后半部分就是一个断言了（关于程序状态的命题），但我们目前断言的语法树是说不出来的，如第二个forall的个数是由n决定的。更核心的问题是，`ceval c1 st(i) st(i+1)`是一个高阶描述。因此，我们要把上面的描述转换成我们需要构造的断言。我们先做下面这一步的转化。

注意到：后条件Q和程序c中，涉及到的程序变量只有有穷多个。假设它们是$x_1,x_2,\ldots,x_m$。那我们就可以改成，对任意的$n\times m$个整数，下述性质成立

```Coq
for any natural number n,
  for any integers x(0,1), x(0,2), ..., x(0,m),
                    x(1,1), x(1,2), ..., x(1,m),
                    x(2,1), x(2,2), ..., x(2,m),
                    ...
                    x(n,1), x(n,2), ..., x(n,m),
  if
  (1) {[ X1 ]} == x(0,1) AND ... AND {[ Xm ]} == x(0, m) AND (* 初始状态的赋值 *)
  (2) for any i, if 0 <= i < n, then                         (* 对其他状态 *)
        (2.1) b [ X1 |-> x(i, 1); ...; Xm |-> x(i, m) ]      
             (* 完成赋值替换后，布尔条件成立，此时b上不再具有程序变量了 *)
        (2.2) IH(X1 = x(i + 1, 1) AND ... AND Xm = x(i + 1, m)) 
              (* 首先，i+1状态上赋值吻合，应用IH（最弱前条件断言 *)
                [ X1 |-> x(i, 1); ...; Xm |-> x(i, m) ]
              (* 在这个最弱前条件断言上，替换成i状态的取值，那么成立 *)
        (2.3) NOT IH(False) [ X1 |-> x(i, 1); ...; Xm |-> x(i, m) ]
              (* 以False（不终止）作为后条件，使得循环体本身不终止的
                 那些起始状态的集合，经过i状态的赋值后条件不成立 *)
  then either
  (3) b [ X1 |-> x(n, 1); ...; Xm |-> x(n, m) ]; or
  (4) Q [ X1 |-> x(n, 1); ...; Xm |-> x(n, m) ].
```

上文虽然是informal definition，但全部都是语法替换、IH构造、NOT等，只剩一件事，即forall的长度和n有关。技术上，我们可以用Godel Beta Predicate（用任意整数刻画任意整数序列）完成这件事。


### Godel Beta Predicate

The Godel beta predicate `Beta(a,b,i,x)` is defined as:

    x = a mod (1 + (i+1) * b)

According to The Chinese remainder theorem, for any natural number `n` and natural number sequence `x(0)`, `x(1)`, ..., `x(n)`, there always exist `a` and `b` such that for any `0 <= i <= n`,

    Beta(a, b, i, y) if and only if y = x(i).

That means, any quantification over sequences can be represented by a combination of a fixed number of normal quantification and the Godel beta predicate. For example, the following two statement are equivalent:

    for any natural numbers n, x(0), x(1), ..., x(n),
      if for any i, 0 <= i < n, x(i) <= x(i+1) holds,
      then x(n) satisfies property R

and

    for any natural numbers n, a, b,
      if:
         for any i, x and x',
           if 0 <= i < n, Beta(a, b, i, x) and Beta(a, b, i+1, x')
           then x < x'
      then:
         for any x,
           if Beta(a, b, n, x) then x satisfies property P.

Using this method, we can easily state loops' weakest preconditions in our assertion language.

This proves the expressiveness lemma.


## Establishing Triples With Weakest Precondtions

如果P是c,Q的最弱前条件，（最弱前条件必须等价，但不一定唯一），那么`{{P}} c {{Q}}`是可证的。我们现在证明的是所有最弱前条件对应的霍尔三元组可证，而不是我们刚刚构造的最弱前条件。归纳

### Skip

If `P` is a weakest precondition of `c` and `Q`, we know that `P` is actually equivalent with `Q`. Q也是最弱前条件， Thus, ` P IMPLY Q ` is a valid first order proposition. 由于Q c Q可证，且P是最弱前条件，By the assertion derivation logic's completeness, we know that `P |-- Q` which is immediately followed by `|-- {{ P }} c {{ Q }}`according to the consequence rule.

### Assignment

The proof is similar.

### Sequence

The proof is similar. 由IH，`P c1 R` 可证， `R c2 Q` 可证，由顺序执行规则。proved directly by definition and IH。

### If, else

The proof is similar.

### While

This is the only interesting case! Suppose `wp P c Q`. We know:

    for any st and La,
      (st, La) |== P if and only if
      for any st', if (ceval c st st'), then (st', La) |== Q.

1. Goal1: `|-- {{ P AND {[ b ]} }} c1 {{ P }}.`
   Now, consider the weakest precondition of `c1` and `P`. We claim that `P AND {[ b ]}` is stronger than weakest preconditions of `c1` and `P`. 
   我们已知，P是整个循环的最弱前条件，我们现在检查经过一次循环，是不是还是符合b。

For fixed `st` and `La`, if

    (st, La) |== P AND {[ b ]}

then for any `st'`

    if (ceval c st st'), then (st', La) |== Q.

因为一开始符合b，我们知道必然执行一次，Since `b` is true on `st`, we know that for any `st'` and `st''`,

    if (ceval c1 st st') and (ceval c st' st''), then (st'', La) |== Q.

This is equivalent to say: for any `st'`,

    if (ceval c1 st st') then 【for any st'',
       if (ceval c st' st''), then (st'', La) |== Q.】

诶，拆开来之后，后半句不就是最弱前条件的表述吗，By the fact that `wp P c Q`, we conclude that for any `st'`,

    if (ceval c1 st st') then (st', La) |== P.

Now, suppose `P'` is a weakest precondtion of `c` and `P` (by expressiveness
lemma, it must exist). What we just proved means that `(P AND {[ b ]}) IMPLY P'`
is a valid assertion. By the first order logic's completeness,

    P AND {[b]} |-- P'.

By induction hypothesis:

    |-- {{ P' }} c1 {{ P }}.

Then by the consequence rule:

    |-- {{ P AND {[ b ]} }} c1 {{ P }}.

Thus,

    |-- {{ P }} c {{ P AND NOT {[ b ]} }}.

2. At the same time, due to `wp P c Q`, it is obvious that if `(st, La) |== P AND NOT {[ b ]}` on some interpretation `(st, La)`, then `(st, La) |== Q`. In other words, `(P AND NOT {[ b ]}) IMPLY Q` is valid. 一方面，最弱前条件表明Q必成立，另一方面，非b表明不执行一次循环
 
Thus,

    P AND NOT {[ b ]} |-- Q.

So,

    |-- {{ P }} c {{ Q }}.

This proves that all triples with weakest preconditions are provable.