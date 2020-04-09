---
title: 【Programming Language】Denotation VS Small-Step
url: pl-denovsstep
date: 2020-04-09 08:06:30
tags: 
- Programming Language

categories: 
- Courses

---

Week 6 of 2020 Spring

<!--more-->

[toc]


## Semantic Equavalence: Brief Idea

指称语义:对程序结构归纳, 小步语义: 构造step-by-step relation,based on command. We will prove.
```Coq
Theorem semantic_equiv: forall c st1 st2,
      ceval c st1 st2 <-> multi_cstep (c, st1) (CSkip, st2)
```

## Denotation to Small-Step

Proof idea:
- =>
  由于ceval是递归定义的, 我们需要对C的语法树做结构归纳.
  ```
  ceval c st1 st2 -> multi_cstep (c, st1) (CSkip)
  C ::= Skip
      | X ::= E
      | c1 ;; c2
      | If B Then c1 Else c2 EndIf
      | While B Do C EndWhile
  ```
  1. `ceval Skip st1 st2` -> `multi_cstep (Skip, st1) (CSkip, st2)` 左边implies st1 = st2, 由自反性得证
  2. `ceval (X ::= E) st1 st2` -> `multi_cstep (X ::= E, st1) (CSkip, st2)`, 左边说明了st2中仅有X与st1不同, 但右侧不是显然的, 因为E可能是复杂的表达式
     - Recall: 同余关系 on assignment: if on state `st`, `E -->* E'`, then `(X::=E, st) -->* (X::= E', st)`
     - 我们发现, 我们需要一个关于整数类型表达式的性质, if `aeval E st = n`, then `multi_astep st E (ANum n)`.
     - 这样, 我们可以构造, `(X::=E, st1) -->* (X::=ANum (aeval E st1), st1) -->* (Skip, st2)`, 且符合我们指称语义中给出的st1和st2的关系.
  3. `ceval (c1 ;; c2) st1 st2` -> `multi_cstep (c1 ;; c2, st1) (CSkip, st2)`
     注意, IH一定是forall st1 st2. 因为我们是对c归纳.
     ```Coq
     IH1: forall st1 st2, ceval c1 st1 st2 -> multi_cstep (c1,st1) (CSkip, st2)
     IH2: forall st1 st2, ceval c2 st1 st2 -> multi_cstep (c2,st1) (CSkip, st2)
     ```
     Recall `ceval (c1;;c2) = concat (ceval c1) (ceval c2)` $\Rightarrow$ $\exists$ st, `ceval c1 st1 st` and `ceval c2 st st2`
     By IH1, `multi_cstep (c1,st1) (CSkip, st)`.
     By Congruence property, `(c1;;c2,st1) -->* (CSkip;;c2, st)` and that `(CSkip;;c2,st) --> (c2,st)`
     By IH2, `(c2,st) -->* (CSkip, st2)`.
  4. `ceval (If b Then c1 Else c2 EndIf) st1 st2` -> `multi_cstep (If b Then c1 Else c2 EndIf) (CSkip, st2)`
     ```Coq
     IH1: forall st1 st2, ceval c1 st1 st2 -> multi_cstep (c1,st1) (CSkip, st2)
     IH2: forall st1 st2, ceval c2 st1 st2 -> multi_cstep (c2,st1) (CSkip, st2)
     ```
     Recall 
     ```Coq
     ceval (If b Then c1 Else c2 EndIf) = union (concat (test_rel [[b]]) (ceval c1)) 
                                                (concat (test_rel [[!b]]) (ceval c2));
     Thus
     ceval (If b Then c1 Else c2 EndIf) st1 st2 <->
        beval b st1 /\ ceval c1 st1 st2 \/
        ~ beval b st1 /\ ceval c2 st1 st2
     By IH,
        beval b st1 /\ (c1, st1) -->* (CSkip, st2) \/
        ~ beval b st1 /\ (c2, st1) -->* (CSkip, st2)
     ```
     同样, 我们暂时还没有对布尔表达式求值的多步关系做证明. 我们还需要证明:
     ```Coq
     If [beval b st], then [b -->* BTrue within st],
     if [~ beval b st], then [b -->* BFalse within st],
     ```
     我们可以根据union的两种情况分别构造多步关系, 以`beval b st1`为例,
     ```Coq
     (If b Then c1 Else c2 EndIf)
     -->* (If BTrue Then c1 Else c2 EndIf)
     -->* (c1, st1) -->* (CSkip, st2)
     ```
  5. `ceval (While b Do c EndWhile) st1 st2` -> `multi_cstep (While b Do c EndWhile) (CSkip, st2)`
     IH: `forall st1 st2, ceval c st1 st2 -> multi_cstep (c,st1) (CSkip, st2)`
     注意, 左侧是循环执行了0,1~n次, 右侧是不断用if嵌套展开.
     By assumption, exists n, `iter_loop_body b (ceval c) n st1 st2`, 接下来我们就需要证明, 如果恰好执行n次, 小步关系可构造, 我们对n进行归纳证明
     - When `n = 0`, `iter_loop_body b (ceval c) n st1 st2` means `~ test_rel b st1 st2`, 即`b`在`st1`上为假, 且`st1 = st2`.  由此我们可以构造
       ```Coq
       (While b Do c EndWhile, st1) 
       -->* (If b Then c;;While b Do c EndWhile Else Skip, st1 )
       -->* (If BFalse Then c;;While b Do c EndWhile Else Skip, st1 )
       -->* (Skip, st1) = (Skip, st2)
     - When `n = n' + 1`,
       IHn: if `forall st1, st2, iter_loop_body b (ceval c) n' st1 st2`, then `(While b Do c EndWhile, st1) -->* (CSkip, st2)`
       To Prove: if `forall st1, st2, iter_loop_body b (ceval c) (n' + 1) st1 st2`, then `(While b Do c EndWhile, st1) -->* (CSkip, st2)`
       By assumption, exists `st1', st1''`, `test_rel [[b]] st1 st1' /\ st1 = st1' /\ ceval c st1' st1'' /\ iter_loop_body b (ceval c) n' st1'' st2`.
       Now, we have
       ```Coq
       (While b Do c EndWhile, st1) 
       --> (If b Then c;;While b Do c EndWhile Else Skip, st1)
       -->* (If BTrue Then c;;While b Do c EndWhile Else Skip, st1)
       --> ( c;;While b Do c EndWhile, st1)
       [IHc] -->* (Skip;; While b Do c EndWhile, st1'')
       --> (While b Do c EndWhile, st1'')
       [IHn] -->* (CSkip, st2)
       ```

## Small-Step to Denotation

### Induction on CExp

Proof Idea: 对程序c的结构进行归纳.

#### Sequence
```Coq
IH1: forall st1 st2, (c1, st1) (CSkip, st2) -> ceval c2 st1 st2
IH2: forall st1 st2, (c2, st1) (CSkip, st2) -> ceval c2 st1 st2
-------
(c1;;c2, st1) (CSkip, st2) -> ceval (c1;;c2) st1 st2
```

实际上是在问, 程序的中间状态一定是怎么样的, Intuitively:
```Coq
(c1;;c2, st1) -->* (CSkip;; c2, st) --> (c2, st) -->* (CSkip, st2)
```

问题是, 我们能否用`(c1;;c2, st1) -->* (CSkip, st2)`, 给出上面的命题, 且应用一个类似一个反向的congruence由`(c1;;c2, st1) -->* (CSkip;; c2, st)` 得出 `(c1,st1) -->* (CSkip, st)`

idea: 对多步关系做1n归纳证明. 首先, refl是不成立的. 对第一步的可能: 若`c1`是`Skip`, 直接得证(结构发生变化,但结论trivial). 若不是`Skip`(结构不变,可以应用IH),
```Coq
       (c1;;c2, st1) --> (c;;c2, s) ---------------------------------->* (CSkip, st2)
By IH, (c1;;c2, st1) --> (c;;c2, s) -->* (CSkip;;c2,st) --> (c2,st) -->* (CSkip, st2)
```

#### Assignment
```Coq
(X ::= E, st1) -->* (CSkip, st2) -> ceval (X::=E) st1 st2
```
我们希望构造子结构:
```Coq
E -->* (ANum (aeval E st1)) within st1
```
can be proved by 1n induction

可以看到, 证明思路是一致的, 即由整体的多步关系构造子结构的多步关系.

### Alternative Proof: Induction on Multi-step

```Coq
(c, st1) -->* (CSkip, st2) -> ceval c st1 st2
```
考虑, 对多步关系做归纳.
- 若为refl, 显然c=CSkip, 则有ceval c st1 st2
- 若非refl, 则有`(c, st1) --> (c', st1') -->* (CSkip , st2)`
  我们只要证明, **小步语义可以保持终止状态不变**, 具体来说:
  ```Coq
  Lemma ceval_preserve: forall c c' st1 st1',
        cstep (c, st1) (c', st1') ->
        forall st2, ceval c st1 st2 <-> ceval c' st1' st2;
  ```
  **如果小步语义的单步关系能保持(指称语义)的运行结果不变**, 加上IH: `ceval c' st1' st2`, 我们就能完成归纳证明. 实质上, 我们在归纳证明中只需要上面引理的一半
  ```Coq
  Lemma ceval_preserve': forall c c' st1 st1',
        cstep (c, st1) (c', st1') ->
        forall st2, ceval c st1' st2 -> ceval c' st1' st2;
  ```

#### Foundamental Lemma

注意到, 小步语义是归纳定义的.(rule based definition)
```Coq
| CS_SeqStep :forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
```

因此, 我们还要对小步关系做**归纳**证明, 考虑顺序执行:

```Coq
If the first step is established by:
  [CSeqStep: if (c1, st1) --> (c1', st1') then (c1;;c2, st1) -> (c1';;c2, st')]
IH: forall st2, ceval c1' st' st2 -> ceval c1 st st2
To prove: forall st2, ceval (c1';;c2) st' st2 -> ceval (c1;;c2) st st2
```
**Proof.**
By `ceval (c1';;c2) st' st2`, there exists `st0`, `ceval c1' st' st0` and `ceval c2 st0 st2`.
By IH, `ceval c1' st st0`, by def of ceval, `ceval (c1;;c2) st st2`.

其他情形反而比较简单, 例如,
```Coq
If the first step is established by:
  [CSeq: (CSkip;;c, st) -> (c, st)]
To prove: forall st2, ceval c st st2 -> ceval (CSkip;;c) st st2
Trivial
```

```Coq
If the first step is established by:
  [CS_While: (While b Do c EndWhile,st) ->
             (If b Then c;;While b Do c EndWhile Else Skip EndIf, st)]
To prove: forall st', 
   if: ceval (If b Then c;;While b Do c EndWhile Else Skip EndIf) st st' 
   Then ceval (While b Do c EndWhile) st st2
Which has been proved in the deno chapter
```

我们在证明中, 还需要证明布尔关系的小步语义维持指称语义的求值结果一致. 如
```Coq
Lemma beval_preserve: forall st b1 b2,
  bstep st b1 b2 ->
  (beval b1 st <-> beval b2 st).
```