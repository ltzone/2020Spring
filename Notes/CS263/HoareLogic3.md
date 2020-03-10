---
title: 【Programming Language】Hoare Logic 3
url: pl-hoare3
date: 2020-03-10 14:02:32
tags: 
- Programming Language 

categories: 
- Courses

---

Week 2 of 2020 Spring. More about Hoare Logic

**KeyWords**: Hoare Logic, Program Semantics

<!--more-->

[toc]

Recall: 此前证明中的问题
1. 我们还没有对赋值的行为做出规定. 都是以单独声明的形式呈现的
2. 等价推理规则的转换还没有实现

## Assignment Rule (forward)

Common Pattern of Post Conditions after `X:=E`:
1. The original value of `X` satisfies the precondition
2. The current value of `X` can be calculated by `E` using the original value of `X`.
 
However, we cannot always refer o the original value directly.

```Coq
{ n * [[Y]] + [[X]] = m AND 0 <= [[X]] AND [[X]] < n }
Y ::= 0
{ ??? }
```

The best condition can be (丰富的数学语言)

```Coq
{ EXISTS y, n * y + [[X]] + n = m AND
  0 ≤ [[X]] AND [[X]] < n AND [[Y]] = 0 }
```

Using Exstential Quantifier, we can write the following postcodition informally:

> There exists an old value x of program variable X, such that
> 1. the precondition P would hold if the value of X would be x 
> 2. the value of X is result of evaluating the expression E if **treating** all occurrences of X in E as x.



### Symbolic substitution in program expressions

How to deal with **treating**?
**Definition:** `E [X |-> E0]` where `E` , `X` and `E0` are interger-typed expressions, The result will be an interger-typed expression.
Similarly, `B [X |-> E0]` where `B` is boolean-typed and `X` and `E0` should be interger-typed. The result will be an boolean-typed expression.

### Symbolic substitution in assertions

`P [X |-> E0]` where `P` is assertion and `X` and `E0` should be same-typed. `E0` can be constant expression or others. The result will be an assertion.

Remember, 语法替换, 替换操作的对象是语法树, 操作的实际意义是将语法书中被替换的节点用新的一棵子树替换.

### Proof Rule

由前条件写出最强后条件(proposed by Floyd.)
```Coq
Axiom hoare_asgn_fwd : forall P `(X: var) E,
  {{ P }}
  X ::= E
  {{ EXISTS x, P [X |-> x] AND {[X]} = {[ E [X |-> x] ]} }}.
```
## Assignment Rule (backward)
由后条件写出最弱前条件, "the real Hoare" assignment rule. 由后条件简单替换.

```Coq
Axiom hoare_asgn_bwd : forall P `(X: var) E,
  {{ P [ X |-> E] }} X ::= E {{ P }}.
```

任何一条都足够描述赋值语句的性质. 实际上, 这两条规则是等价的.

## Consequence Rule
Proof Cases:
- 去除条件中的一些信息(推理)
- 等价变化
```Coq
Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->  {{P'}} c {{Q'}} -> Q' |-- Q 
  ->  {{P}} c {{Q}}.
(* P是一个更强的前条件, Q是一个更弱的后条件, 那么{{P}} c {{Q}}成立 *)
```

以上我们定义的规则是对程序行为的描述, 它们是连接程序语义的桥梁


> Extension:
> 我们定义的有限若干条规则是否足够用来证明所有程序具有的性质?
> Yes. 霍尔逻辑的推理规则构成了程序语言完整的描述.
> How to prove? 
> - 如果程序C真的具有某个性质(即PcQ真的成立), 我们可以用霍尔逻辑说明它.
>   - 如何说明PcQ成立? 要说明程序行为成立
>   - 我们对于程序行为的定义?
>   - 目前为止我们只给出了Hoare Logic式的定义
>   - 但当我们给出其他关于程序行为的定义时, 我们可以做到这一点(即证明不同程序语义之间的关系)


