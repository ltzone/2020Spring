---
title: 【Programming Language】First Order Logic
url: pl-forder
date: 2020-03-17 14:03:56
tags: 
- Programming Language

categories: 
- Courses

---

Week 3 of 2020 Spring

<!--more-->

[toc]

## Review

### Assignment 1

Task 2_2: 
```
Hoare triple: {{ EXISTS k. {[X]} = 2 * k }} c {{ {[Y]} = 0 }}.
Informal description: the program [c] will test whether [X] is an even
number (偶数); if yes, [0] will be assigned into [Y].
Do they express equivalent meaning? 1: Yes. 2: No.
```
不保证程序一定有检验偶数这一步, 错误. 自然语言的描述和霍尔三元组不等价

Task 2_5:
```
Hoare triple: for any m, {{ {[X]} + {[Y]} = m }} c {{ {[X]} + {[Y]} = m }}.
Informal description: the program [c] will not change the sum of [X] and [Y].
Do they express equivalent meaning? 1: Yes. 2: No.
```
答案是正确的, 因为是forall m.

### Brief Summary

Till now, we used a simple imperative programming language (指令式程序语言) as an example to introduce the following concept:
- assertions (including syntactic substitution and assertion derivation)
- Hoare triples
- axiomatic semantics.

同时, 我们借助IMP可以在Coq中进行程序中的证明. 目前为止, 我们在证明过程中依然需要假设断言推导的条件成立. 我们也希望证明命题推导的成立.

## Assertion entailment

在Imp库中, 给出了`entailer`指令, 将断言推导转化为与程序状态无关的数学证明.

Coq标准库还提供了`lia`(linear integer arithmetic system) tactic解决线性不等式的证明. (关于整数的性质, 关于命题的性质, 关于不等式的性质 OK), 可以解决可判定问题.

> Proof
> 避免存在量词可以使用bwd_assignment
> `eapply hoare_consequence;[|apply hoare_assgn_bwd]` 直接生成
> 进入hoare_while时, 先用hoare_consequence改进前后条件.

对于非线性的运算, Coq提供了`nia`(non linear)的一定支持, 但这不是万能的.
```Coq
Goal forall x y:Z, (x+y)*(x+y) >= 0.
Proof.
  intros.
  Fail nia.
Abort.
```

## First Order Logic in Coq

Coq最重要的用途在于它对逻辑的支持, 我们介绍一些Coq中一阶逻辑的证明.

- In Coq, `I` is a proof of `True`. use `exact I`.
- `revert` 是 `intros`的逆操作
- `specialize`效果相当于`pose proof;clear`
- 矛盾律: P和非P可以推导出任何东西
- 排中律: P和非P必须有一个成立

## First Order Logic for Assertion Derivation

我们也可以直接选择在断言推导中进行逻辑推导. 断言推导本身也构成了一阶逻辑. Imp库提供了这一支持.

