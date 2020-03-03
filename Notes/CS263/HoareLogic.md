---
title: 【Programming Language】 Hoare Logic 1
url: pl-hoare
date: 2020-03-03 14:02:12
tags: 
- Programming Language

categories:
- Courses

---

Week 1 of 2020 Spring. An Introduction to Hoare Logic.

**Keywords**: Assertions, Hoare Triples, Program Semantic

<!--more-->

[toc]

## Assertions

Informally, an assertion is a proposition which describes a particular property of program states.

我们可以用严谨而丰富的数学语言描述程序状态的命题/性质（断言）。

More generally, 我们可以用程序变量的值、程序变量的地址、内存上的信息来描述程序状态。

$$(\mathbf{[I]} \longmapsto \theta) \text{AND} ([\mathbf{t}] +4 \longmapsto \text { NULL } ) \operatorname{AND} ([\mathbb{S}] = 0)$$

### What is a "Proposition"

- 命题是一个句子
  - 断言应被定义为语法树
  - 命题5≠6
- 命题是句子的含义
  - 断言应被定义为程序状态的集合
  - 命题5=6，即所有的程序状态都满足该断言

### Assertions vs. boolean functions
- 并不是所有断言都可以用布尔函数描述
    - FORALL ...
- 并不是所有布尔函数表达一个断言
    - side effects in C
- 断言描述性质，布尔函数强调计算的过程
- 也具有一定的联系，如很多动态程序分析工具都是用布尔函数描述断言的

## Hoare Logic

> We use **Hoare Triple**  `{{P}} c {{Q}}` to describe the following propery:
> *if command c is started satisfying assertion P, and if c eventually terminates in some final state, then this final state will satisfy the assertion Q*

The following codes holds, since the command will not terminate, so all the post condition holds.

```
{{ [X] = 1 }}
  While !(X == 0) Do X ::= X + 1 EndWhile
{{ [X] = 100 }}
```

## Hoare Triples as Program Semantics

用Hoare Triples描述程序的行为，注意，我们此前仅定义了表达式的语法，没有定义command的含义。如，我们可以声明hoare_seq为顺序执行的语义。

```
Axiom hoare_seq: forall (P Q R: Assertion) (c1 c2: com),
{{P}} c1 {{Q}} -> {{Q}} c2 {{R}} ->{{P}} c1;;c2 {{R}}.
```

```
Axiom hoare_skip: forall ( Q: Assertion),
{{P}} SKIP {{P}} 
```

```
Axiom hoare_if_first_try: forall P Q b c1 c2,
{{P}} c1 {{Q}} -> {{P}} c2 {{Q}} ->
{{P}} If b Then c1 Else c2 EndIF {{Q}}.
```

```
Axiom hoare_if: forall P Q b c1 c2,
{{P AND [[b]]}} c1 {{Q}} ->
{{P AND NOT [[b]]}} c2 {{Q}} ->
{{P}} If b Then c1 Else c2 EndIF {{Q}}.
```

where `[[b]]` means the boolean expression b evaluates to `true`.