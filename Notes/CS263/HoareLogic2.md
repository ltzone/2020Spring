---
title: 【Programming Language】Hoare Logic 2
url: pl-hoare2
date: 2020-03-05 08:02:32
tags: 
- Programming Language 

categories: 
- Courses

---

Week 1 of 2020 Spring. More about Hoare Logic

**KeyWords**: Hoare Logic, Program Semantics

<!--more-->

[toc]

## Examples about Hoare_if

Recall.

```
Axiom hoare_if: forall P Q b c1 c2,
{{P AND [[b]]}} c1 {{Q}} ->
{{P AND NOT [[b]]}} c2 {{Q}} ->
{{P}} If b Then c1 Else c2 EndIF {{Q}}.
```

Consider the following swap program.

```
IF X<= Y
THEN SKIP;
ELSE Z=X;X=Y;Y=Z;
END IF
```

A specification about the program.

```
for all n, m, 
{{[[x]]=n,[[y]]=m}}c
{{[[x]]=min(n,m),[[y]]=max(n,m)}}
```

Write down the triples that two branches satisfy.

```
{{[[X]]=n,[[Y]]=m AND [[X<=Y]]}}
c
{{[[X]]=min(n,m),[[Y]]=max(n,m)}}
```

```
{{[[X]]=n,[[Y]]=m AND NOT [[X<=Y]]}}
c
{{[[X]]=min(n,m),[[Y]]=max(n,m)}}
```

## Axiomatic semantics for loops

Suppose we have a loop
```
{{P}} While b Do c EndWhile {{Q}}
```

It may be hard to come up with a straight complete specification, we might be tempted to write:

```
Axiom hoare_while_first_try: forall (P:Assertion) (b:bexp) (c:com), [[b]] = false -> {{P}} While b Do c EndWhile {{P AND NOT [[b]]}}
```

```
Axiom hoare_while_second_try: forall (P:Assertion) (b:bexp) (c:com), {{P}} c {{P}} -> {{P}} While b Do c EndWhile {{P AND NOT [[b]]}}
```

```
Axiom hoare_while: forall (P:Assertion) (b:bexp) (c:com), {{P AND [[b]]}} c {{P}} -> {{P}} While b Do c EndWhile {{P AND NOT [[b]]}}
```

Where the assertion P is called a loop invariant(循环不变量).

<!--
### Example: Reduce to Zero.

```
{{}}
While !(X==0) Do
X = X - 1
EndWhile
```
-->

### Example: Division
```
{{0<=m And 0<n}}
X = m;;
Y = 0;;
While n<=X Do
  X = X - n;;
  Y = Y + 1;;
EndWhile
{{n*[[Y]]+[[X]]=m AND 0 <= [[X]] AND [[X]]<n}}
```

Considering the bexp, we rewrite the post condition.
```
{{n*[[Y]]+[[X]]=m AND 0 <= [[X]] AND NOT [[n<=X]]}}
(Remark: [[n ≤ X]] --||-- n <= [[X]])
```

The loop invariant is
```
{{n*[[Y]]+[[X]]=m AND 0 <= [[X]]}}
```

By the way, since `0<n` is not used in this spec, we can remove it. It makes sense since the program will not terminate if `n` is not positive.

### How to find a good loop invariant

Consider a case for the division program
```
{{[[X]]=10 AND [[Y]]=0}} c {{[[X]]=7 AND [[Y]]=1}}
{{[[X]]=7 AND [[Y]]=1}} c {{[[X]]=4 AND [[Y]]=2}}
{{[[X]]=4 AND [[Y]]=2}} c {{[[X]]=1 AND [[Y]]=3}}
```

Therefore, our loop invariand `P` should not be stronger than
```
{{[[X]]=10 AND [[Y]]=0}} OR {{[[X]]=7 AND [[Y]]=1}} OR {{[[X]]=4 AND [[Y]]=2}} OR {{[[X]]=1 AND [[Y]]=3}}
```

On the other side,  A loop invariant `P` should not be too weak to _derive meaningful conclusion_ from the conjunction `P AND NOT [[b]]`.

Note the above specification is already good enough, it can be checked by the following props.
1. It ensures the correctness of every loop
2. By combining `P` with `NOT [[b]]` (`NOT 3<=X`), we can derive that `{{[[X]]=1 AND [[Y]]=3}}`

But we should abbreviate the specification a little.

```
{{n*[[Y]]+[[X]]=m AND 0 <= [[X]] AND 0 <= [[Y]]}}
```

```
{{n*[[Y]]+[[X]]=m AND 0 <= [[X]] AND 0 <= [[Y]]}}
```

> Summary: The most critical steps in our examples above is to find a good loop invariant. Is there a generic method of doing that?
> 1. A loop invariant should not be too strong. The program states before and after every single loop body's iteration should satisfy the invariant.
> 2. A loop invariant `P` should not be too weak to derive meaningful conclusion from the conjunction `P AND NOT [[b]]`.


### Example: Remainder Only
```
X = m;;
While n<=X Do
  X = X - n;;
EndWhile
```
Our loop invariant is
```
(EXISTS q, n*q + [[X]] = m) AND 0 <= [[X]])
```

### Example: Slow subtraction
```
X = m;
Y = p;
While !(X==0) Do
  Y = Y - 1;
  X = X - 1;
EndWhile
```
Loop Invariant:
```
[[Y]] - [[X]] = p - m
```

> Above all, Because we use these axioms about Hoare triples to define program semantics, such definition is called an axiomatic semantics (公理化语义). We also say that these axioms form a proof system (推理系统), or a Hoare logic (霍尔逻辑).
> 公理化语义是我们定义的第一种描述程序语言的语义工具.

