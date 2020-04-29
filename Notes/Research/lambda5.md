---
title: 【Lambda Calculus】Polymorphism - System F
url: lambda-poly
date: 2020-04-15 15:15:53
tags: 
- Lambda Calculus

categories: 
- Courses

---

Week 7 of 2020 Spring.

<!--more-->

[toc]

## Example

I can have the identity for Booleans which could be 
$$\text{id Bool} = \lambda (x: \text{Bool}).x : \text{Bool} \rightarrow\text{ Bool}$$
$$\text{id Num} = \lambda (x: \text{Num}).x : \text{Num} \rightarrow\text{ Num}$$
$$\text{id Alpha} = \lambda (x: \text{Alpha}).x : \text{Alpha }\rightarrow \text{Alpha}$$

> When you are doing something without knowing anything, you are doing everything.

We simply assume a base type. Syntax Tree:
$$
\begin{array}{l}
  \tau ::= \alpha \space | \space \text{arr}(\tau_1,\tau_2) \space | \space \text{all} (\alpha,\tau) \\
  \tau ::= \alpha \space | \space \tau \rightarrow \tau \space | \space \forall \alpha.\tau \\
  \\
  e ::= x \space | \space \text{lam} \{\tau\} (x,e) \space | \space \text{app} (e_1,e_2) \space | \space \text{Lam}(\alpha,e)\space | \space\text{App}(e,\tau) \\
  e ::= x \space | \space \lambda x:\tau . e \space | \space e_1 \space e_2 \space | \space \Lambda \alpha.e \space | \space e \space \tau
\end{array}
$$

Judgement: $\Gamma ::= x_1:\tau_1, \ldots, x_n:\tau_n$, $\Theta ::= \alpha_1, \alpha_2, \ldots, \alpha_n$

$$
\begin{aligned}
J ::=& \Theta ; \Gamma \vdash e:\tau \space \quad FV(e) \subseteq \Gamma\\
    |& \space \Theta \vdash \tau : \star \quad FV(\tau) \subseteq \Theta
\end{aligned}
$$

The meaning of $\star$ is just $FV(e) \subseteq \Gamma$ or $FV(\tau) \subseteq \Theta$

## Typing Rules

$$
\begin{array}{c}
\begin{array}{c}
\\ \hline
\Theta, \alpha \vdash \alpha : \star
\end{array}
  &
\quad
\begin{array}{c}
\Theta \vdash \tau_1 : \star \quad \Theta \vdash \tau_2 : \star \\
\hline
\Theta \vdash \tau_1 \rightarrow \tau_2 : \star
\end{array}
\end{array}
$$

Here comes the instresting forall. Forall introduce an extra generic type. (with the premise that $\alpha$ is not binded by $\tau$.)

$$
\begin{array}{c}
\Theta,\alpha \vdash \tau :\star \\
\hline
\Theta \vdash \forall \alpha.\tau : \star
\end{array}
$$

In other words, we can say $\Theta$ captures all the binded variables in the expressions following $\vdash$

Function application and lambda expression, Nothing happens.

$$
\begin{array}{c}
\begin{array}{c}
\Theta;\Gamma \vdash e_1: \tau \rightarrow \tau' \quad \Theta;\Gamma \vdash e_2 :\tau \\
\hline
\Theta;\Gamma \vdash e_1 \space e_2 : \tau'
\end{array}
& \quad
\begin{array}{c}
\Theta;\Gamma ,x:\tau \vdash e:\tau' \\
\hline
\Theta;\Gamma \lambda x.e:\tau \rightarrow \tau'
\end{array}
\end{array}
$$

Application and function of types.

$$
\begin{array}{c}
\Theta;\Gamma \vdash e:\forall\alpha.\tau \quad \Theta \vdash \tau':\star \\
\hline
\Theta;\Gamma \vdash e\space \tau':\tau[\tau'/\alpha]
\end{array}
$$

$$
\begin{array}{c}
\Theta,\alpha;\Gamma \vdash e:\tau \\
\hline
\Theta;\Gamma \vdash \Lambda \alpha. e : \forall \alpha.\tau
\end{array}
$$
The implication of the above rule is that it's ok to talk about $\alpha$ when we can extract $\alpha$ from the context.

> TODO: what does type-substitution mean?

### Theorems

1. If $\Theta \vdash \tau:\star$, then $FV(\tau) \subseteq \Theta$
2. If $\Theta;\Gamma \vdash e:\tau$ then $\Theta \vdash \Gamma$ and $\Theta \vdash \tau:\star$.


### Application

With type quantifier, we can talk about recursive types in a more elegant way
 

 ## Semantics

 ### Call-by-Name

$$
\begin{aligned}
\text{value} =& \lambda x:\tau.e \\
|& x \\
|& \Lambda \alpha.e 
\end{aligned}
$$

Lemma(Progress) if $\Theta ;\Gamma\vdash e:\tau$. Then $e$ is either a value or $e\mapsto e'$
Lemma(Preservation) if $\Theta; \Gamma \vdash e:\tau$ and $e\mapsto e'$, Then $\Theta, \Gamma \vdash e':\tau$
Theorem(Type-Safety) if $\Theta;\Gamma \vdash e:\tau$ and $e\mapsto^{*} e'$, then $e'$ is not stuck.(either a value or $e\mapsto e'$)

Lemma(Type-substitution): if $\Theta;\Gamma \vdash e:\tau$ and $\Theta \vdash \tau:\star$ are derivable, then so is $\Theta ; \Gamma [\tau/\alpha] \vdash e[\tau/\alpha] : \tau[\tau/\alpha]$

beta rule:
1. $(\lambda x .e) e^{\prime} \mapsto e\left[e^{\prime} / x\right]$
2. $(\Lambda \alpha . e) \tau \mapsto e[\tau / \alpha]$ (we write so because $e[\tau / \alpha]$ is exactly what we say in the type-substitution typing rule)

$$E \in \text {EvalCxt }::=\square\space |\space E \space e\space | \space E\space  \tau$$

We can prove the lemmas above by induction.

### Call-by-Value

substitute the value during a function call

$$
\begin{array}{c}
e' \text{ value} \\
\hline
(\lambda x:\tau.e) \space e' \mapsto e[e'/x]
\end{array}
$$

$$
\begin{array}{c}
\\
\hline
(\Lambda \alpha.e) \space \tau \mapsto e[\tau/\alpha]
\end{array}
$$

Other inferences are same as simple lambda calculus, can be seen from the evaluation context.

$$
\begin{array}{c}
e \mapsto e' \\
\hline
e  \space \tau \mapsto e' \space \tau
\end{array}
$$

$$E \in \text {EvalCxt }::=\square\space |\space E \space e\space | \space E\space  \tau \space | \space V \space E$$



## Erasure

We want to reason about the properties that are not related to $\Lambda\alpha$. We define erasure by induction on expression. (hide types from users).

$$
\begin{array}{l}
\text{erase}(x) = x \\
\text{erase}(\lambda x:\tau.e) = \lambda x. \text{erase}(e) \\
\text{erase}(e_1 \space e_2) = \text{erase}(e_1) \space \text{erase}(e_2) \\
\text{erase}(\Lambda \alpha.e) = \text{erase}(e) \\
\text{erase}(e \space \tau) = \text{erase}(e) \\
\end{array}
$$

**Theorem** (Erasure doesn't change the result of a program: v is a vlue):[Type Erasure]:
if $e \mapsto^{*} v$, then $\text{\text{erase}}(e) \mapsto^{*} \text{erase}(v)$.

First question: which semantics do we need?

### CBN

A CBN Fix for $\Lambda \alpha.e$ stops evaluating: add a premise that "if $\Theta , \cdot \vdash e: \tau$ and $\tau \neq \forall \alpha.\tau$".

Otherwise, a counter example
$$\text{erase}(\Lambda \alpha.(\lambda x.x)(\lambda x.x)) =(\lambda x.x)(\lambda x.x)$$


### CBV

Recall $\Omega \mapsto \Omega$.
a counter example: $\text{erase} ((\lambda x. 1) (\Lambda\beta.\Omega)) = (\lambda x. 1) (\Omega)$ is no longer a value!

### Refined erasure

add a dummy $\lambda$
$$
\begin{array}{l}
\text{erase}(x) = x \\
\text{erase}(\lambda x:\tau.e) = \lambda x. \text{erase}(e) \\
\text{erase}(e_1 \space e_2) = \text{erase}(e_1) \space \text{erase}(e_2) \\
\text{erase}(\Lambda \alpha.e) = \lambda x. \text{erase}(e) \quad (x \notin FV(e)) \\
\text{erase}(e \space \tau) = \text{erase}(e) \\
\end{array}
$$



## STLC VS SYSTEM-F

两种系统都定义了syntax, operational semantics(CBN,CBV), type inference.

补充一点 curry-howard iso.

proof system v.s. type system
prop         v.s. type
proof        v.s. program
proof rule   v.s. language constructor

P /\ Q : Prop       v.s. A * B : Type
conj H1 H2: P /\ Q  v.s. (x, y) : A * B

P -> Q : Prop               v.s. A -> B : Type
fun H ==> ... H ..: P -> Q  v.s. fun x => ... x ... : A -> B

典型的同构对应关系
```
/\, \/, True, False, ->
*, +, unit, void, ->
```

In System-F: 类型多了一个Forall，`forall x:A, X`

问题来了：
1. `LAMBDA tau. lambda x:tau. x`的类型是`forall tau, tau -> tau`。Q1:但在Coq中的写法是`(forall tau:Prop, tau -> tau):Prop`。两个`Prop`一样吗？Yes。

2. `@nil : forall A:Type, list A`,`@cons: forall A: Type, A -> list A -> list A`.但`(forall A:Type, list A):Type`。Q2： 两个Type一样吗？Not necessary。

### Insights

Type World: predicative，不能在一个type中quantify all types(sets)。类似集合论中，不能有包含自己的集合（罗素悖论）。（Hint: universe inconsiistency，Coq内部是会动态分配继承机制的）

Prop World：impredicative（within one proposition， quantify over all proposition）奇怪之处，可以带入本身。`(forall tau:Prop, tau -> tau) -> (forall tau:Prop, tau -> tau)`.

Prop World这个系统成立的原因，就是System-F。我们可以认为这个同构保持一致性。