---
title: 【Lambda Calculus】Introduction
url: lambda-1
date: 2020-03-11 14:30:13
tags: 
- Lambda Calculus

categories: 
- Research

---

Week 2 of 2020 Spring, Lambda Calculus

<!--more-->

[toc]

## Syntax and Laws

### Syntax of Expressions
```
e ::= x (variables)
    | e1 e2 (function application apply e1 to e2)
    | λ x. e (a mapping from a variable to a result)
```
Using trees
```
e ::= x | app (e1, e2) | lam(x.e) (x is a variable bound in e)
```
### λ-calculus Laws
Lambda calculus is more than a notation. We give laws for λ-calculus.
(α) Equivalence: the name of variable in lambda doesn't matter
$$ \lambda x.e = \lambda y.e [y/x], y \notin FV(e)  $$
(β) Function Application
$$ (\lambda x.e) e^{\prime} =_{\beta} e[e^{\prime}/x] $$
(η) Not Changing Anything
$$ \lambda x.(e x) =_{\eta} e, x \notin FV(e)$$
> What is FV?
> e.g. for `lambda x.y+x`
> `lambda z.y+z` is fine.
> but `lambda y.y+y` is wrong, since$y\in FV(x+y)$, binded
Above all are primitive transitions. The question is left for which direction to go.(How to use the laws)

## Semantics

### Call By Name Semantic

We give two inference rules directly.

$$ \frac{}{(\lambda x.e) e^{\prime} \mapsto e[e^{\prime}/x] }$$

$$\frac{e_1 \mapsto e_1^{\prime}}{e_1 e_2 \mapsto e_1^{\prime} e_2}$$

A further question is: which context to apply to rule?

Definition: Evaluation Context
```
E :EvalCxt ::= BOX (the context we are interested in)
             | E e.
BOX[e] = e
(E e')[e] = (E[e]) e'      
```

在EvalCxt中, box只能挖在expression的左边, 因此达到了规定从左向右化简的目的.
Then the rule can be rewritten as:
$$\frac{e \mapsto e^{\prime}} {E[e] \mapsto E[e^{\prime}]}$$

We illustrate this idea by showing how `((λx.λy.x) 1) 2` works
Example: for `((λx.λy.x) 1) 2`:
- `E = [] 2` `e = ((λx.λy.x) 1)` $\mapsto$ `e' = λy.1`
- So `((λx.λy.x) 1) 2` $\mapsto$ `(λy.1) 2` $\mapsto$ `1`

### Call-By-Value Semantic
The difference is that β-law no longer always holds, as most PLs do.
$$\frac{}{(\lambda x.e) v \mapsto e[v/x], v\in \text{value}}$$
where value is defined as
```
V ::= x | λx.e
```
$$\frac{e \mapsto e^{\prime} }{ E[e] \mapsto E[e^{\prime}]}$$
where evaluation context is defined as
```
E:EvalCxt ::= BOX | E e 
            | V E (when a value has already been evaluated)
with (V E)[e] = V (E[e])
```

And we can transform the evalcxt-formed inference rule to 5 explicit inference rules.

$$\begin{array}{cc}
\begin{array}{c}
\hline {x \in \text{Value}} \\
\end{array} &
\begin{array}{c}
\hline {\lambda x.e \in \text{Value}} \\
\end{array} \\ \\
\begin{array}{c}
v \in \text{Value}\\
\hline (\lambda x.e) v \mapsto e[v/x]
\end{array} &
\begin{array}{c}
e_1 \mapsto e_1^{\prime} \\ \hline
e_1 e_2 \mapsto e_1^{\prime} e_2 \\
\end{array} \\ \\
\begin{array}{c}
e_1 \in \text{Value} , e_2 \mapsto e_2^{\prime} \\ \hline
e_1 e_2 \mapsto e_1 e_2^{\prime} \\
\end{array} \\
\end{array}$$


## Encoding Game


### If-branch
We design the following syntax sugar:
`if e then e1 else e2` is defined as `e e1 e2`, where `e` can be
- True = `λx. λy. x`
- False = `λx. λy. y` 

Then it is easy to check that

- `if True then e1 else e2` $\mapsto$ `e1`
- `if False then e1 else e2` $\mapsto$ `e2`

We define booleans without booleans.

### Sets
- We define $e\in e' := e' e$.
- $e_1 \cup e_2 := \lambda x. or (e_1 x) (e_2 x)$
- $e_1 \cap e_2 := \lambda x. and (e_1 x) (e_2 x)$

- Infinite negation
  Russel Set $R = {e | e \notin e}$, is $R \in R$?
  in lambda language, $R = \lambda x. not(x x)$
  > 这个问题没有答案, 它会不停地一步一步计算evaluate下去
  $$\begin{aligned}
  R\quad R &\mapsto (\neg (x \quad x))[R/x] \\
  &= \neg (R \quad R) \\
  &\mapsto \neg (\neg (R \quad R)) \mapsto \ldots
  \end{aligned}s$$
- infinite refl
  $\omega = (\lambda x.x x) (\lambda x.x x)$
  $\omega \mapsto \omega$
- infinite apply 设计y combinator, 使得`y f`一步后得到`f(y f)`由此不停地套用下去.
  `y f = (λx.f(xx))(λx.f(xx))`
  $y f \mapsto f(y f)$

Use lambda calculus to define recursive functions.  Paradox in the language makes recursion happen
$$\begin{aligned}
  times = \lambda x. \lambda y. \quad if \quad x == 0 \quad & then \quad 0 \\
  & else \quad y + times \space (x-1)\space  y
\end{aligned}$$
$$\begin{aligned}
  timesish = \lambda next. \lambda x. \lambda y. if \quad x == 0 \quad & then \quad 0 \\
  & else \quad y + (next \space (x-1) \space y)
\end{aligned}$$

## Untyped vs. typed

Typing rules:
$$
\tau \in \text{Type} = \alpha | \tau_1 \rightarrow \tau_2
$$

$$
\begin{array}{c}
\hline
\Gamma x :\tau \vdash x : \tau
\end{array}
$$

$$
\begin{array}{c}
\Gamma \vdash e: \tau^{\prime} \rightarrow \tau \quad \Gamma \vdash e^{\prime} : \tau^{\prime} \\
\hline
\Gamma \vdash e \space e' :\tau
\end{array}
$$

$$
\begin{array}{c}
\Gamma x:\tau \vdash e: \tau^{\prime} \\
\hline
\Gamma \vdash \lambda x.e :\tau \rightarrow \tau^{\prime}
\end{array}
$$

An example:


$$
\begin{array}{c}
\hline
x:\alpha \vdash x: \alpha \\
\hline
\vdash \lambda x.x :\alpha \rightarrow \alpha 
\end{array}
$$


Context是变量名到类型的映射.

> Theorem (termination) if a term e is will-typed under any context. Then there exists an $e^{\prime}$ such that $e \mapsto e^{\prime}$ and $e^{\prime}$ will not reduce to anything.

在Typed system下, self-apply是不被允许的

