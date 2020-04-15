---
title: Lambda Calculus 3
url: lambda3
date: 2020-04-08 15:09:46
tags: 
- Lambda Calculus

categories: 
- Courses

---



<!--more-->

[toc]



## Logical Relations and Termination

**Def (closed) $e$ is closed when $FV(e) = \emptyset$**

**Def (well-typed) e is well-typed when there is a $\Gamma$ and $\tau$ such that $\Gamma \vdash e:\tau$ is derivable**

**Def (Terminates): e is terminating when there is an e' such that $e\mapsto ^* e'$ and $e'\mapsto$ nothing.**


## Review

### Definition & Semantics
$$
\begin{array}{l}
b::= \text{True}\space|\space\text{False} \\
e::= x  \space|\space \lambda x.e \space|\space e1 e2\space|\space b \space|\space \text{ if } e_1 \text{ then } e_2 \text{ else }e_3 \\
\tau ::= \text{Bool} \space|\space \tau_1 \rightarrow \tau_2 \\
(\lambda x.e) \space e' \mapsto e[e'/x] \\
\text{ if True} \text{ then } e_1 \text{ else }e_2 \mapsto e_1 \\
\text{ if False} \text{ then } e_1 \text{ else }e_2 \mapsto e_1
\end{array}
$$

$$
\begin{array}{c}
  \begin{array}{c}
  e_1 \mapsto e_1' \\
  \hline
  e_1\space e_2 \mapsto e_1' \space e_2
  \end{array} &
  \begin{array}{c}
  e_1 \mapsto e_1' \\
  \hline
  \text{ if } e_1 \text{ then } e_2 \text{ else }e_3 \\
  \mapsto \text{ if } e_1' \text{ then } e_2 \text{ else }e_3
  \end{array} \\
\end{array}
$$

### Typing Rule
$$
\begin{array}{cc}
  \begin{array}{c}
  \hline
  \Gamma x : \tau \vdash x:\tau \\
  \end{array}
  &
  \begin{array}{c}
  \Gamma \vdash e_1:\tau \rightarrow \tau' \quad \Gamma \vdash e_2:\tau \\
  \hline
  \Gamma \vdash e_1 \space e_2 :\tau'
  \end{array} \\
  \\ 
  \begin{array}{c}
  \hline
  \Gamma \vdash \text{True}:\text{Bool}
  \end{array}
  &
  \begin{array}{c}
  \hline
  \Gamma \vdash \text{False}:\text{Bool}
  \end{array} \\
  \\
  \begin{array}{c}
  \Gamma x:\tau \vdash e:\tau' \\
  \hline
  \Gamma \vdash \lambda x.e : \tau \rightarrow \tau'
  \end{array}
  &
  \begin{array}{c}
  \Gamma \vdash e_1:\text{Bool} \quad \Gamma \vdash e_2: \tau \quad \Gamma \vdash e_3: \tau \\
  \hline
  \Gamma \vdash \text{ if } e_1 \text{ then } e_2 \text{ else }e_3: \tau
  \end{array}
\end{array}
$$

Intuition
![](img/04-01-15-13-48.png)

### First Try

**Theorem: if $e$ is closed and well-typed, then it is terminating.**

**Theorem: if $\Box \vdash e: \tau$ is derivable then there is an $e'$ such that $e\vdash^* e' \vdash$ nothing.**

Proof. by induction on the derivation $\mathcal{D}$ of $\Box \vdash e: \tau$.
- $\mathcal{D} = \begin{array}{c} \hline \Box \vdash x:\tau \end{array}$ doesn't happen
- $\mathcal{D} = \begin{array}{c} \hline \Box \vdash \text{True}:\tau \end{array}$ is true since
  $\text{True} \mapsto^* \text{True} \mapsto$ nothing
- $\mathcal{D} = \begin{array}{c} \Box \vdash e_1:\text{Bool} \quad \Box \vdash e_2:\tau \quad \Box \vdash e_3:\tau \\ \hline \Box \vdash \text{if } e_1 \text{ then } e_2 \text{ else } e_3:\tau \end{array}$
  IH: for $i=1,2,3$, there is some $e'$ such that $e_i \mapsto^* e_i \mapsto$ nothing (i.e. proof tree $\mathcal{D}_i$). We need to show $\Box \vdash \text{if } e_1 \text{ then } e_2 \text{ else } e_3:\tau$ terminates
  $\text{if } e_1 \text{ then } e_2 \text{ else } e_3:\tau \mapsto^* \text{if } e'_1 \text{ then } e_2 \text{ else } e_3:\tau$
  Suppose $e'_1$ is a Bool, then $\mapsto^*e_j$ ($j=2$ if b = true else $j=3$), and that $e_j \mapsto^* e'_j \mapsto$ nothing.
  Suppose $e'_1 \neq b$, 
  - **terminates doesn't necessarily mean value**, Our proof is, this is the end, the expression will not step to anything. (The definition of inductive definition says it.) Termination is exactly what we want.
  - or, we may say, this case is impossible because the type-safety (but with a lot more extra complicated proof). or we can say we don't care about whether what the program terminating is a value. it terminates, and this is not exactly true beacuse type safety.
- $\mathcal{D} = \begin{array}{c} x:\tau \vdash e:\tau' \\ \hline \Box \vdash \lambda x.e: \tau \rightarrow \tau' \end{array}$ Find a reduction rule such that $\lambda$ do something. Nothing applies. No rule for $\lambda$ takes a step on its own.
  Furthermore, The IH is vacuous, because it introduces a free variable.
- $\mathcal{D} = \begin{array}{c} \Box \vdash e_1:\tau \rightarrow\tau^{'} \quad \Box \vdash e_2:\tau^{'} \\ \hline \Box \vdash e_1\quad e_2:\tau^{'}  \end{array}$
  IH: for $i = 1,2$, $e_i \mapsto^{*} e'_i \mapsto$ nothing
  Suppose $e'_1 = \lambda x . e^{'}$: it then happens that $e_1 \quad e_2 \mapsto^{*} \lambda x . e^{'} e_2 \mapsto e^{'} [e_2/x]$. Note here I don't know anything about $e^{'}$. **We need to know something about the function. The IH is too weak!** Stronger than what we really care about.

## Reducable terms are terminating
![](img/04-08-15-23-55.png)
intuitively, it's the influence of types extension.
We should say, something inreducable is not just lambda, but also other things.
Now we need to define logical relations to illustrate the idea we just came up with.

### Definition

$$\Box e : \tau \implies e \in \left[\!\!\left[ \tau \right]\!\!\right] \subset \text{Terminating Things}
$$

$$
\begin{aligned}
  \mathbb{C}^{*} &= \{ e| \exists e' \in \mathbb{C}, e\mapsto^{*} e' \} \\
  \left[\!\!\left[\text{bool}\right]\!\!\right] &= \{ \text{True, False} \}^{*}
\end{aligned}
$$

expressions that are not booleans right now may evaluate to booleans, stuff like `λx.x True: Bool`, because it evaluates to boolean.

We define star notation, and this definition may not be well-typed, like `if False then (λx.x) else True`. No need to talk about types in a static sense when we are discussing things about dynamic behavior.

In some sense, it's just a type-based terminating definition, which doesn't care the type safety during the evaluating process.

### Properties of Expansion
- In general, if $\left[\!\!\left[\mathbb{C}\right]\!\!\right]$ terminating, then $\mathbb{C}^{*}$ is terminating.
- $\mathbb{C} \subset \mathbb{C}^{*}$ 
- $\mathbb{C}^{**} = \mathbb{C}^{*}$ 

$\tau_1 \rightarrow \tau_2$ wants a unfold operation.

$$
\left[\!\!\left[\tau_1 \rightarrow \tau_2 \right]\!\!\right] = \{ e \in \text{Termn} | \forall e' \in \left[\!\!\left[ \tau_1 \right]\!\!\right], e \space e' \in \left[\!\!\left[\tau_2\right]\!\!\right]  \}
$$
不仅自己化简终止, 而且添加上任何其他化简终止的term后也化简终止.
We are manually defining a terminating set (without type safety).

### Judgements on Substitutions
Now note that not everything in the proof are closed, for example, in lambda function, there may be free variables.

What does $\left[\!\!\left[ \Gamma \vdash e:\tau \right]\!\!\right]$ mean?

Define $\left[\!\!\left[\Gamma\right]\!\!\right]$ to be any sensible substitution you come up with.
$$\left[\!\!\left[\Gamma\right]\!\!\right] = \{ \sigma \in \text{Subst}| \forall (x:\tau) \in \Gamma, x[\sigma] \in \left[\!\!\left[\tau\right]\!\!\right] \}$$
$$\left[\!\!\left[\Gamma \vdash e: \tau\right]\!\!\right] = \{\forall \sigma \in \left[\!\!\left[\Gamma\right]\!\!\right], e[\Gamma] \in \left[\!\!\left[\tau\right]\!\!\right]\}$$ 

### Foundamental Lemma (Logical Relation)

我们实际上是定义了一个参数是type的集合了, 所谓的logical relation就是term和type之间的relation. 这种思路是可扩展的.

Lemma (Fundamental Lemma):
if $\Gamma \vdash e:\tau$ is derivable, then $\left[\!\!\left[\Gamma \vdash e:\tau\right]\!\!\right]$ true.

What we are meaning here is to say the inference rule(syntax truth) preserves some property (semantic truth).

Proof. by induction on the given derivation $\mathcal{D} : \Gamma \vdash e:\tau$

1. $\mathcal{D} = \begin{array}{c} \hline \Gamma, x :\tau \vdash x:\tau \end{array}$.
   We should show, $\left[\!\!\left[\Gamma, x :\tau \vdash x:\tau\right]\!\!\right]$ is true.
   Suppose $\sigma \in \left[\!\!\left[\Gamma, x:\tau\right]\!\!\right]$,  we should show $x[\sigma] \in \left[\!\!\left[ \tau \right]\!\!\right]$. This can be proved from the definition of a 'reasonable substitution'.
2. $\mathcal{D} = \begin{array}{c} \Gamma \vdash e_1 : \tau \rightarrow \tau', \quad \Gamma \vdash e_2: \tau \\ \hline \Gamma \vdash e_1 \space e_2 :\tau'  \end{array}$
   IH: $\left[\!\!\left[\Gamma \vdash e_1 : \tau \rightarrow \tau'\right]\!\!\right]$ is true, $\left[\!\!\left[\Gamma \vdash e_2: \tau\right]\!\!\right]$ is true.
   Show: $\left[\!\!\left[\Gamma \vdash e_1 \space e_2 :\tau'\right]\!\!\right]$.
   Suppose $\sigma \in \left[\!\!\left[\Gamma\right]\!\!\right]$, we should show $(e_1 \space e_2)[\sigma] \in \left[\!\!\left[\tau'\right]\!\!\right]$
   By definition this is equivalent to $e_1[\sigma] \space e_2[\sigma]$.
   We already know that (by IH1) $e_1[\sigma] \in \left[\!\!\left[\tau \rightarrow \tau'\right]\!\!\right]$. and that $e_2 [\sigma] \in \left[\!\!\left[\tau\right]\!\!\right]$. The proof goal follows directly.
3. Things get a little more tricky when it comes to $\lambda$
   $\mathcal{D} = \begin{array}{c} \Gamma, x:\tau \vdash e : \tau' \\ \hline \Gamma \vdash \lambda x.e : \tau \rightarrow \tau'  \end{array}$
   IH: $\left[\!\!\left[\Gamma, x:\tau \vdash e : \tau'\right]\!\!\right]$ is true.
   Show: $\left[\!\!\left[  \Gamma \vdash \lambda x.e : \tau \rightarrow \tau' \right]\!\!\right]$. i.e. forall $\sigma \in \left[\!\!\left[\Gamma\right]\!\!\right]$,
   $$(\lambda x.e)[\sigma] = \lambda x. (e[\sigma]) \in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right] \iff \lambda x. (e[\sigma]) \space e_1 \in \left[\!\!\left[\tau_2\right]\!\!\right], \forall e_1 \in \left[\!\!\left[\tau_1\right]\!\!\right]$$

   Observe that
   $$\lambda x. (e[\sigma]) \space e_1 \mapsto e[\sigma,e_1/x]$$
   Since $e_1\in \left[\!\!\left[\tau_1\right]\!\!\right]$ and $\sigma \in \left[\!\!\left[\Gamma\right]\!\!\right]$, $[\sigma,e_1/x] \in \left[\!\!\left[\Gamma, x:\tau_1\right]\!\!\right]$. By IH we know $e[\sigma,e_1/x] \in \left[\!\!\left[\tau_2\right]\!\!\right]$.

   Note that we are actually taking a step forward here, in order to prove that $\lambda x. (e[\sigma]) \in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$, we should prove a lemma *Closure under expansion*.

### Closure under expansion

Lemma (Closure under expansion). For all types $\tau,$ if $e \mapsto^{*} e^{\prime}$ and $e^{\prime} \in$ $\left[\!\!\left[\tau\right]\!\!\right]$ then $e \in \left[\!\!\left[\tau\right]\!\!\right]$ as well. That is to say, $\left[\!\!\left[\tau\right]\!\!\right]^{*} \subseteq \left[\!\!\left[\tau\right]\!\!\right]$ for any $\tau$.

Proof. by induction on the syntax of the type $\tau$.
- $\tau = \text{bool}: \left[\!\!\left[\text{bool}\right]\!\!\right] = \{ \text{true, false} \}^{*} = \{ \text{true, false} \}^{**} = \left[\!\!\left[\text{bool}\right]\!\!\right]^{*}$
- $\tau = \tau_1 \rightarrow \tau_2$: We must show that if $e \mapsto^{*} e'$ and $e' \in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$, then $e \in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$.
  IH: $\left[\!\!\left[tau_1\right]\!\!\right] = \left[\!\!\left[tau_1\right]\!\!\right]^{*}$ and $\left[\!\!\left[tau_2\right]\!\!\right] = \left[\!\!\left[tau_2\right]\!\!\right]^{*}$
  Suppose $e$ and $e'$ are arbitrary expressions such that $e \mapsto^{*} e' \in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$. Showing that $e\in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$ is equivalent to show that for all $e_1 \in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$, $e\space e_1 \in \left[\!\!\left[\tau_2\right]\!\!\right]$. So let $e_1$ be an arbitrary expression in $\left[\!\!\left[\tau_1\right]\!\!\right]$. Now observe that
  $$e\space e_1 \mapsto^{*} e' e_1 \in \left[\!\!\left[\tau_2\right]\!\!\right]$$
  because $e'\in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$. Therefore, we learn from the inductive hypothesis $\left[\!\!\left[tau_2\right]\!\!\right] = \left[\!\!\left[tau_2\right]\!\!\right]^{*}$ that $e\space e_1 \in \left[\!\!\left[\tau_2\right]\!\!\right]$ as well. so $e\in \left[\!\!\left[\tau_1 \rightarrow \tau_2\right]\!\!\right]$ by definition.

Goal: Lemma: $\left[\!\!\left[\tau\right]\!\!\right] \subset Termin.$ Trivial from the lemma above.