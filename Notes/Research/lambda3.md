---
title: 【Lambda Calculus】Recursive Functions
url: lambda-3
date: 2020-03-25 14:41:40
tags: 
- Lambda Calculus

categories: 
- Research

---

Week 4 of 2020 Spring.

<!--more-->

[toc]

## Basic Definition

定义整数及整数上的递归函数的syntax
```
e ::= ...| Z | S (e)
      | rec (e1, e2, x.y.e3)
或者我们可以写成
e ::= ...| Z | S (e)
      | rec e as {Z => e0 | S x with y => e1}
```

Typing Rules:
```
tau = ... | Nat

1. --------------------------
   Gamma |- Z : Nat
  
2. Gamma |- e : Nat 
   --------------------------
   Gamma |- S e : Nat

3. Gamma |-- e1: nat,
   Gamma |-- e2: tau
   Gamma |-- e3: nat -> tau -> tau
   ---------------------------
   Gamma |-- rec(e1,e2,e3):tau

   Gamma |-- e1: nat,
   Gamma |-- e2: tau
   Gamma x:nat, y(=f(x)):tau |-- e3'(=f(x+1)): tau
   ---------------------------
   Gamma |-- rec(e1,e2,lambda x. lambda y. e3'):tau
```


## Values and Evaluation
$$
\begin{array}{c}
\hline
Z:val \\
\end{array}
$$


lazy:Haskell (easier to build programs)
$$
\begin{array}{c}
\hline
S e:val \\
\end{array}
$$

eager:Ocaml... (easier to know the cost of things)
$$
\begin{array}{c}
e: val \\
\hline
S e:val \\
\end{array}
$$

> reference: why (lazy) functional programming matters by Hohn Huges.

Then we have 
```
---------------------------
rec Z as Z -> e0 | S x with y -> e1 |--> e0

-------------------------------
rec S e as Z -> e0 | S x with y -> e1 |--> 
e1 [e/x, (rec e as z-> e0 | S x with y -> e1)/y]
```

This is why we call-by name, since expressions are replaced by other expressions instead of value.

Evaluation Context
```
E ::= ... | rec E as {...}
```
```
e |--> e'
------------------------
rec e as (...) |-> rec e' as (....)
```



For call by value
```
E ::= ... | rec E as {...} | S E
```
```
e |--> e'
------------------------
S e |--> S e'
```

## Formula for doing recursive types

We assume that the recursive function will terminate. Type rules:
$$\tau ::= \ldots | \mu_{\alpha.\tau}$$

One interpretation is identical

$$
\mu_{\alpha.\tau} = \tau[\mu_{\alpha.\tau}/\alpha]
$$

Another interpretation is convertable
$$
\mu_{\alpha.\tau} \approx \tau[\mu_{\alpha.\tau}/\alpha]
$$

For the latter, we need to define conversions(fold and unfold).
$$
e ::= ... | \text{fold} (e) (\leftarrow) | \text{unfold} (e) (\rightarrow) 
$$
What's the type of fold and unfold?

$$
\begin{array}{c}
\Gamma \vdash e :\tau [ \mu_{\alpha.\tau}/\alpha] \\
\hline
\Gamma \vdash \text{fold}(e): \mu_{\alpha. \tau } 
\end{array}
$$

$$
\begin{array}{c}
\Gamma \vdash e :\mu_{\alpha. \tau}  \\
\hline
\Gamma \vdash \text{unfold}(e): \tau [ \mu_{\alpha.\tau}/\alpha]
\end{array}
$$

Now types have a variable instead of constant
$$
\tau ::= ... | \mu_{\alpha.\tau} | \alpha
$$
But the variable are always closed concerning the fold unfold rules, where $\alpha$ and $\tau$ can be inferred by the type we are evaluating implicitly.

### Call-by-name semantics for unfold/fold

(We specify that `fold e: val`)

$$
(\alpha) \quad
\begin{array}{c}
\hline
\text{unfold}(\text{fold}(e)) \mapsto e
\end{array}
$$

$$
(\beta) \quad
\begin{array}{c}
e \mapsto e' \\
\hline
\text{unfold}(e) \mapsto \text{unfold}(e')
\end{array}
$$

$$
(\eta) \quad
\begin{array}{c}
\hline
\text{fold}(\text{unfold}(e)) = _{\eta} e : \mu_{\alpha.\tau} \\
\end{array}
$$


$\eta$ rule serves as an extensial proposition. 用于我们的说明, 并不属于程序的执行的语义

### Eager version: Call-by-value

$$
\begin{array}{c}
\begin{array}{c}
e:val\\
\hline
\text{fold}(e):val
\end{array} \\ \\
\begin{array}{c}
e:val\\
\hline
\text{unfold} (\text{fold} (e)) \mapsto e
\end{array} \\ \\
\begin{array}{c}
e \mapsto e'\\
\hline
\text{fold} (e) \mapsto \text{fold}(e')
\end{array} \\ \\
\text{+ other parts above}
\end{array}
$$

fold和unfold语义描述的是我们对expression执行unpack和pack的先后关系.

## Recursive Types
Now we use these general rules to figure out recursive types. 
朴素的Type定义中, $\text{Nat} \approx \text{unit} + \text{Nat}$
in order to get rid of circulating, 我们引入了$\mu_{\alpha.\tau}$表达
$\alpha$ is the recursive occurence of something.

对自然数
$$
\begin{array}{c}
\text{Nat} = \mu_{\alpha.unit} + \alpha \\
Z = \text{fold} (l \cdot \diamondsuit ) \\
S\space e = \text{fold} (r \cdot e)
\end{array}
$$

对列表,我们也可以这样定义
$$
\begin{array}{c}
\text{List} \space \tau \approx \text{unit} + (\tau \times \text{List} \space \tau)\\
\Leftrightarrow
\begin{array}{l}  
\text{List} \space \tau = \mu_{\alpha.\text{unit}} + (\tau \times \alpha) \\
\text{nil} = \text{fold} (l \cdot \Diamond) \\
\text{cons }e\space e' = \text{fold} (r \cdot \left< e , e' \right>) 
\end{array}
\end{array}
$$

这里$l$和$r$可以理解为是一个标识label

利用这样的定义, 我们可以写出case analysis更formal的定义
$$
\begin{array}{c}
\begin{array}{l}
  \text{case e of} \\
  \text{| Z} \Rightarrow e_0 \\
  \text{| S e} \Rightarrow e_1
\end{array}=
  \begin{array}{l}
    \text{case unfold(e) of} \\
  \text{| } l \cdot \alpha \text{ (unit value that we don't need)} \Rightarrow e_0 \\
  \text{| } r \cdot x \text{ (the actual number $x$)}\Rightarrow e_1
  \end{array}
\end{array}
$$


For recursor

$$
\begin{array}{l}
\omega = \lambda x. x \space x \\
\Omega  = \omega \space \omega \\
\Rightarrow \Omega \mapsto \Omega
\end{array}
$$

What's the type of self-application?

Now, there is.

Note
$$
\begin{array}{c}
  \longleftarrow^{\text{unfold}}\\
  \mu_{\alpha.(\alpha\rightarrow\tau)} \rightarrow \tau \approx  \mu_{\alpha.(\alpha\rightarrow\tau)} \\ 
  \longrightarrow^{\text{fold}}\\
\end{array}
$$
Hence we can derive the type of the recursor.


### Application of Recursion

$$
\begin{array}{l}
\omega : \mu_{\alpha.(\alpha\rightarrow\tau)}\rightarrow \tau\\
\omega = \lambda x:\mu_{\alpha.(\alpha\rightarrow\tau)}. \text{unfold}(x)[:\mu_{\alpha.(\alpha\rightarrow\tau)}\rightarrow \tau] \space x \\
\Omega : \tau \\
\begin{array}{ll}
\Omega = \omega \space & (\text{fold} (\omega)) \\
& \text{↑ which is } \mu_{\alpha.(\alpha\rightarrow\tau)} 
\end{array}  \\
\Rightarrow \text{Type Checks!}
\end{array}
$$

$\Omega$ isn’t very useful; a reduction step just regenerates the same again. But what happens if we have something like  $\Omega$ that changes a bit every step.

Given a function on $\tau$, $y$ gives back a fixpoint. 

$$y: (\tau \rightarrow \tau) \rightarrow \tau$$


$$y = \lambda f:\tau \rightarrow \tau. (\lambda x:\mu_{\alpha \rightarrow \tau}. f ((\text{unfold } x) \space x))$$

函数值中的部分实际上是

$$ \text{fold} (\lambda x :\mu_{\alpha \rightarrow \tau}. f ((\text{unfold } x) \space x)) $$

So actually $y$ takes several steps from $f$ to a fixpoint.

$$
\begin{aligned}
  \Omega = \omega \space (\text{fold } \omega) & \mapsto (\text{unfold } (\text{fold } \omega)) \space (\text{fold } \omega) \\
  & \mapsto \omega \space (\text{fold } \omega)
\end{aligned}
$$

This is how we get 
$$
y\space f = f\space (y\space f)
$$

### Example

Why is a the fixed-point generator $Y$ useful? Because it can be used to implement recursion, even though there is no recursion in the $\lambda$ -calculus to begin with. For example, this recursive definition of multiplication
$$
\text {times}=\lambda x . \lambda y . \text { if } x \leq 0 \text { then } 0 \text { else } y+(\text {times}\space(x-1) \space y)
$$
can instead be written non-recursively by using $Y$ like so:
$$
\begin{aligned}
\text {timesish} &=\lambda \text {next.} \lambda x . \lambda y . \text { if } x \leq 0 \text { then } 0 \text { else } y+(\text {next }\space \space (x-1) \space \space y) \\
\text {times} &=Y \text { timesish}
\end{aligned}
$$
Now check that times does the same thing as the recursive definition above:
$$
\begin{aligned}
\text{times}\space 0 \space y & = Y \space\space \text{timesish} \space\space 0 \space\space y \\
&\mapsto \text { timesish (}  Y  \space\space \text {timesish) } \space\space 0 \space\space y \\
& \mapsto^{*} \text { if } 0 \leq 0 \text { then } 0 \text { else } y+(Y \space\space \text { timesish } \space\space (0-1) \space\space y)\\
&\mapsto 0
\end{aligned}
$$

$$
\begin{aligned}
\text {times }\space\space(x+1)\space\space y &=Y \space\space \text { timesish }\space\space(x+1)\space\space y \\
&\mapsto \text { timesish (} Y \space\space \text { timesish) } \space\space (x+1) \space\space y \\
&\mapsto^{*} \text { if }(x+1) \leq 0 \text { then 0 else } y+(Y \text { timesish }\space\space (x+1-1) \space\space y) \\
&\mapsto^{*} y+(Y \text { timesish }\space\space(x+1-1)\space\space  y) \\
&\mapsto^{*} y+(\text { times}\space\space x\space\space y)
\end{aligned}
$$