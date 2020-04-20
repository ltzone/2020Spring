---
title: 【Information Theory】Differential Entropy 2
url: it-diff2
date: 2020-04-20 08:03:26
tags: 
- Information Theory

categories: 
- Courses

---

Week 8 of 2020 Spring.

<!--more-->

[toc]

## Correlated Gaussian
我们计算两个随机变量的互信息，这里以联合高斯分布为例。
(Mutual information between correlated Gaussian random variables with correlation $\rho$ ) Let $(X, Y) \sim \mathcal{N}(0, K),$ where
$$
\boldsymbol{K}=\left[\begin{array}{cc}
\boldsymbol{\sigma}^{2} & \boldsymbol{\rho} \boldsymbol{\sigma}^{2} \\
\boldsymbol{\rho} \boldsymbol{\sigma}^{2} & \boldsymbol{\sigma}^{2}
\end{array}\right]
$$
$I(X ; Y) ?$

$$
\begin{array}{c}
h(X)=h(Y)=\frac{1}{2} \log 2 \pi e \sigma^{2} \\
h(X, Y)=\frac{1}{2} \log (2 \pi e)^{2}|K|=\frac{1}{2} \log (2 \pi e)^{2} \sigma^{4}\left(1-\rho^{2}\right) \\
I(X ; Y)=h(X)+h(Y)-h(X, Y)=-\frac{1}{2} \log \left(1-\rho^{2}\right)
\end{array}
$$
- $\rho=0, X$ and $Y$ are independent and $I$ is 0
- $\rho=\pm 1, X$ and $Y$ are perfectly correlated and $I$ is $\infty$

## Maximum Entropy with Constraints

$E(X^2),Var(X)$给定的情况下，高斯分布最大化微分熵。

> - Let the random variable $X \in R$ have mean $\mu$ and variance $\sigma^{2}$. Then
>   $$
>   h(X) \leq \frac{1}{2} \log 2 \pi e \sigma^{2}
>   $$
>   with equality iff $X \sim \mathcal{N}\left(\boldsymbol{\mu}, \boldsymbol{\sigma}^{2}\right)$
> - Let the random variable $X \in R$ satisfy $E X^{2} \leq \sigma^{2} .$ Then
>   $$
>   h(x) \leq \frac{1}{2} \log 2 \pi e \sigma^{2}
>   $$
>   with equality iff $X \sim \mathcal{N}\left(0, \sigma^{2}\right)$

证明域平均分布最大化离散熵的证明如下，我们用相对熵推出。

1. Let $X_{G} \sim \mathcal{N}\left(\mu, \sigma^{2}\right) .$ Consider 
   $$\boldsymbol{D}\left(X \| X_{G}\right) \geqq \mathbf{0}$$
  Then
  $$
  \int f \log \frac{f}{g} \geq 0
  $$
  把对数函数展开，由于$g$是高斯分布，可以进一步展开。
  $$h(X)=h(f) \leq-\int f \log g=-\int f \log \frac{1}{\sqrt{2 \pi \sigma^{2}}}+f\left(-\frac{(x-\mu)^{2}}{2 \sigma^{2}}\right)$$
  由于右侧都是常数，可代入化简。
  $$h(X) \leq \frac{1}{2} \log 2 \pi \sigma^{2}+\frac{1}{2}=\frac{1}{2} \log 2 \pi e \sigma^{2}$$
2. $\operatorname{Var}(X)=E\left(X^{2}\right)-E(X)^{2} \leq \sigma^{2} \cdot \Rightarrow$ Case 1

使用这两个结论时一定要注意是否存在确定的均值、方差或二阶矩是否存在上界。

## Maximum Entropy

最大熵原理在不同的限制下可以得到不同的结论。（详见Cover Ch.12）

Consider the following problem: Maximize the entropy $h(f)$ over all probability densities $f$ satisfying （$++$条件）
1. $f(x) \geq 0,$ with equality outside the support 非负性
2. $\int_{s} f(x) d x=1$ 规范性
3. $\int_{S} f(x) r_{i}(x) d x=\alpha_{i}$ for $1 \leq i \leq m .\left(r_{i}(x) \text { is a function of } \right) x$. Thus, $f$ is a density on support set $S$ meeting certain moment constraints $\alpha_{1}, \alpha_{2}, \ldots, \alpha_{m}$ 即某些关于$x$的函数的均值是一定的。

> Theorem 12.1.1 (Maximum entropy distribution) Let 
> $$f^{*}(x)=f_{\lambda}(x)=e^{\lambda_{0}+\sum_{i=1}^{m} \lambda_{i} r_{i}(x)}$$
> $x \in S,$ where $\lambda_{0}, \ldots, \lambda_{m}$ are chosen so that $f^{*}$ satisfies $(++) .$ Then $f^{*}$ uniquely maximizes $h(f)$ over all probability densities $f$ satisfying constraints $(++)$
> 最大熵的分布是$f^{*}$取到的，但其中一些系数需要通过$\lambda_i$作为待定系数，还需更多条件可确定待定系数。

**Proof.**
$$\begin{aligned}
h(g) &=-\int_{S} g \ln g \\
&=-\int_{S} g \ln \frac{g}{f^{*}} f^{*} \\
&=-D\left(g \| f^{*}\right)-\int_{S} g \ln f^{*} \\
& \stackrel{(a)}{\leq}-\int_{S} g \ln f^{*} \\
& \stackrel{(b)}{=}-\int_{S} g\left(\lambda_{0}+\sum \lambda_{i} r_{i}\right) \\
& \stackrel{(c)}{=}-\int_{S} f^{*}\left(\lambda_{0}+\sum \lambda_{i} r_{i}\right) \\
&=-\int_{S} f^{*} \ln f^{*} \\
&=h\left(f^{*}\right)
\end{aligned}$$

where (a) follows from the nonnegativity of relative entropy, (b) follows from the definition of $f^{*},$ and $(\mathrm{c})$ follows from the fact that both $f^{*}$ and $g$ satisfy the constraints. Note that equality holds in (a) if and only if $g(x)=f^{*}(x)$ for all $x,$ except for a set of measure $0,$ thus proving uniqueness.

The same approach holds for discrete entropies and for multivariate distributions.

**Examples.**
- Let $S=[a, b],$ with no other constraints. Then the maximum entropy distribution is the uniform distribution over this range.
- $S=[0, \infty)$ and $E X=\mu .$ Then the entropy-maximizing distribution is
  $$
  f(x)=\frac{1}{\mu} e^{-\frac{x}{\mu}}, \quad x \geq 0
  $$
- $S=(-\infty, \infty), E X=\alpha_{1},$ and $E X^{2}=\alpha_{2} .$ The maximum entropy distribution is $\mathcal{N}\left(\alpha_{1}, \alpha_{2}-\alpha_{1}^{2}\right)$

## Hadamard's Inequality

$K$ is a nonnegative definite symmetric $n \times n$ matrix. Let $|K|$ denote the determinant of $K$
> Theorem (Hadamard) $|K| \leq \prod K_{i i},$ with equality iff $K_{i j}=0, \quad i \neq j$

**Proof.**
Let $X \sim \mathcal{N}(0, K) .$ Then
$$
\frac{1}{2} \log (2 \pi e)^{n}|K|=h\left(X_{1}, X_{2}, \ldots, X_{n}\right) \leqq \Sigma h\left(X_{i}\right)=\sum_{i=1}^{n} \frac{1}{2} \log 2 \pi e\left|K_{i i}\right|
$$
with equality iff $\left.X_{1}, X_{2}, \ldots, X_{n} \text { are independent (i.e., } K_{i j}=0, i \neq j\right)$

idea：矩阵转化为多元高斯分布，联合分布熵小于边缘分布熵的和。
remark：熵是一个基础的物理量，可以用来证明很多不等式(Cover Ch 17.9, 17.10)，比如一系列有关正定矩阵的性质
- $\log |K|$ is concave
- $\log \left(\left|K_{n}\right| /\left|K_{n-p}\right|\right)$ is concave in $K_{n}$
- $\left|K_{n}\right| /\left|K_{n-1}\right|$ is concave in $K_{n}$

## Balanced Information Inequality

平衡信息不等式：离散熵与微分熵的同和不同
Differences between inequalities of the discrete entropy and differential entropy
- Both $H(X, Y) \leq H(X)+H(Y)$ and $h(X, Y) \leq h(X)+h(Y)$ are valid
- $H(X, Y) \geq H(X)$ but neither $h(X, Y) \geq h(X)$ nor $h(X, Y) \leq h(X)$ is valid
Take $H(X, Y, Z) \leq \frac{1}{4} H(X)+\frac{1}{2} H(Y, Z)+\frac{3}{4} H(Z, X)$ for example.
Count the weights of random variables $X, Y, Z$ in both sides $X: 1,1 ; Y: 1, \frac{1}{2} ; Z: 1, \frac{5}{4}$ 定义$X,Y,Z$的净权重。
The net weights of $X, Y, Z$ are $0, \frac{1}{2},-\frac{1}{4}$

比如，下面的不等式是平衡的：
Balanced: If the net weights of $X, Y, Z$ are all zero.
$$
h(X, Y) \leq h(X)+h(Y) \text { and } h(X, Y, Z) \leq \frac{1}{2} h(X, Y)+\frac{1}{2} h(Y, Z)+\frac{1}{2} h(Z, X)
$$

> 对更为一般的情况，
> Let $[n]:=\{1,2, \ldots, n\} .$ For any $\alpha \subseteq[n],$ denote $\left(X_{i}: i \in \alpha\right)$ by $X_{\alpha} .$ For example, $\alpha=\{1,3,4\},$ we denote $X_{1}, X_{3}, X_{4}$ by $X_{(1,3,4)}$ for simplicity.
> - We could write any information inequality in the form $\Sigma_{\alpha} w_{\alpha} H\left(X_{\alpha}\right) \geq 0$ or $\Sigma_{\alpha} w_{\alpha} h\left(X_{\alpha}\right) \geq 0$
> - An information inequality is called balanced if for any $i \in[n]$, the net weight of $X_{i}$ is zero.
> - The linear continuous inequality $\Sigma_{\alpha} w_{\alpha} h\left(X_{\alpha}\right) \geq 0$ is valid if and only if its corresponding discrete counterpart $\Sigma_{\mathrm{g}} w_{\mathrm{g}} H\left(X_{\mathrm{g}}\right) \geq 0$ is valid and balanced.
> 由此，我们可以建立微分熵不等式和离散熵不等式的关系。这个不等式是正确的**当且仅当**它对应的离散熵不等式是正确的且平衡的。

Ref: Balanced Information Inequalities, T. H. Chan, IEEE Transactions
on Information Theory, Vol. 49 , No. 12 , December 2003

## Han’s Inequality

Let $\left(X_{1}, X_{2}, \ldots, X_{n}\right)$ have a density, and for every $S \subseteq\{1,2, \ldots, n\},$ denoted by $X(S)$ the subset $\left\{X_{i}: i \in S\right\} .$ Let
$$
\begin{array}{c}
h_{k}^{(n)}=\frac{1}{\left(\begin{array}{c}
n \\
k
\end{array}\right)} \sum_{S:[S]=k} \frac{h(X(S))}{k} \\
g_{k}^{(n)}=\frac{1}{\left(\begin{array}{l}
n \\
k
\end{array}\right)} \sum_{S:|S|=k} \frac{h\left(X(S) | X\left(S^{c}\right)\right)}{k}
\end{array}
$$

从n个随机变量中取k个，求联合熵、条件熵。

When $n=3$,
$$\begin{aligned}
h_{1}^{(3)} &=\frac{H\left(X_{1}\right)+H\left(X_{2}\right)+H\left(X_{3}\right)}{3} \geq h_{2}^{(3)}=\frac{H\left(X_{1}, X_{2}\right)+H\left(X_{2}, X_{3}\right)+H\left(X_{3}, X_{1}\right)}{3} \\
& \geq h_{3}^{(3)}=H\left(X_{1}, X_{2}, X_{3}\right)
\end{aligned}$$

$$\begin{aligned}
g_{1}^{(3)} &=\frac{H\left(X_{1} | X_{2}, X_{3}\right)+H\left(X_{2} | X_{1}, X_{3}\right)+H\left(X_{3} | X_{1}, X_{2}\right)}{3} \\
& \leq g_{2}^{(3)}=\frac{H\left(X_{1}, X_{2} | X_{3}\right)+H\left(X_{2}, X_{3} | X_{1}\right)+H\left(X_{3}, X_{1} | X_{2}\right)}{3} \\
& \leq g_{3}^{(3)}=H\left(X_{1}, X_{2}, X_{3}\right)
\end{aligned}$$

> Han's inequality:
> $h_{1}^{(n)} \geq h_{2}^{(n)} \ldots \geq h_{n}^{(n)}=H\left(X_{1}, X_{2}, \ldots, X_{n}\right)=g_{n}^{(n)} \geq \cdots \geq g_{2}^{(n)} \geq g_{1}^{(n)}$



## Information Heat


### Heat Equation

- Heat equation (Fourier): Let $x$ be the position and $t$ be the time, 热传导方程。**（它与高斯信道是等价的）**
  $$\frac{\partial}{\partial t} f(x, t)=\frac{1}{2} \frac{\partial^{2}}{\partial x^{2}} f(x, t)$$
- Let $X$ be any random variable with a density $f(x)$. Let $Z$ be an independent normally distributed random variable with zero mean and unit variance, $Z \sim \mathcal{N}(0,1) .$ Let
  $$Y_{t}=X+\sqrt{t} Z$$
  The **probability density function** $f(y ; t)(f(y ; t) \text { is a function in } y, \text { not } t)$ of $Y_{t}$ **satisfies heat equation**
  $$f(y ; t)=\int f(x) \frac{1}{\sqrt{2 \pi t}} e^{\frac{(y-x)^{2}}{2 t}} d x$$
  高斯信道的输出信号与热传导方程具有一一对应的关系。

### Entropy and Fisher Information
对连续型随机变量定义一个新的信息量， Fisher Information

> Fisher information: Let $X$ be any random variable with density $f(x)$. Its Fisher information is given by
> $$
> I(x)=\int_{-\infty}^{+\infty} f(x)\left[\frac{\frac{\partial}{\partial x} f(x)}{f(x)}\right]^{2} d x
> $$
- Let $X$ be any random variable with a density $f(x)$. Let $Z$ be an independent normally distributed random variable with zero mean and unit variance. Let $Y_{t}=X+\sqrt{t} Z$
  $$\frac{\partial}{\partial t} h\left(Y_{t}\right)=\frac{1}{2} I\left(Y_{t}\right)$$ 表明信息量与统计量之间也存在关联。
- Let $f(y, t) \text { (or } f)$ be the p.d.f of $Y_{t}$
  $$\begin{array}{c}
  \frac{\partial}{\partial t} h\left(Y_{t}\right)=\frac{1}{2} I\left(Y_{t}\right)=\frac{1}{2} \int \frac{f_{y}^{2}}{f} d y \geq 0 \\
  \frac{\partial^{2}}{\partial t^{2}} h\left(Y_{t}\right)=-\frac{1}{2} \int f\left(\frac{f_{y y}}{f}-\frac{f_{y}^{2}}{f^{2}}\right)^{2} d y \leq 0
  \end{array}$$
  $h(Y_t)$关于t是一个递增的凹函数。

- When $X$ is Gaussian $\mathcal{N}(0,1)$
  $$h\left(Y_{t}\right)=\frac{1}{2} \log 2 \pi e(1+t)$$
  对高斯分布的输入，n阶导数可求，且符号为
  All the derivatives alternate in signs: $+,-,+,-, \dots$

### Higher Order Derivatives of ℎ(𝑌𝑡)

(Cheng 2015) Let $X$ be any random variable with a density $f(x)$. Let $Z$ be an independent normally distributed random variable with zero mean and unit variance. Let $Y_{t}=X+\sqrt{t} Z$ and $f(y, t) \text { (or } f)$ be the p.d.f of $Y_{t} .$ Then
$$
\frac{\partial^{3}}{\partial t^{3}} h\left(Y_{t}\right) \geq 0 \text { and } \frac{\partial^{4}}{\partial t^{4}} h\left(Y_{t}\right) \leq 0
$$
Conjecture: When $n$ is even, $\frac{\partial^{n}}{\partial t^{n}} h\left(Y_{t}\right) \leq 0,$ otherwise $\frac{\partial^{n}}{\partial t^{n}} h\left(Y_{t}\right) \geq 0$

Ref: F. Cheng and Y. Geng, Higher Order Derivatives in Costa's Entropy Power Inequality

## EPI and FII

> (Shannon 1948, Entropy power inequality (EPI)) If $X$ and $Y$ are independent random $n$ -vectors with densities, then
> $$e^{\frac{2}{n} h(X+Y)} \geq e^{\frac{2}{n} h(X)}+e^{\frac{2}{n} h(Y)}$$
若对随机变量：
$$e^{2 h(X+Y)} \geq e^{2 h(X)}+e^{2 h(Y)}$$
- 也可以互推FII不等式，Fisher information inequality (FII)
  $$\frac{1}{I(X+Y)} \geq \frac{1}{I(X)}+\frac{1}{I(Y)}$$
- Most profound result in Shannon's 1948 paper
- EPI can imply some very fundamental results 
  - Uncertainty principle in quantom physics
  - Young's inequality 
  - Nash's inequality 
  - Cramer-Rao bound

References:
- T. Cover, Information theoretic inequalities, 1990
- O. Rioul , “Information Theoretic Proofs of Entropy Power Inequalities,” 2011