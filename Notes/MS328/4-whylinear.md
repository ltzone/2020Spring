---
title: 【大数据分析】线性模型
url: bd-whylinear
date: 2020-03-26 18:03:39
tags: 
- Big Data Analysis

categories: 
- Courses

---

Week 4 of 2020 Spring

<!--more-->

[toc]

我们做最小二乘估计时, $\beta$的维度一般是解释变量$X$的维度加一.

$$\underset{\beta \in \mathbb{R}^{p}}{\arg \min }(\mathbb{Y}-\mathbb{X} \beta)^{\top}(\mathbb{Y}-\mathbb{X} \beta)=\left(\mathbb{X}^{\top} \mathbb{X}\right)^{-1} \mathbb{X}^{\top} \mathbb{Y}$$

## 极大似然估计

### Formulation

在数理统计中,对于来自某一总体的样本
$$X_{1}, \cdots, X_{n} \text { i.i.d. } \sim f(x, \theta)$$

对于未知参数$\theta$, 极大似然估计(MLE)
$$\hat{\theta}=\arg \max _{\theta} \prod_{i=1}^{n} f\left(X_{i}, \theta\right)$$

$$L(\theta)=\prod_{i=1}^{n} f\left(X_{i}, \theta\right)$$
被称为似然函数, 实际上是$X_1,\ldots,X_n$的联合分布密度函数. 只是在这里, 我们把视角反过来了. 概率中, 我们把$\theta$看作固定的, 统计中, 给定了样本, 这是关于$\theta$的函数.(似然函数)

### Example

如, 抛100次硬币, 得到51次正面, 49次反面. $\hat{p}=0.51$
正面向上的概率$p$,
$$L(p) = C_{100}^{51} p^{51} (10p)^{49}$$ 
我们问, 如果我们恰好可以构造一个硬币$p$, 那最可能让51次正面发生的p应该多大?

$$
\begin{aligned}
  \hat{p} = \arg \max _{p} L(p) = \arg \max_{p} p^{51} (1-p)^{49} = 0.51
\end{aligned}
$$

一个连续的例子:
$X~N(\mu,1)$, 我们做一次实验, 看到$X = 1$, 估计$\mu$是多大? $\hat{\mu}=1$ 

最后归结到一个优化问题. 常见的做法如下
注意到log(`)是单调增函数，很多时候也会考虑对数极大似然估
计(log-likelihood):
$$\begin{aligned}
\hat{\theta} &=\arg \max _{\theta} \log \left\{\prod_{i=1}^{n} f\left(X_{i}, \theta\right)\right\} \\
&=\arg \max _{\theta} \sum_{i=1}^{n} \log f\left(X_{i}, \theta\right) \\
&=\arg \max _{\theta} \frac{1}{n} \sum_{i=1}^{n} \log f\left(X_{i}, \theta\right)
\end{aligned}$$

类似于最小二乘法，我们从损失函数的角度理解MLE:

$$\begin{aligned}
\hat{\theta} &=\arg \max _{\theta} \prod_{i=1}^{n} f\left(X_{i}, \theta\right)=\arg \max _{\theta} \frac{1}{n} \sum_{i=1}^{n} \log f\left(X_{i}, \theta\right) \\
&=\arg \min _{\theta}-\prod_{i=1}^{n} f\left(X_{i}, \theta\right)=\arg \min _{\theta} \frac{1}{n} \sum_{i=1}^{n}-\log f\left(X_{i}, \theta\right)
\end{aligned}$$

如果$L(\theta_1)\leL(\theta_2)$, 那么$\theta_1$产生样本的可能性更大.

### Analysis

> 上面的损失函数与传统的损失函数有什么不同?
> 1. 必须要知道分布, f必须有具体形式
> 2. 在f不是概率函数的情况下, MLE不一定是非负的, 当然, 这不影响我们的优化问题($L(\theta) - L^{\star}$)


Pros:
- 极大似然估计理论上是**最有效**的估计(纯粹理论角度, 在概率上能够最有效地表达事件本身可能具有的随机性). 
- 极大似然估计的构造思想非常简洁,是统计思想的最好体现. 在很多参数估计或者模型估计中，极大似然估计的思想被大量使用.(很容易构造,如可以对传染病模型每一层公式构造一个极大似然估计.)
Cons:
- 极大似然估计的表现依赖于似然函数的选取,在实际数据中必须选
择**合适的总体分布**(需要具体的形式).
- 极大似然估计中的优化问题有的时候**没有显示解**(影响可解释性)或者不容易计算(得不到所需估计).

### From MLE to 最小二乘法

假定应变量Y和解释变量X有线性关系:
$$Y_i=X_i^{T}\beta + \epsilon_i, i=1,\ldots,n$$
其中$\epsilon_i$是噪音, 且均值为0, 方差为$\sigma^2$ 由于没有具体分布, 我们无法写出似然函数, 所以**必须额外假设$\epsilon_i$的分布/分布族**

假设$\epsilon_{1}, \cdots, \epsilon_{n}, \text { i.i.d. } \sim N\left(0, \sigma^{2}\right)$

$$L\left(\beta, \sigma^{2}\right)=\prod_{i=1}^{n} \frac{1}{\sqrt{2 \pi} \sigma} \exp \left\{-\frac{1}{2 \sigma^{2}}\left(Y_{i}-X_{i}^{\top} \beta\right)^{2}\right\}$$

这里我们把$\sigma^2$也当未知参数放进了模型，其在线性模型的相关假设检验中非常重要. 如果$\sigma$当成已知的也完全不影响最小二乘的估计形式.

$$\arg \max _{\beta \in \mathbb{R}^{\rho}, \sigma^{2}} \frac{1}{(\sqrt{2 \pi} \sigma)^{n}} \exp \left\{-\frac{1}{2 \sigma^{2}}(\mathbb{Y}-\mathbb{X} \beta)^{\top}(\mathbb{Y}-\mathbb{X} \beta)\right\}$$

如果只关注回归系数$\beta$部分

$$\hat{\beta}=\arg \min _{\beta \in \mathbb{R}^{p}}(\mathbb{Y}-\mathbb{X} \beta)^{\top}(\mathbb{Y}-\mathbb{X} \beta)$$


当噪音部分为正态分布时候，极大似然估计等价于最小二乘估计.

> 思考: 如果噪音不是正态分布，例如对称均匀分布、对称指数分布等，极大似然估计的形式是什么样的？

### 指数噪音

我们假定噪音不是正态分布，而是对称的指数分布，即Laplace 分布：
$$\epsilon_{i} \sim \text { Laplace }\left(0, \frac{\sigma}{\sqrt{2}}\right): f(x)=\frac{1}{\sqrt{2} \sigma} \exp \left\{-\frac{\sqrt{2}|x|}{\sigma}\right\}$$

这里为了便于联系起来,$E \epsilon_{i}=0, \operatorname{var}\left(\epsilon_{i}\right)=\sigma^{2}$, 类似于正态噪音, 我们可以写出最大似然估计
$$\arg \max _{\beta \in \mathbb{R}^{p}, \sigma^{2}} \prod_{i=1}^n f(Y_i-X_i^{T}\beta)$$

$$\arg \max _{\beta \in \mathbb{R}^{p}, \sigma^{2}} \frac{1}{(\sqrt{2} \sigma)^{n}} \exp \left\{-\frac{\sqrt{2}}{\sigma}\left\|\mathbb{Y}-\mathbb{X}^{\prime} \beta\right\|_{1}\right\}$$
$$\hat{\beta}=\arg \min \sum_{i=1}^{n}\left|Y_{i}-X_{i}^{\prime} \beta\right|$$

我们发现损失函数从l2-norm变成了l1-norm. "最小一乘法"

一个直观理解可以是, 如果我们取所有$X_i=1$, 即对于一组数据 $Y_{1}, \cdots, Y_{n}$ 正态噪音和对称指数噪音的极大似然估计正好对应样本均值和样本中位数. 在有些问题中, 中位数比均值更稳健一些, 这也可以作为最小一乘法和最小二乘法的区别.

## 最优线性投影


### 矩估计的思想
$X_1,\ldots,X_n~f(X,\theta)$, $\hat{\theta}$, 我们可以求X的n阶矩得到一个反函数, $\theta=g^{-1}(EX,EX^2,\ldots)$. 由此, 把$\bar{X}$代入, 我们就可以得到$\hat{X}$

统计中, 样本的两重性: 抽样前$X_i,Y_i$是随机变量,抽样后就变成了数

### Formulation

把样本$(X_1,Y_1), ..., (X_n,Y_n)$看成是来自于总体$(X,Y)$，我们考虑最优的线性投影：
$$\underset{\beta \in \mathbb{R}^{p}}{\arg \min } E\left(Y-X^{\top} \beta\right)^{2}$$
即从总体角度来找到最优的线性投影.

我们要根据整体分布求出最小期望. 即$g(\beta)=E\left(Y-X^{\top} \beta\right)^{2}$

简单起见, 我们假定$EX=0,EY=0$, 那么
$$\begin{aligned}
E\left(Y-X^{\top} \beta\right)^{2} &=E Y^{2}-2 E Y X^{\top} \beta+E \beta^{\top} X X^{\top} \beta \\
&=E Y^{2}-2 \beta^{\top}(E Y X)+\beta^{\top} \operatorname{cov}(X) \beta
\end{aligned}$$

记$X=\left(Z_{1}, \ldots, Z_{p}\right)^{\top}$

$$E Y X=\operatorname{cov}(X, Y)=\left(\begin{array}{c}
\operatorname{cov}\left(Y, Z_{1}\right) \\
\vdots \\
\operatorname{cov}\left(Y, Z_{p}\right)
\end{array}\right), \quad \Sigma=\operatorname{cov}(X)=\left(\operatorname{cov}\left(Z_{i}, Z_{j}\right)\right)_{p \times p}$$

### 协方差矩阵
在多元/高维数据分析中，总体协方差矩阵
$$\Sigma=\operatorname{cov}(X)=\left(\operatorname{cov}\left(Z_{i}, Z_{j}\right)\right)_{p \times p}$$
是一个非常重要的参数，其刻画了数据的离散程度(类似于一元随机变
量中的方差). 总体协方差矩阵的逆矩阵$\Omega=\Sigma^{-1}$也是一个重要的度量，一般称为精度矩阵(precision matrix)

$\Sigma$和$\Omega$是过去二十年高维统计的主要研究课题，是高斯图模型(Gaussian Graphical Model)中的核心参数.


### Solution


$$\begin{aligned}
&\arg \min E\left(Y-\alpha-X^{\top} \beta\right)^{2}\\
&\alpha \in \mathbb{R}, \beta \in \mathbb{R} p
\end{aligned}$$

Recall $\arg\min E(Y-a)^2 = EY$

所以我们可以单独解后者
$$\begin{aligned}
\beta^{*} &=\arg \min E\left((Y-E Y)-(X-E X)^{\top} \beta\right)^{2} \\
&=\arg \min \left\{\beta^{\top} \operatorname{cov}(X) \beta-2 \beta^{\top} \operatorname{cov}(X, Y)\right\} \\
&=\Sigma^{-1} \operatorname{cov}(X, Y)
\end{aligned}$$
在$\Sigma$严格正定的条件下有解

以及
$$\alpha^{*}=\underset{\alpha \in \mathbb{R}}{\arg \min } E\left(Y-\alpha-X^{\top} \beta^{*}\right)^{2}=E\left(Y-X^{\top} \beta^{*}\right)=E Y-(E X)^{\top} \beta^{*}$$

i.p ruo$cov(X,Y)=0$,即X与Y不相关, 那么$\beta^{\star}=0$

已知分布, 从参数的角度我们找到了最优的系数.

### 应用

接下来, 在实际的数据集中, 我们根据样本的方差,协方差矩阵估计参数.

$$\hat{\Sigma}=\frac{1}{n} \sum_{i=1}^{n}\left(X_{i}-\bar{X}\right)\left(X_{i}-\bar{X}\right)^{\top}, \operatorname{cov} \left( \widehat{X, Y}\right)=\frac{1}{n} \sum_{i=1}^{n}\left(Y_{i}-\bar{Y}\right)\left(X_{i}-\bar{X}\right)$$

可以得到对应估计:

$$\hat{\beta}=\hat{\Sigma}^{-1} \operatorname{cov} \left( \widehat{X, Y}\right), \hat{\alpha}=\bar{Y}-\bar{X}^{\top} \hat{\beta}$$

注意到最小二乘法中数据矩阵第一列是1，通过矩阵运算可以验证上述
结果$(\hat{\alpha},\hat{\beta})^{T}$和$\left(\mathbb{X}^{\top} \mathbb{X}\right)^{-1} \mathbb{X}^{\top} \mathbb{Y}$是完全一样的. easy to check by矩阵乘法.

### 总结

所谓最优线性投影, 最小二乘本质是在总体的角度找最好的那条线. 即我们把X Y当成随机的, 在已知他们的联合分布的情况下, 我们可以找到那条最好的线. 也就是说
$$(\alpha^{\star}, \beta^{\star} )= \underset{\alpha \in \mathbb{R}, \beta \in \mathbb{R}^{p}}{\arg \min } E\left(Y-\alpha-X^{\top} \beta\right)^{2}$$
是我们用最小二乘法在真正算的东西.

## 回归函数

### 条件期望

在最优线性投影的基础上, 我们考虑任意的函数g(·).
$$\arg \min E(Y-g(X))^{2}$$

记$Z=E(Y | X)$(条件期望, 某种程度上可以理解为是X的一个函数$E(Y|X=x)$, 表达式中仅依赖于X不依赖于Y), 我们有
$$\begin{aligned}
E(Y-g(X))^{2} &=E(Y-Z+Z-g(X))^{2} \\
&=E(Y-Z)^{2}+E(Z-g(X))^{2}+2 E(Y-Z)(Z-g(X)) \\
&=E(Y-Z)^{2}+E(Z-g(X))^{2}
\end{aligned}$$
为什么可以消掉?
$$ E(Y-Z)(Z-g(X)) = E_X E[(Y-Z)(Z-g(X))|X] = E_X (E[((Y|X)-Z)(Z-g(X))]) = 0
$$

如何解释?
- $E(Y-f(x))^2$ 与g无关. f是最优模型
  在**均方损失**下，最优的函数为$f(x)=E(Y | X=x)$ (recall $\arg \min_{a} E(Y-a)^{2}=E Y$) 
  如果我们换一个损失函数, 可能就没有这么漂亮的结果了
- $E(f(x)-g(x))^2$ 这是我们构造的模型,
  我们要找一个g, 使上面的期望值最小

### 函数簇

从数学角度, 我们在均方损失意义下, 找到的最优函数是一个条件期望, 函数f(x)的形式有无穷多种. 我们从函数簇的角度进行分析, 我们从线性空间的维度看
1. $f(x)=a$, 那么对应的基为{1}, 可以认为是1维的, 要估计就是在一维空间里面找一个数值.
2. $f(x)=a+bx$, 那么对应的基为{1,x}, 可以认为是2维的, 要估计就是在二维空间里面找一个点. 这也正是最小二乘估计的思想
3. 从泰勒展开的角度, 当然, 我们可以写$f(X)=a+a_{1} x+\cdots+a_{n} x^{n}$, $\left\{1, x, \ldots, x^{n}\right\}$, n+1维, 但我们也不希望函数空间太大, 不然很难找.(父母身高分开考虑,直观上会变好,实际效果很少)

如果考虑模型$f(x)=\operatorname{acos}(b x)+c$, 模型维度就是$\{a,b,c\}$

### 延伸
类似于最小二乘法，基于回归函数的思想考虑所有备选的回归函数f (`)
$$\hat{f}(x)=\arg \min _{f} \frac{1}{n} \sum_{i=1}^{n}\left(Y_{i}-f\left(X_{i}\right)\right)^{2}$$

如果对函数f ()不加任何限制，直观上
- 得到的估计就为经过每一个观察值的任意函数曲线(如果出现Xi有重合的情形，估计函数应该经过平均值点)。
- 这样得到的估计函数很多时候会非常扭曲，严重的过度拟合(over-tting, 在训练集上表现完美，但是测试集上可能让人失望).
- 奥卡姆剃刀


### Penalized Regression

出现这个问题的原因是，我们让回归函数过于随意了. 可以考虑对函数
的光滑性加上一定的限制条件，常用的形式为：

在传统的均方损失下, 我们增加了一个惩罚项.

$$\hat{f}(x)=\arg \min _{f} \frac{1}{n} \sum_{i=1}^{n}\left(Y_{i}-f\left(X_{i}\right)\right)^{2}+\lambda \int\left(f^{\prime \prime}(x)\right)^{2} d x$$

其中$\lambda \geq 0$为调节参数(tuning parameter). 等价的优化形式为

$$\hat{f}(x)=\arg \min _{f} \frac{1}{n} \sum_{i=1}^{n}\left(Y_{i}-f\left(X_{i}\right)\right)^{2}, \text { subject to } \int\left(f^{\prime \prime}(x)\right)^{2} d x \leq t$$

优化的角度上述两个问题是完全等价的，即$\lambda$和t有一一对应关系.


### Splines

这里$\left(f^{\prime \prime}(x)\right)^{2}$的作用就是尽量让函数光滑，特别的$f^{\prime \prime}(x)=0$对应的是线性函数：
- 而$\lambda$的大小(或者t的大小)体现了我们希望所得函数的光滑程度。
- 调节参数选取和样本个数有很大关系。例如样本不是很多，这时候$\lambda$选取的应该大一点，希望得到的回归函数尽量简单一点。反之，如果有足够多的样本，调节参数就可以小一点，我们可以训练出复杂的回归函数.
两个极端情况是：
- $\lambda=0$ 即不考虑惩罚，得到的函数是经过所有点(或平均)的函数.
- $\lambda=\infty$ 对应$f^{\prime \prime}(x)=0$,得到的估计就是最小二乘估计.
给定$\lambda$,上述优化问题的解对应的是**样条函数**(Spline).