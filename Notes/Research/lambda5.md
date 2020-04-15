---
title: 【Lambda Calculus】Polymorphism
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
J ::= \Theta ; \Gamma \vdash e:\tau \space | \space \Theta \vdash \tau : \star \quad FV(\tau) \subset \Theta
$$

## Typing Rules

