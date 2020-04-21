---
title: 【Computer Composition】The Processor
url: cc-processor
date: 2020-04-20 15:18:36
tags: 
- Computer Composition

categories: 
- Courses

---

Week 8 of 2020 Spring.

<!--more-->

[toc]

## Introduction

![](img/04-20-15-22-12.png)

Recall: 我们此前的大部分指令，前半部分（解析命令，取数）基本相同，后半部分则大不相同（算，读，写）

Higher-Order Abstraction

![](img/04-20-15-22-45.png)

不同的指令实际上是在激活不同的模块，选择不同的数据流进行实现。那么，如果我们能够设计一个方案，在合适的时候设置合适的控制信号，就能够让数据流通道跑起来，那我们就实现了指令的功能。因此，下面我们的重点就放在了Controller上。

此外，对时序逻辑电路，我们还要确保状态的锁存，否则会出现振荡电路。

![](img/04-20-15-29-56.png)
