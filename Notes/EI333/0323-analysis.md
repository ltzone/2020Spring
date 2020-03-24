---
title: 【Software Engineering】Analysis
url: se-analysis
date: 2020-03-23 10:01:31
tags: 
- Software Engineering

categories: 
- Courses

---

Week 4 of 2020 Spring

<!--more-->

[toc]

## Models for Analysis

### What is a good model

关系保持准则 Relationships, which are valid in reality R, are also valid in model M.
- I : Mapping of real things in reality R to abstractions in the model M abbildet(Interpretation)
- $f_M$: relationship between abstractions in M
- $f_R$: relationship between real things in R

In a good model the following diagram is commutative:
[It preserves relationships among the objects it represents.]
![](img/03-23-10-15-30.png)

### Models of models of models

在以往模型基础上建立新的模型 Modeling is relative. We can think of a model as reality and can build another model from it (with additional abstractions).
![](img/03-23-10-17-00.png)
一层层模型的development体现的是软件开发的生命周期过程.

### Analysis Model
分析阶段, 我们需要创建下面三类模型:
- Functional model: user cases and scenarios
  - Use case diagram
- **Analysis** object model: class and object diagrams
  - Class Diagram
  - 区分此后design阶段的object model
- Dynamic model: state machine and sequence diagrams
  - statechart diagram
  - sequence diagram
  - ...... (activity diagram, etc)
![](img/03-23-10-19-18.png)

分析阶段的模型和前后开发过程的关系
![](img/03-23-10-21-28.png)

提醒: analysis阶段承上启下, 但仍然是在需求的大阶段内, 依然是user-level concepts(即object model反应的是user相关的概念)
- 数据库, 子系统, 网络, 等概念不应该出现.
- 避免技术术语的出现, 见下图
- 过早的决策可能会产生非最优的结果
![](img/03-23-10-24-15.png)



## Activities during object modeling
七个步骤间存在迭代, 不一定是承接的

Main goal: Find the important abstractions
Steps during object modeling
1. Object identification 实际是在找类
   - Identifying Entity Objects
   - Identifying Boundary Object
   - Identifying Control Objects
2. Mapping Use Cases to Objects with Sequence Diagrams 建立动态模型, 同时也帮助我们找到更多类
3. Modeling Interactions among Objects with **CRC Cards**(class responsbility cards)
4. Identifying Associations, Aggregates and Attributes
5. Modeling State-Dependent Behavior of Individual Objects 如果单个对象有多个状态
6. Modeling Inheritance Relationships 类与类之间是否存在继承关系
7. Reviewing

Order of steps
- Goal: get the desired abstractions
- Order of steps secondary, only a heuristic
- **Iteration** is important


### Object Identifications

- Identify the **boundaries** of the system 开发财务系统还是开发企业管理系统, 哪些是系统的内部对象, 哪些是与系统交互的对象
- Identify the **important** **entities** in the system
- Object identification is crucial to object-oriented modeling
- Basic assumption: 
  1. We can find  the  objects  for a new software system (Forward Engineering) 从头开始找起
  2. We can identify the  objects in  an existing system  (Reverse Engineering) 从代码找起

- The application domain has to be analyzed. 
- Depending on the purpose of the system different objects might be found
  - How can we identify the purpose of a system?
  - **Scenarios and use cases**
- Another important problem: Define system boundary. 
  - What object is inside, what object is outside?

#### Pieces of an object model

object model不止是classes
- Classes
- Associations (Relations)
- Attributes
- Operations

#### Object Types

我们可以按照对象的类别识别对象. 软件工程领域非常重要的三分类:
- Entity Objects 实体类
  - Represent the persistent information tracked by the system (Application domain objects, “Business objects”)
  - 生产力
- Boundary Objects 边界类
  - Represent the interaction between the user and the system
  - 交互
- Control Objects: 控制类
  - Represent the control tasks performed by the system
  - 管理者
- Object types originated in Smalltalk: 推广之, 在系统开发中, 也会存在对应的三部分架构模式
  - Model 业务代码, View 交互, Controller 协调单元(MVC)

为什么我们要按照三个类别识别对象?
Recall: 软件开发的挑战: complexity and **change**
- Both **interface** and **control** of the system are more likely to change than the application domain [model] UI一定是变化最大的, 需要单独提出
- Paradox: The static information model from analysis is more stable, yet the designed representation is most likely to change [implementation]
- David Parnas invented **the Information Hiding Principle** and recommended **encapsulation of data structures** for this reason. 面向对象方法学可以良好的支持数据隐藏和封装

#### How to find objects
具体的识别对象的方法:
Finding objects is the central piece in object modeling
- Learn about problem domain: Observe your client
- Apply general world knowledge and intuition
- **Take the flow of events and find participating objects in use cases**
- **Do a syntactic analysis** of problem statement,  scenario  or flow of events 
  - Abbott Textual Analysis, 1983, also called noun-verb analysis
    - Nouns are good candidates for classes 
    - Verbs are good candidates for operations
- **Apply design knowledge**
  - 在一些设计模式中, 要求提供一些类
  - Distinguish different types of objects [recognition/discrimination]
- Try to establish a taxonomy 分类法	[inheritance discovery]
我们重点介绍三类重点方法.

#### Finding Participating Objects in Use Cases

拿到use case, 看 flow of events中重点的六样东西
- Find **terms** that developers or users need to clarify in order to understand the flow of events
- Look for **recurring nouns** (e.g., Incident),
- Identify **real world entities** that the system needs to keep track of (e.g., FieldOfficer, Dispatcher, Resource)现实生活中需要跟踪的实体
- Identify **real world procedures** that the system needs to keep track of (e.g., EmergencyOperationsPlan) 现实生活中虽然并非具体, 但需要被软件调控管理, 会是在发生的一件事情.
- Identify **data sources** or **sinks** (e.g., Printer) 数据的输入输出点
- Identify **interface artifacts** (e.g., PoliceStation) [e.g., telecomm link?] 用户界面/端口

当然, 还会有不能识别的对象, 这会通过sequence diagram找出
**牢记! user's term!!**

> Example: flow of events 买玩具
> The _customer_ 类 _enters_ (方法) a _store_(是store提供的enter方法). with the intention of buying a _toy_(类) for his _child_(类) with the age of n.
> Help must be available within less than one minute. 
> The store owner gives advice to the customer. The advice depends on the age range of the child and the attributes of the toy. 
> The customer selects a dangerous toy which is kind of _unsuitable_(child和toy之间存在关系,suitable) for the child.
> The store owner recommends _another type of toy_(存在继承结构). a more _yellow doll_(继承的子类). 
> ![](img/03-23-11-10-09.png)

我们再针对三类对象的类型分别详述

Entity objects 主要关注
- 术语 Terms that developers or users need to clarify in order to understand the use case
- 重复出现的名词 Recurring nouns in the user cases (e.g., Incident)
- 现实实体 Real-world entities that the system needs to track (e.g., FieldOfficer, Dispatcher, Resource)
- 现实活动 Real-world activities that the system need to track (e.g, EmergencyOperationsPlan)
- 数据端口 Data sources or sinks (e.g, Printer)

Boundary object 边界类
- 界面元素 Identify user interface controls that the user needs to initiate the use case (e.g., ReportEmergency _Button_)
- 用户信息 Identify forms the users needs to enter data into the system (e.g., EmergencyReportForm)
- 消息 Identify notices and messages the system uses to respond to the user (e.g., AcknowledgementNotice)
- 当多个用户进行交互时, 需要将终端分开 When multiple actors are involved in a use case, identify actor terminals to refer to the user interface under consideration (e.g., DispatcherStation)

Control Objects 控制类
- 实际是我们发明出来的, 往往没有实体对应
- 设立领导,提高效率, 两种方式
  - Identify one control object per use case
  - Identify one control object per actor in the use case
- The life span of a control object should cover the extent of the use case or the extent of a user session

> Example: 电子手表的三分类
> ![](img/03-23-11-16-32.png)

在UML中, 存在原型机制, 可以手动选择.


#### Mapping Use Cases to Objects with Sequence Diagrams
识别对象的第二方法. Sequence Diagram是识别对象过程的工具, 边画sequence diagram边做决定,做设计.

- An event always has a sender and a receiver. 我们通过sender和receiver识别对象
- The representation of the event is sometimes called a message
- Find sender and receiver for each event => These are the objects participating in the use case

> 比如, _警官_ 通过按 _按钮_ 播报警情, 创建了 _control对象_ (在后续过程中扮演协调者的作用), 创建 _警情表_ , 由警官提交, form会给control发完成信息, control 创建了 emergency report, 发到控制中心, 销毁officer form
> ![](img/03-23-11-26-59.png)
> 接下来由manage主导, 创建incidentform, 由dispatcher看到, 创建incident, 填入, 提交, 创建通知, manage就可以销毁incident form
> ![](img/03-23-11-27-08.png)
> manage将完成调度的信息发回report emergency control, 创建notice, 告知现场警官, dismiss掉, manage也可以销毁report control了.
> ![](img/03-23-11-27-17.png)

总结: 画顺序图的规则和规律
Layout
- 第一列: actor, 系统之外启动交互的实体
- 第二列: 边界对象, 直接和acotr交互
- 第三列: control object

creation:
- control object应该尽早(由initial边界对象)唤起, (后续的)边界对象应该由唤醒的control object全权负责

access:
- 实体可以被control和boundary访问
- 但实体不能命令boundary和control
  - 由此确保有效抗拒外界的变化, 各司其职.


> Example: 游戏平台组织比赛
> 联盟负责人向边界类发起新比赛, 边界类创建新比赛控制类
> 比赛控制类首先向arena检查是否允许新比赛.
> 联盟负责人继续向边界类提交信息, 交到控制类, 控制类带上这些数据,向league创建, 由此创建了新的锦标赛类.
> ![](img/03-23-11-32-50.png)

由于部分概念已经找出来, 画在图上了, 但通过画顺序图, 我们找到了更多的边界类,控制类

![](img/03-23-11-33-28.png) ![](img/03-23-11-33-50.png)

同时, 顺序图还帮助我们发现了更多类的事件响应/消息/方法, 这会落实到类(i.p. public operation of the message receiver). **实现了责任的划分**.

![](img/03-23-11-36-22.png)

两种风格的责任分配
| 集中式 | 分布式 |
|--|--|
| ![](img/03-23-11-38-27.png) | ![](img/03-23-11-38-36.png) |
| 用一个control unit负责下达一切命令, 其余部门都听命于control, 相互之间不交流 | 相互之间存在消息的传递 |

过去, 终端的能力十分局限, centralized好
后来, PC的发展, decentralized好
现在, 云端能力极大提升, centralized好
未来, 又提倡数据存储在终端, 边缘分布式, decentralized好.

### Identify Associations

### Identify Aggregates

### Identify Attributes

## Reviewing the Analysis Model

## Managing Analysis