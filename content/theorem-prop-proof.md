# 命题与证明

## （一）命题即类型

我们可引入一种新类型 Prop，来表示命题，然后引入用其他命题构造新命题的构造子。
```
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
```
对每个元素 p : Prop，可以引入另一个类型 Proof p，作为 p 的证明的类型。<br/>
「公理」是这个类型中的常值。

## （二）以「命题即类型」的方式工作

在「命题即类型」范式中，只涉及 → 的定理可以通过 lambda 抽象和应用来证明。<br/>
在 Lean 中，theorem 命令引入了一个新的定理：
```
variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
--通过 show 语句明确指定最后一个项 hp 的类型
theorem t2 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
```

## （三）命题逻辑
操作符的优先级如下：¬ > ∧ > ∨ > → > ↔。<br/>
在上一章中，我们观察到 lambda 抽象可以被看作是→ 的「引入规则」，展示了如何「引入」或建立一个蕴含。<br/>
应用可以看作是一个「消去规则」，展示了如何在证明中「消去」或使用一个蕴含。<br/>

（1）合取

引入：表达式And.intro h1 h2 是 p ∧ q 的证明，<br/>
它使用了 h1 : p 和 h2 : q 的证明。通常把 And.intro 称为合取引入规则。<br/>
下面的例子我们使用 And.intro 来创建 p → q → p ∧ q 的证明。
```
variable (p q : Prop)
example (hp : p) (hq : q) : p ∧ q := 
  And.intro hp hq

--step1 定义命题，将hp:p，hq:q添加到上下文
--step2 p ∧ q 被解析为And p q类型，现在要尝试构成这个类型的项
--step3 进入And.intro，找到构造子intro，::后为其构造的类型，命名left和right
--step4 进行类型推断，p为And中的a,q为and中的b，And.intro : p → q → And p q类型

#check p ∧ q
```
消去：表达式And.left h 从 h : p ∧ q 建立了一个 p 的证明。<br/>
类似地，And.right h 是 q 的证明。它们常被称为左或右合取消去规则。
```
variable (p q : Prop)
example (h : p ∧ q) : p := h.left --或写出And.left
example (h : p ∧ q) : q := And.right h
--step1 And p q类型的构造子为left:p，right:q
```
例子：我们现在可以证明 p ∧ q → q ∧ p：
```
variable (p q : Prop)
example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
```
（2）析取

引入：表达式 Or.intro_left q hp 从证明 hp : p 建立了 p ∨ q 的证明。<br/>
类似地，Or.intro_right p hq 从证明 hq : q 建立了 p ∨ q 的证明。<br/>
这是左右析取（「或」）引入规则。
```
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```
看看 Or.intro_left 的类型，两个构造子分别是左注入和右注入<br/>
structure：用于定义单一构造子的类型，所有字段必须同时提供<br/>
inductive：用于定义多个构造子的类型，表示不同的可能性

消去：如果我们想要从 p ∨ q 证明 r，只需要展示 p 可以证明 r，<br/>
且 q 也可以证明 r。换句话说，它是一种逐情况证明。<br/>
在表达式 Or.elim hpq hpr hqr 中，Or.elim 接受三个论证，<br/>
hpq : p ∨ q，hpr : p → r 和 hqr : q → r，生成 r 的证明。
```
variable (p q r : Prop)
example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
```
（三）否定和假言

否定 ¬p 真正的定义是 p → False，所以我们通过从 p 导出一个矛盾来获得 ¬p。<br/>
类似地，表达式 hnp hp 从 hp : p 和 hnp : ¬p 产生一个 False 的证明。
```
variable (p q : Prop)
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```
连接词False 只有一个消去规则 False.elim，<br/>
它表达了一个事实，即矛盾能导出一切。
```
variable (p q : Prop)
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

（4）逻辑等价

表达式 Iff.intro h1 h2 从 h1 : p → q 和 h2 : q → p 生成了 p ↔ q 的证明。<br/>
表达式 Iff.mp h 从 h : p ↔ q 生成了 p → q 的证明。<br/>
表达式 Iff.mpr h 从 h : p ↔ q 生成了 q → p 的证明。<br/>
下面是 p ∧ q ↔ q ∧ p 的证明：
```
variable (p q : Prop)
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))
#check and_swap p q    -- p ∧ q ↔ q ∧ p
variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```


## （四）引入辅助子目标

这里介绍 Lean 提供的另一种帮助构造长证明的方法，
即 have 结构，它在证明中引入了一个辅助的子目标。
```
variable (p q : Prop)
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

## （五）经典逻辑
不会证明+不想lean报错： 使用sorry，可以避开形式化的检查。

