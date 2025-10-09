# 简介

《Theorem Proving in Lean 4》侧重于教你在 Lean 中编写和验证证明，掌握其底层理论知识，并且不太需要针对 Lean 的基础知识。<br/>

你将学习 Lean 所基于的逻辑系统，它是依值类型论（Dependent type theory）的一个版本，足以证明几乎所有传统的数学定理，并且有足够的表达能力自然地表示数学定理。<br/>

更具体地说，Lean 是基于具有归纳类型（Inductive type）的构造演算（Calculus of Construction）系统的类型论版本。<br/>

Lean 不仅可以定义数学对象和表达依值类型论的数学断言，而且还可以作为一种语言来编写证明。

```
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p := --合取交换律
  -- 使用 lambda 表达式引入一个假设 hpq，它表示 "p 且 q" 这个命题成立
  fun hpq : p ∧ q =>
  -- 从 "p 且 q" 中提取出 p 成立的证据，命名为 hp
  have hp : p := And.left hpq
  -- 从 "p 且 q" 中提取出 q 成立的证据，命名为 hq
  have hq : q := And.right hpq
  -- 证明目标 "q 且 p"，通过 And.intro 构造这个合取命题，
  show q ∧ p from And.intro hq hp
#check and_commutative
```
