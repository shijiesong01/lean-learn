# Lean基础

## 什么是Lean？

Lean是一个交互式定理证明器和函数式编程语言，由Microsoft Research开发。它结合了数学证明和编程，让形式化验证变得更加直观。

## 核心概念

### 类型理论
Lean基于**依赖类型理论**，这意味着类型可以依赖于值：

```lean
-- 自然数类型
def nat : Type := ℕ

-- 依赖类型：列表的长度
def vector (α : Type) (n : ℕ) : Type := {l : list α // l.length = n}
```

### 命题即类型
在Lean中，**命题就是类型**，证明就是构造该类型的值：

```lean
-- 命题：对于所有自然数n，n + 0 = n
theorem add_zero (n : ℕ) : n + 0 = n :=
begin
  induction n,
  { refl },
  { simp [nat.add_succ, ih] }
end
```

## 基本语法

### 定义函数
```lean
-- 简单函数定义
def double (x : ℕ) : ℕ := x + x

-- 递归函数
def factorial : ℕ → ℕ
| 0 := 1
| (n + 1) := (n + 1) * factorial n
```

### 定义定理
```lean
-- 定理：加法交换律
theorem add_comm (a b : ℕ) : a + b = b + a :=
begin
  induction a,
  { simp },
  { simp [nat.add_succ, ih] }
end
```

## 证明策略

### 基本策略
- `refl` - 自反性
- `simp` - 简化
- `rw` - 重写
- `exact` - 精确匹配

### 示例证明
```lean
theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) :=
begin
  induction a,
  { refl },
  { simp [nat.add_succ, ih] }
end
```

## 学习资源

### 官方文档
- [Lean 4手册](https://leanprover.github.io/lean4/doc/)
- [数学库文档](https://leanprover-community.github.io/)

### 推荐书籍
1. **《Theorem Proving in Lean 4》** - 官方教程
2. **《Mathematics in Lean》** - 数学形式化
3. **《Functional Programming in Lean》** - 函数式编程

## 实践建议

### 学习路径
1. **基础语法** - 熟悉Lean 4的基本语法
2. **类型理论** - 理解依赖类型
3. **证明策略** - 掌握各种证明方法
4. **数学形式化** - 将数学概念形式化
5. **项目实践** - 完成实际的形式化项目

### 练习项目
- 实现基本的数据结构
- 证明经典的数学定理
- 形式化算法正确性
- 参与开源项目

## 总结

Lean是一个强大的工具，它将数学证明和编程完美结合。虽然学习曲线较陡，但掌握后能够进行严格的形式化验证，对数学和计算机科学都有重要意义。

> **提示**：学习Lean需要耐心和坚持，建议从简单的例子开始，逐步深入。
