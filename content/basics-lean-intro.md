# Lean介绍



## （一）什么是Lean？

一句话概述：Lean是具有归纳类型的构造演算系统的依值类型论版本，能自然表达并证明几乎所有传统数学定理的交互式定理证明器。

逻辑基础：基于依赖类型，结合了经典逻辑和计算逻辑。
特点：由微软研究院支持，设计注重实用性和现代编程体验，拥有规模庞大的 mathlib 库，覆盖从基础数学到前沿理论。支持元编程和自动化，如 Aesop 策略，Lean 4 原生支持 VS Code，提供交互式提示。

应用场景：可用于数学形式化，如素数定理的证明，以及程序验证等领域。


## （二）核心概念

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

## （三）基本语法

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

## （四）证明策略

### 基本策略
以下是几个常用的策略
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

## （五）总结

Lean是一个强大的工具，它将数学证明和编程完美结合。虽然学习曲线较陡，但掌握后能够进行严格的形式化验证，对数学和计算机科学都有重要意义。

接下来的几个章节将会从不同角度，循序渐进地对Lean做系统介绍。

> **提示**：学习Lean需要耐心和坚持，建议从简单的例子开始，逐步深入。
