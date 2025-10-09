# 引言

在阅读本章的过程中，建议将代码复制到自己的lean环境下，会有更好的学习效果

---

## （一）type与term

Lean是基于类型论的定理证明器，其核心就是默认一切对象/项（term）比如a，都具有对饮的类型（type）比如A，写法为a:A<br/>
我们用check语法查看每个项的类型，eval进行计算，以下是各类例子

```
-- 变量声明
#check 1
#check (1 : Float) --强制规定1为浮点数类型

-- 函数声明
#check fun x : Nat ↦ x 
#check fun (x y : Nat) ↦ x + y

--Nat本身也具有类型
#check Nat

--Type也有类型，这样的设计解决了集合论中集合包含自身的问题
#check Type
#check Type 32 --lean中最多支持32层

--定义函数并计算
def plus(x y : Nat) :=
  x + y
#eval plus 1 2
```

## （二）实现1+1=2：定义代数结构、函数和命题

### 2.1 如何定义代数结构

inductive可用于构造新的代数结构，where后跟相应的构造子,下面我们参考皮亚诺公理，重新定义自然数

```
inductive Nat' where
  | zero : Nat'
  | succ : Nat' → Nat'
#check Nat'.zero --0
#eval Nat'.zero --就是这个值，其他没定义
#eval Nat.zero  --这里系统约定了是0的表示
```

### 2.2 如何定义函数

在定义自然数后，我们利用归纳定义新的自然数的加法运算
```
def Nat'.add (n k : Nat') : Nat' :=
  match k with
  | Nat'.zero => n
  | Nat'.succ k' => Nat'.succ (Nat'.add n k')

#check Nat'.add Nat'.zero Nat'.zero
#eval Nat'.add (Nat'.succ Nat'.zero) (Nat'.succ Nat'.zero) --1+1=2
```

### 2.3 如何证明命题
在lean中我们可以利用example语句书写和证明命题，一般情况下“ : ”后是对应命题，“ : ”前是该命题证明的命名，“ := ”后是对应命题的证明过程。或者可直接通俗地理解为<br/>
“ 证明名称 : 命题 := 证明过程”

```
example: Nat'.add (Nat'.succ Nat'.zero) (Nat'.succ Nat'.zero) = Nat'.succ (Nat'.succ Nat'.zero) := by
  rfl
```
上述rfl是一种常见的证明策略，接下来我们回通过实际例子再介绍几个证明策略。

## （三）整除性质的证明

### 2.1 陈述命题
在 Lean 中，当使用def定义标识符时，若“ : ”后面指定的类型为Prop，则表明该标识符被定义为一个命题（即一个逻辑陈述）。
```
def dvd_mul_right2 (m n k: Nat): Prop := m∣n → m∣n*k
```

### 2.2 在证明前寻找引理
证明整除的性质前，并不需要从头开始构造各种代数结构和运算，Lean以及其Mathlib库提供了诸多构造好的结构和定理，只需要从中找到能辅助证明的定理作为引理，即可简化证明时的步骤
```
#check Nat.dvd_trans --Nat.dvd_trans {a b c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c
#check Nat.dvd_mul_right --Nat.dvd_mul_right (a b : ℕ) : a ∣ a * b
```
### 2.3 用三种写法去做证明吧
1.直接构造证明项（λ 抽象式）
```
example : ∀ (m n k : Nat), m ∣ n → m ∣ n * k :=
  fun m n k h ↦ Nat.dvd_trans h (Nat.dvd_mul_right n k)
```
2.分离式陈述（参数化前提）<br/>
这种在声明时就加入条件h的一般不用
```
example (m n k : Nat) (h : m ∣ n) : m ∣ n * k :=
  Nat.dvd_trans h (Nat.dvd_mul_right n k)
```
3.用by开启战术模式（交互式分步证明）
<br/>以下这种写法更常见，分离问题和证明结构清晰
```
example : ∀ (m n k : Nat), m ∣ n → m ∣ n * k := by
  intro m n k h
  apply Nat.dvd_trans h
  apply Nat.dvd_mul_right n k
```

## （四）证明乘法分配率
在熟悉了常见证明过程后，我们通过乘法分配律的例子区分两种含策略的证明结构
### 4.1 策略式证明
```
example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]
  rw [← Nat.add_assoc, Nat.mul_comm b a, Nat.add_assoc (a*a) (a*b) (a*b), ← Nat.two_mul, ← Nat.mul_assoc]
  repeat rw [← Nat.pow_two]
```

### 4.2 计算式证明（也含策略的使用）
```
example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  calc
    _ = a * a + a * b + (b * a + b * b) := by rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    _ =  a * a + 2 * a * b + b * b := by
      rw [← Nat.add_assoc, Nat.mul_comm b a, Nat.add_assoc (a*a) (a*b) (a*b), ← Nat.two_mul, ← Nat.mul_assoc]
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [Nat.pow_two, Nat.pow_two]
```
