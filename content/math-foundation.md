# 基础

接下来开始正式进行《mathematics in lean》的讲解，相比原教程进行了大量的篇幅缩减，并直接关注核心要点，并仅列出相应的1-2道例题

在粘贴或书写代码时，最好每添加一行/一步，都去观察LeanInfoView的Tactic state反馈。

---
因为常常需要使用Mathlib库，所以可以在最顶部先写好库的导入
```
import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
```

## S01_Calculating（计算）

#### 知识点1 rw相关写法

rw ：将所有匹配的子式替换为定理或假设的右边<br/>
nth_rw n [h]：将第n个匹配的子式替换为h的右边<br/>
rw [← thm]：将所有匹配的子式替换为thm的左边<br/>
calc ：逐步计算，每一步都需要证明<br/>
ring ：自动进行环论中的计算（基本覆盖了下面的带输定理）

```
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm a (b*c)]
  rw [mul_assoc]
  rw [mul_comm a c]
```
```
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h] --修改第2处匹配的子式a+b为c
  rw [add_mul]
```
```
example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring
```

#### 知识点2 常见代数定理总结

使用check可以观察每个定理的具体特性
```
--交换律结合律
#check add_comm -- add_comm : ∀ a b : G, a + b = b + a
#check add_assoc -- add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
#check mul_comm -- mul_comm : ∀ a b : R, a * b = b * a
#check mul_assoc -- mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
--分配律
#check mul_add -- mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c
#check add_mul -- add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c
--二倍或平方
#check two_mul -- two_mul : ∀ a : R, 2 * a = a + a
#check pow_two -- pow_two : ∀ a : R, a ^ 2 = a * a
--减法
#check add_sub -- add_sub : ∀ a b c : G, a + b - c = a + (b - c)
#check mul_sub -- mul_sub : ∀ a b c : R, a * (b - c) = a * b - a * c
#check sub_add -- sub_add : ∀ a b c : G, a - b + c = a + (c - b)
#check sub_sub -- sub_sub : ∀ a b c : G, a - b - c = a - (b + c)
--零和一
#check add_zero -- add_zero : ∀ a : G, a + 0 = a
#check zero_add -- zero_add : ∀ a : G, 0 + a = a
#check zero_mul -- zero_mul : ∀ a : R, 0 * a = 0
#check mul_zero -- mul_zero : ∀ a : R, a * 0 = 0
#check sub_self -- sub_self : ∀ a : G, a - a = 0
#check mul_one -- mul_one : ∀ a : R, a * 1 = a
#check one_mul -- one_mul : ∀ a : R, 1 * a = a
--等式消去
#check add_neg_cancel -- add_neg_cancel : ∀ a : R, a + -a = 0
#check neg_add_cancel -- neg_add_cancel : ∀ a : R, -a + a = 0
#check neg_add_cancel_left --neg_add_cancel_left : ∀ (a b : G), -a + (a + b) = b
#check add_left_cancel --add_left_cancel : {a b c : R} (h : a + b = a + c) : b = c
```

#### 知识点3 section...end空间

在构造的空间中，可以使用variable去统一命名变量，不用单独写在每个example中
```
section

variable (a b c d : ℝ)

example  (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm b a]
  rw [sub_self]

end
```

#### 知识点4 calc格式书写证明

利用calc格式，可以更好的模拟数学解题的写法去书写证明过程，展示中间过程

```
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    _ = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc (a*a+b*a) (a*b) (b*b), add_assoc (a*a) (b*a) (a*b)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
```


## S02_Proving_Identities_in_Algebraic_Structures（证明代数结构的性质）
#### 知识点1 熟悉简单的代数性质证明
有关消去的场景：
```
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
```
#### 知识点2 have的用法
have可以引入一个新的命题
```
theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]
```

#### 知识点3



## S03_Using_Theorems_and_Lemmas


## S04_More_on_Order_and_Divisibility


## S05_Proving_Facts_about_Algebraic_Structures