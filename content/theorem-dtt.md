# 依值类型论（DTT）

## （一）简单类型论

「类型论」得名于其中每个表达式都有一个类型。

下面的一些例子展示了如何声明对象以及检查其类型。
```
def m : Nat := 1       -- m 是自然数
def n : Nat := 0
def b1 : Bool := true  -- b1 是布尔型
/- 检查类型（check） -/
#check m            -- 输出: Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
/- 求值（Evaluate） -/
#eval 5 * 4         -- 20
#eval m + 2         -- 3
```

简单类型论的强大之处在于，你可以从其他类型中构建新的类型。
例如，如果a 和 b 是类型，a -> b 表示从 a 到 b 的函数类型，
a × b 表示由 a 元素与 b 元素配对构成的类型，也称为笛卡尔积。

```
#check Nat → Nat      -- 用"\to" or "\r"来打出这个箭头
#check Nat × Nat      -- 用"\times"打出乘号
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  结果和上一个一样
#check Nat.succ     -- Nat → Nat
#check Nat.succ 2   -- Nat
#check (0, 1)       -- Nat × Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat
#check Nat.add      -- Nat → Nat → Nat
#check Nat.add 3    -- Nat → Nat
```

## （二）类型作为对象

Lean 所依据的依值类型论对简单类型论的其中一项升级是，
类型本身（如 Nat 和 Bool 这些东西）也是对象，因此也具有类型。

```
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat → (Nat → Nat) -- Type
```
上面的每个表达式都是类型为 Type 的对象。你也可以为类型声明新的常量:
```
def α : Type := Nat
def G : Type → Type → Type := Prod
#check α        -- Type
#check G α      -- Type → Type
```
Type 自己的类型是什么？答案是Lean 的底层基础有无限的类型层次：
```
#check Type      -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```
这里有另一个例子：给出任意类型 α，那么类型 List α 是类型为 α 的元素的列表的类型。
```
#check List α    -- Type
#check List Nat  -- Type
```
有些操作需要在类型宇宙上具有多态（Polymorphic）。例如，List α 应该对任何类型的 α 都有意义，

无论 α 存在于哪种类型的宇宙中。所以函数 List 有如下的类型：
```
#check List    -- List.{u} (α : Type u) : Type u
```
你可以使用 universe 命令来声明宇宙变量，这样就可以定义多态常量：
```
def F.{u} (α : Type u) : Type u := Prod α α
#check F    -- Type u → Type u
```

## （三）函数抽象和求值

Lean 提供 fun (或 λ)关键字用于从给定表达式创建函数，如下所示：
```
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ 和 fun 是同义词
#eval (λ x : Nat => x + 5) 10    -- 15
```

## （四）定义与局部定义

def 关键字提供了一个声明新对象的重要方式。

```
def double (x : Nat) : Nat :=
  x + x
#eval double 3    -- 6

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)
#eval doTwice double 2   -- 8
```
Lean 还允许你使用 let 关键字来引入「局部定义」。

表达式 let a := t1; t2 定义等价于把 t2 中所有的 a 替换成 t1 的结果。
```
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16
def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y
#eval twice_double 2   -- 16
```

## （五）小节与命名空间

Lean 提供 variable 指令来统一声明变量：

有时需要限制变量的作用范围。Lean 提供了小节标记 section 来实现这个目的

```
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)
  def compose := g (f x)
  def doThrice := h (h (h x))
end useful
```
Lean 可以让你把定义放进一个「命名空间」（namespace）里，并且命名空间也是层次化的：

命名空间也可以嵌套的，关闭的命名空间可以之后重新打开，甚至是在另一个文件里
```
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7
  def fa : Nat := f a

  #check f
  #check fa
  #check Foo.fa
end Foo --关
-- #check   -- error
#check Foo.f
#check Foo.fa
open Foo --开
#check f
#check fa
#check Foo.fa
```

## （六）依值类型论「依赖」着什么?


给定 α : Type 和 β : α → Type，把 β 考虑成 α 之上的类型类，也就是说，对于每个 a : α 都有类型 β a。<br/>
在这种情况下，类型 (a : α) → β a 表示的是具有如下性质的函数 f 的类型：<br/>
对于每个 a : α，f a 是 β a 的一个元素。<br/>
换句话说，f 返回值的类型取决于其输入。<br/>
这就是依值函数类型，或者依值箭头类型的一个例子。

```
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

## （七）隐参数

当一个函数接受一个通常可以从上下文推断出来的参数时，Lean 允许你指定该参数在默认情况下应该保持隐式。
这是通过将参数放入花括号来实现的，如下所示:

```
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil
```
