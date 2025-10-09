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

