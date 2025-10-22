# 交互方式

在配置好lean后，有众多交互方式，下面介绍常见的几种：

## （一）基于VS Code infoview的直观展示

非常直观，不再具体介绍

## （二）基于REPL的Json格式交互

https://github.com/leanprover-community/repl
https://www.leanprover.cn/tool/repl/#_1

### 1 安装配置

### 2 命令模式
注：<br/>
1. 必须是json格式，不然会结束运行；有语法错误则不会结束；
2. 按ctrl+D发送终止符EOF，才会获得结果；
3. env用于区分不同的状态，作用是复用上下文，输入带有env可指定对应状态，不带env的语句则默认开启下一个新的状态；<br/>
输入命令：
```
{"cmd": "example (a b c : ℝ) : a * (b * d) = b * (a * d) := by sorry", "env": 2}
```
这里的 env": 2 表示：当前命令将在编号为 2 的环境中执行。这个环境 2 是之前某个命令执行后返回的结果，包含了该命令之前所有的定义、导入（例如 Mathlib.Data.Real.Basic 等）等信息。
```
......
   "data": "declaration uses 'sorry'"}],
 "env": 3}
```
输出结果中的 env": 3 表示：当前命令执行完成后，生成了一个新的环境，编号为 3。这个新环境 3 继承了环境 2 中的所有内容，同时包含了当前 example 声明的信息（即新增了这个待证明的命题）。<br/>
若要 "回溯" 到之前的状态（例如放弃最近的操作），直接使用更早的 env 编号即可。

示例：
```
{"cmd": "def f := 2"}  // 无 env，创建新环境执行
{"cmd": "example : f = 2 := rfl", "env": 1}  // 基于 env=1 的环境执行
```

### 3 策略模式
注：<br/>
1. 必须是json格式，不然会结束运行；有语法错误则不会结束；
2. 按ctrl+D发送终止符EOF，才会获得结果；
3. 当输入问题含有sorry且带有env时进入策略模式，进入后的证明过程都在该env下进行；
4. 策略模式下，存档用proofState记录，因此每次输入和输出都带有proofState;

示例：
```
(base) $ lake exe repl
{"cmd": "import Mathlib.Data.Real.Basic"}
{"env": 0}

{"cmd": "example (a b c : ℝ) : a * (b * c) = b * (a * c) := by sorry", "env": 0}
{"sorries":
 [{"proofState": 0,
   "pos": {"line": 1, "column": 54},
   "goal": "a b c : ℝ\n⊢ a * (b * c) = b * (a * c)",
   "endPos": {"line": 1, "column": 59}}],
 "messages":
 [{"severity": "warning",
   "pos": {"line": 1, "column": 0},
   "endPos": {"line": 1, "column": 7},
   "data": "declaration uses 'sorry'"}],
 "env": 1}

{"tactic":"rw [← mul_assoc a b c]", "proofState":0}
{"proofState": 1, "goals": ["a b c : ℝ\n⊢ a * b * c = b * (a * c)"]}

 {"tactic":"rw [mul_comm a b]", "proofState":0}
{"message":
 "Lean error:\ntactic 'rewrite' failed, did not find instance of the pattern in the target expression\n  a * b\na b c : ℝ\n⊢ a * (b * c) = b * (a * c)"}

 {"tactic":"rw [mul_comm a b]", "proofState":1}    
{"proofState": 2, "goals": ["a b c : ℝ\n⊢ b * a * c = b * (a * c)"]}

 {"tactic":"rw [mul_assoc b a c]", "proofState":2}
{"proofState": 3, "goals": []}
```

## （三）基于LeanDojo的交互

LeanDojo 是一个基于 Python 的交互式 Lean 环境，提供了丰富的 API 和工具。

### 1 安装配置

```bash
pip install leandojo
```

### 2 基本使用

```python
from leandojo import LeanDojo

# 创建 Lean 环境
lean = LeanDojo()

# 执行 Lean 代码
result = lean.run("def hello := \"world\"")
print(result)
```

### 3 交互式证明

```python
# 开始一个证明
lean.start_proof("theorem add_zero (n : ℕ) : n + 0 = n := by sorry")

# 应用策略
lean.apply_tactic("rfl")

# 检查证明状态
print(lean.get_proof_state())
```

## （四）命令行交互

### 1 Lean 命令行工具

使用命令行进行基本交互：

```bash
# 检查文件语法
lean --check MyFile.lean

# 编译文件
lean --compile MyFile.lean

# 运行可执行文件
./MyFile
```

### 2 Lake 构建系统

Lake 提供项目级别的交互：

```bash
# 构建项目
lake build

# 运行测试
lake test

# 清理构建文件
lake clean

# 更新依赖
lake update
```

## （五）调试技巧

### 1 使用 sorry

在开发过程中，可以使用 `sorry` 来临时跳过证明：

```lean
theorem example_theorem : P → Q := by
  intro h
  -- 暂时跳过这个证明
  sorry
```

### 2 使用 #check 和 #eval

检查表达式类型和值：

```lean
#check 1 + 1  -- 显示类型：ℕ
#eval 1 + 1   -- 显示值：2
```

### 3 使用 #print 查看定义

查看函数或定理的定义：

```lean
#print add  -- 显示 add 函数的定义
```

## （六）最佳实践

### 1 渐进式开发

- 先写类型签名，再写实现
- 使用 `sorry` 标记未完成的部分
- 逐步完善证明

### 2 利用类型信息

- 经常查看目标面板
- 利用类型信息指导证明方向
- 注意错误信息的提示

### 3 保持代码整洁

- 使用有意义的变量名
- 添加适当的注释
- 组织代码结构清晰
