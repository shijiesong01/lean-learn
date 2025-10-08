# 开发工程

## （一）项目结构理解

### 1.1 各文件介绍

当我们通过【安装配置】章节成功配置好含Mathlib的Lean项目后，会得到以下文件：

lean-toolchain: 记录了此项目的lean版本号
```
leanprover/lean4:v4.23.0
```
lakefile.toml: 记录了项目名称、版本号、build目标；库模块名称；可执行文件名称和入口；项目依赖外部库的名称、地址和版本号
```
name = "new-math2"
version = "0.1.0"
defaultTargets = ["new-math2"]

[[lean_lib]]
name = "NewMath2"

[[lean_exe]]
name = "new-math2"
root = "Main"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.23.0"
```
lake-manifest.json: Lake 生成的依赖清单文件，记录项目依赖的精确版本

NewMath2/Basic.lean: 属于项目库的子模块文件，通常包含基础定义、定理或工具函数。

NewMath2.lean: 库的主模块文件，一般用于汇总导出子模块内容，方便外部通过import NewMath2引用整个库。

Main.lean: 项目可执行程序的入口模块，包含main函数，是程序运行的起始点。


### 1.2 编译可执行文件

配置好项目后，可运行lake build进行编译
```
cd NewMath2
lake build
```
编译后会生成.lake/build/bin目录，记录了可执行文件，现在直接终端运行它
```
.\.lake\build\bin\new-math2.exe
```
---
好了，以上就是全部编译过程了；如果想再练一次，可以新建NewMath2/Smile.lean，加入以下代码定义新的变量expression
```
def expression : String := "a big smile"
```
NewMath2.lean文件中也需要更新，以实现导入对应名称:
```
import NewMath2.Basic
import NewMath2.Smile
```
最后在主程序引入，重新编译运行：
```
import Greeting
import Greeting.Basic
import Greeting.Smile
def main : IO Unit :=
  do
    IO.println s!"Hello, {hello}!"
    IO.println s!"Hello, {hello}, with {expression}!" 
```
好了，再次在终端编译和运行吧，看看输出结果
```
lake build
.\.lake\build\bin\new-math2.exe
```


## （二）常用命令

### ① elan相关操作
Elan是Lean的版本管理器，可以自动管理所有不同版本的Lean，并确保在打开项目时使用正确的版本。

显示当前所安装的lean版本和默认版本
```
elan show
```
修改lean的默认版本
```
elan default leanprover/lean4:v4.23.0
```

### ② lake相关操作

创建一个新的文件夹
```
lake new project
```


### ③ lean相关操作
