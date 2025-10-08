# 安装配置

## （一）Linux下安装
### 1.1 安装elan
1. 安装vscode, git
2. 下载插件“Lean 4”
3. 搜索中输入以下内容进入安装指导界面
```
> Lean 4.Docs.ShowSetupGuide
```
4. 下载elan<br/>
>Elan是Lean的版本管理器，可以自动管理所有不同版本的Lean，并确保在打开项目时使用正确的版本。<br/>
elan install leanprover/lean4:v4.6.0-rc1  即可下载相应版本的lean

**plan a.** 可点击Lean4 Setup中 Install Lean-click to install 进行elan和git的下载<br/>
**plan b.** 或者直接运行下面代码安装
```
curl "https://elan.lean-lang.org/elan-init.sh" -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
```
5. 重启终端后，elan会被加入环境变量中，可运行代码查看版本
```
elan --version
```

---

### 1.2 配置lean项目（含Mathlib）

#### （1）创建新的lean项目<br/>
**plan a.** 可点击lean - new project - Create Project Using Mathlib会直接自动配置项目（安装lean的时间较长）<br/>
**plan b.** 或者运行下面代码逐步创建
1. 创建指定lean版本的新项目
```
lake new project2 leanprover/lean4:v4.23.0
cd project2
```
2. 修改lakefile.toml添加mathlib依赖<br/>
注意rev项的版本应该和对应的lean版本相同<br/>
```
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.23.0"
```
3. 下载当前项目所需**依赖**的**预编译缓存**文件
```
lake update
lake exe cache get
``` 
3. 正式编译该项目所有代码
```
lake build
```
4. 重启终端，否则可能一直显示错误，运行代码测试
```
-- 尝试导入 mathlib 的基础模块
import Mathlib.Data.Nat.Basic

-- 仅使用 mathlib 中定义的自然数类型
def main : IO Unit := do
  -- 如果能正常打印，说明 mathlib 已正确导入
  IO.println "mathlib 导入成功！"
  -- 验证自然数类型可正常使用（来自 mathlib）
  IO.println s!"自然数示例: {1 + 2}"
```


#### （2）配置mathematics_in_lean
1. 将GitHub项目clone到指定路径
```
mkdir lean-project
cd lean-project
git clone https://github.com/leanprover-community/mathematics_in_lean.git
```
>打开后可见下面几个主要文件<br/>
lakefile.toml: 描述项目依赖于mathlib以及所要编译的目标
lake-manifest.json：记录了所有依赖的版本和地址
lean-toolchain: 指定使用lean的版本

2. 下载当前项目所需**依赖**的**预编译缓存**文件
```
cd mathematics_in_lean
lake exe cache get
``` 
3. 正式编译该项目所有代码
```
lake build
```
4. 打开电子书，输入
```
> Lean 4: Open Document View
```

## （二）Windows下安装

不推荐，暂无正式教程

