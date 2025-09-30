# 学习笔记

一个基于原生HTML/CSS的纯静态学习网站，专注于分享学习心得和知识。

## 🎯 项目特点

- **纯静态** - 使用原生HTML、CSS、JavaScript，无需框架
- **易维护** - 简单的文件结构，易于更新内容
- **响应式** - 支持各种设备访问
- **快速部署** - 直接上传到GitHub即可访问

## 📁 项目结构

```
AI-learn/
├── index.html              # 首页
├── css/
│   └── style.css           # 样式文件
├── js/
│   └── script.js           # 脚本文件
├── pages/                  # 内容页面
│   ├── ml-basics.html      # 机器学习基础
│   ├── about.html          # 关于页面
│   └── ...                 # 其他内容页面
└── README.md               # 说明文档
```

## 🚀 部署到GitHub Pages

### 1. 上传到GitHub
1. 将所有文件推送到GitHub仓库
2. 在仓库设置中启用GitHub Pages
3. 选择主分支作为源
4. 网站将自动部署到 `https://yourusername.github.io/AI-learn/`

### 2. 本地预览
直接在浏览器中打开 `index.html` 即可预览网站效果。

## 📝 内容管理

### 添加新页面
1. 在 `pages/` 目录下创建新的HTML文件
2. 复制现有页面的结构
3. 修改内容部分
4. 在侧边栏导航中添加链接

### 页面模板
```html
<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>页面标题 - 学习笔记</title>
    <link rel="stylesheet" href="../css/style.css">
</head>
<body>
    <div class="container">
        <!-- 侧边栏 -->
        <aside class="sidebar" id="sidebar">
            <!-- 导航内容 -->
        </aside>

        <!-- 主内容区域 -->
        <main class="main-content">
            <div class="content-header">
                <h1>页面标题</h1>
                <p>页面描述</p>
            </div>
            
            <div class="content-body">
                <!-- 页面内容 -->
            </div>
        </main>
    </div>

    <script src="../js/script.js"></script>
</body>
</html>
```

## 🎨 自定义样式

### 修改主题颜色
编辑 `css/style.css` 文件中的颜色变量：
```css
/* 侧边栏背景色 */
.sidebar {
    background: #2c3e50; /* 修改这里 */
}

/* 主色调 */
.nav-link:hover,
.nav-link.active {
    border-left-color: #3498db; /* 修改这里 */
}
```

## 📱 响应式设计

网站已经包含响应式设计，支持：
- 桌面端（>768px）- 侧边栏固定显示
- 平板端（≤768px）- 侧边栏可折叠
- 移动端（≤480px）- 优化的移动体验

## 🔧 功能特性

- **侧边栏导航** - 可折叠的侧边栏，支持子菜单
- **响应式布局** - 适配各种屏幕尺寸
- **平滑滚动** - 页面内锚点平滑滚动
- **返回顶部** - 自动显示返回顶部按钮
- **移动端优化** - 触摸友好的移动端体验

## 📚 学习板块

网站包含以下五个主要学习板块：

1. **首页** - 网站介绍和学习指南
2. **机器学习** - 基础概念、算法原理、实践应用
3. **深度学习** - 深度学习入门、CNN、RNN、Transformer
4. **Lean** - Lean基础、定理证明、实践应用
5. **大模型** - 大模型基础、训练技术、应用场景

## 📖 使用说明

1. 点击左侧导航栏中的主题开始学习
2. 每个主题下都有详细的子章节
3. 内容按难度递增排列
4. 建议按顺序学习以获得最佳效果

