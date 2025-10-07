# Lean Learn：Lean学习平台

## （一）项目介绍

本项目是一个面向入门者与实务者的 Lean 学习与笔记网站，采用纯静态前端（HTML/CSS/JS）与本地 Markdown 内容分离的方式构建。侧边栏提供四大板块（基础概念、动手实操、定理证明、数学实战），正文区域以单页模式（SPA）按需加载对应 Markdown，页面切换流畅、维护成本低，适合个人与团队协作沉淀知识。

## （二）打开方式

https://shijiesong01.github.io/lean-learn/

（如未启用 GitHub Pages，可用本地方式启动）

```
cd lean-learn
python -m http.server 8000
# 打开浏览器访问 http://localhost:8000
```

## （三）项目结构

- 根目录：入口 `index.html`，统一容器与脚本初始化
- css/：全站样式，含侧边栏简约科研风格与响应式
- js/：核心脚本，注入侧边栏、持久化展开状态、本地 Markdown 渲染、SPA 导航
- pages/：板块与子页面的壳文件，仅保留 `aside` 与 `#markdown-content`
- content/：与 pages 一一对应的 `.md` 正文源，便于版本化协作与离线编辑
- 部署：静态站点，可用 GitHub Pages 或任意静态服务器托管
