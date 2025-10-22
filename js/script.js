// 子菜单展开/折叠功能（保持侧边栏固定，精简为最小必要交互）
document.addEventListener('DOMContentLoaded', function() {
    const SIDEBAR_STATE_KEY = 'sidebar.open.keys';

    function getSidebarHtmlPath() {
        // 统一从 base 出发的相对路径
        return 'pages/sidebar.html';
    }

    function ensureMarkdownMount() {
        const mount = document.getElementById('markdown-content');
        if (mount && !mount.classList.contains('markdown-content')) {
            mount.classList.add('markdown-content');
        }
        return mount;
    }

    function persistOpenState(navItem, isOpen) {
        const key = navItem.getAttribute('data-key');
        if (!key) return;
        let openKeys = [];
        try { openKeys = JSON.parse(localStorage.getItem(SIDEBAR_STATE_KEY) || '[]'); } catch (e) { openKeys = []; }
        const set = new Set(openKeys);
        if (isOpen) { set.add(key); } else { set.delete(key); }
        localStorage.setItem(SIDEBAR_STATE_KEY, JSON.stringify(Array.from(set)));
    }

    function restoreOpenStates(root) {
        let openKeys = [];
        try { openKeys = JSON.parse(localStorage.getItem(SIDEBAR_STATE_KEY) || '[]'); } catch (e) { openKeys = []; }
        const set = new Set(openKeys);
        root.querySelectorAll('.nav-item.has-submenu').forEach(item => {
            const key = item.getAttribute('data-key');
            if (key && set.has(key)) { item.classList.add('open'); }
        });
    }

    async function injectSidebar() {
        const path = getSidebarHtmlPath();
        try {
            const resp = await fetch(path, { cache: 'no-cache' });
            if (!resp.ok) throw new Error('加载sidebar失败');
            const html = await resp.text();
            const container = document.getElementById('sidebar');
            if (container) {
                const temp = document.createElement('div');
                temp.innerHTML = html;
                const aside = temp.querySelector('aside.sidebar');
                container.innerHTML = aside ? aside.innerHTML : html;
                bindSidebarInteractions(container);
                enableSpaNavigation(container);
                restoreOpenStates(container);
            }
        } catch (e) {
            bindSidebarInteractions(document);
            enableSpaNavigation(document);
            restoreOpenStates(document);
        }
    }

    function bindSidebarInteractions(root) {
        root.querySelectorAll('.nav-item.has-submenu').forEach(item => {
            const toggle = item.querySelector('.submenu-toggle');
            if (toggle) {
                toggle.addEventListener('click', function(e) {
                    e.preventDefault();
                    e.stopPropagation();
                    const willOpen = !item.classList.contains('open');
                    item.classList.toggle('open');
                    persistOpenState(item, willOpen);
                });
            }
            const mainLink = item.querySelector(':scope > .nav-link');
            if (mainLink) {
                mainLink.addEventListener('click', function() {
                    const willOpen = !item.classList.contains('open');
                    item.classList.toggle('open');
                    persistOpenState(item, willOpen);
                });
            }
        });
    }

    function getMdFromUrl() {
        const url = new URL(window.location.href);
        return url.searchParams.get('md');
    }

    function loadHighlightAssetsOnce() {
        if (document.getElementById('hljs-script')) return Promise.resolve();
        return new Promise(resolve => {
            const link = document.createElement('link');
            link.rel = 'stylesheet';
            link.href = 'https://cdn.jsdelivr.net/npm/highlight.js@11.9.0/styles/github.min.css';
            document.head.appendChild(link);
            const s = document.createElement('script');
            s.id = 'hljs-script';
            s.src = 'https://cdn.jsdelivr.net/npm/highlight.js@11.9.0/lib/highlight.min.js';
            s.onload = resolve;
            document.body.appendChild(s);
        });
    }

    function addCopyButtons(mount) {
        if (!mount) return;
        mount.querySelectorAll('pre').forEach(pre => {
            if (pre.querySelector('.code-copy-btn')) return; // 避免重复添加
            const btn = document.createElement('button');
            btn.className = 'code-copy-btn';
            btn.type = 'button';
            btn.title = '复制代码';
            btn.innerText = '复制';
            btn.addEventListener('click', async () => {
                const code = pre.querySelector('code');
                const text = code ? code.innerText : pre.innerText;
                try {
                    await navigator.clipboard.writeText(text);
                    btn.innerText = '已复制';
                    setTimeout(() => (btn.innerText = '复制'), 1200);
                } catch (err) {
                    // 兼容性兜底
                    const textarea = document.createElement('textarea');
                    textarea.value = text;
                    textarea.style.position = 'fixed';
                    textarea.style.left = '-9999px';
                    document.body.appendChild(textarea);
                    textarea.select();
                    try { document.execCommand('copy'); } catch (_) {}
                    document.body.removeChild(textarea);
                    btn.innerText = '已复制';
                    setTimeout(() => (btn.innerText = '复制'), 1200);
                }
            });
            pre.style.position = pre.style.position || 'relative';
            pre.appendChild(btn);
        });
    }

    function linkifyQuotedChapters(mount) {
        if (!mount) return;
        // 仅针对“基础概念”页面中提到的引号内章节名进行链接
        const labelToMd = {
            '引言': 'basics-intro',
            'Lean介绍': 'basics-lean-intro',
            '资料整理': 'basics-resources',
            '在线使用': 'hands-online',
            '安装配置': 'hands-setup',
            '开发工程': 'hands-project',
            '交互方式': 'hands-interact'
        };
        const selector = '.markdown-content p, .markdown-content li';
        mount.querySelectorAll(selector).forEach(el => {
            let html = el.innerHTML;
            Object.keys(labelToMd).forEach(label => {
                const md = labelToMd[label];
                const pattern = new RegExp('“' + label.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '”', 'g');
                html = html.replace(pattern, `<a href="index.html?md=${md}" data-md="${md}">“${label}”</a>`);
            });
            el.innerHTML = html;
        });
    }

    async function renderMarkdownByName(mdName) {
        const mount = ensureMarkdownMount();
        if (!mount || !mdName) return;
        const mdPath = 'content/' + mdName.replace(/\.md$/, '') + '.md';
        if (typeof marked === 'undefined') {
            await new Promise((resolve, reject) => {
                const s = document.createElement('script');
                s.src = 'https://cdn.jsdelivr.net/npm/marked@4.3.0/marked.min.js';
                s.onload = resolve;
                s.onerror = reject;
                document.head.appendChild(s);
            }).catch(() => {});
        }
        try {
            const resp = await fetch(mdPath, { cache: 'no-cache' });
            if (!resp.ok) throw new Error('加载Markdown失败');
            const mdText = await resp.text();
            const html = (typeof marked !== 'undefined') ? marked.parse(mdText) : mdText;
            mount.innerHTML = html;
            await loadHighlightAssetsOnce();
            if (window.hljs) {
                mount.querySelectorAll('pre code').forEach(block => {
                    window.hljs.highlightElement(block);
                });
            }
            linkifyQuotedChapters(mount);
            addCopyButtons(mount);
        } catch (e) {
            mount.innerHTML = '<p style="color:#c00">Markdown 加载失败。</p>';
        }
    }

    function enableSpaNavigation(root) {
        root.querySelectorAll('a[data-md]').forEach(a => {
            a.addEventListener('click', function(e) {
                const mdName = a.getAttribute('data-md');
                if (!mdName) return;
                e.preventDefault();
                const href = 'index.html?md=' + encodeURIComponent(mdName);
                window.history.pushState({ md: mdName }, '', href);
                renderMarkdownByName(mdName);
                document.body.setAttribute('data-md', mdName);
            });
        });
        // 正文内的 data-md 链接（包括通过 linkify 注入的）
        document.addEventListener('click', function(e) {
            const a = e.target.closest('a[data-md]');
            if (!a) return;
            const mdName = a.getAttribute('data-md');
            if (!mdName) return;
            e.preventDefault();
            const href = 'index.html?md=' + encodeURIComponent(mdName);
            window.history.pushState({ md: mdName }, '', href);
            renderMarkdownByName(mdName);
            document.body.setAttribute('data-md', mdName);
        });
    }

    async function initialRender() {
        const mdParam = getMdFromUrl();
        const mdAttr = document.body.getAttribute('data-md') || 'home';
        await renderMarkdownByName(mdParam || mdAttr);
    }

    window.addEventListener('popstate', function(e) {
        const state = e.state || {};
        const mdName = state.md || getMdFromUrl() || document.body.getAttribute('data-md') || 'home';
        if (mdName) renderMarkdownByName(mdName);
    });

    injectSidebar().then(initialRender);
});
