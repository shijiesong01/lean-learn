// 子菜单展开/折叠功能（保持侧边栏固定，精简为最小必要交互）
document.addEventListener('DOMContentLoaded', function() {
    const SIDEBAR_STATE_KEY = 'sidebar.open.keys';

    function getSidebarHtmlPath() {
        // 统一从 base 出发的相对路径
        return 'pages/sidebar.html';
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

    async function renderMarkdownByName(mdName) {
        const mount = document.getElementById('markdown-content');
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
