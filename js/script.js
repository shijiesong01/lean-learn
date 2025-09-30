// 侧边栏切换功能
document.addEventListener('DOMContentLoaded', function() {
    const toggleBtn = document.getElementById('toggleBtn');
    const sidebar = document.getElementById('sidebar');
    
    // 创建浮动切换按钮
    const floatingToggle = document.createElement('button');
    floatingToggle.innerHTML = '☰';
    floatingToggle.className = 'floating-toggle';
    floatingToggle.style.cssText = `
        position: fixed;
        top: 20px;
        left: 20px;
        width: 50px;
        height: 50px;
        border-radius: 50%;
        background: #2c3e50;
        color: white;
        border: none;
        cursor: pointer;
        font-size: 20px;
        z-index: 1001;
        box-shadow: 0 2px 10px rgba(0,0,0,0.3);
        display: none;
        transition: all 0.3s ease;
    `;
    document.body.appendChild(floatingToggle);
    
    if (toggleBtn && sidebar) {
        // 侧边栏内的按钮
        toggleBtn.addEventListener('click', function() {
            sidebar.classList.toggle('collapsed');
            updateFloatingButton();
        });
        
        // 浮动按钮
        floatingToggle.addEventListener('click', function() {
            sidebar.classList.toggle('collapsed');
            updateFloatingButton();
        });
        
        function updateFloatingButton() {
            if (sidebar.classList.contains('collapsed')) {
                floatingToggle.style.display = 'block';
            } else {
                floatingToggle.style.display = 'none';
            }
        }
        
        // 初始化
        updateFloatingButton();
    }
});

// 子菜单展开/折叠功能
document.addEventListener('DOMContentLoaded', function() {
    const submenuToggles = document.querySelectorAll('.submenu-toggle');
    
    submenuToggles.forEach(toggle => {
        toggle.addEventListener('click', function(e) {
            e.preventDefault();
            const navItem = this.closest('.nav-item');
            navItem.classList.toggle('open');
        });
    });
});

// 移动端侧边栏处理
document.addEventListener('DOMContentLoaded', function() {
    const sidebar = document.getElementById('sidebar');
    const mainContent = document.querySelector('.main-content');
    
    // 点击主内容区域时关闭侧边栏（移动端）
    if (mainContent) {
        mainContent.addEventListener('click', function() {
            if (window.innerWidth <= 768) {
                sidebar.classList.remove('open');
            }
        });
    }
    
    // 窗口大小改变时的处理
    window.addEventListener('resize', function() {
        if (window.innerWidth > 768) {
            // 桌面端：移除移动端的open类，但保留collapsed状态
            sidebar.classList.remove('open');
        } else {
            // 移动端：默认隐藏侧边栏
            sidebar.classList.add('open');
        }
    });
    
    // 初始化：根据屏幕大小设置侧边栏状态
    if (window.innerWidth <= 768) {
        sidebar.classList.add('open');
    }
    
});

// 平滑滚动
document.querySelectorAll('a[href^="#"]').forEach(anchor => {
    anchor.addEventListener('click', function (e) {
        e.preventDefault();
        const target = document.querySelector(this.getAttribute('href'));
        if (target) {
            target.scrollIntoView({
                behavior: 'smooth',
                block: 'start'
            });
        }
    });
});

// 页面加载动画
window.addEventListener('load', function() {
    document.body.style.opacity = '0';
    document.body.style.transition = 'opacity 0.5s ease-in-out';
    
    setTimeout(() => {
        document.body.style.opacity = '1';
    }, 100);
});

// 返回顶部按钮
function createBackToTop() {
    const backToTop = document.createElement('button');
    backToTop.innerHTML = '↑';
    backToTop.className = 'back-to-top';
    backToTop.style.cssText = `
        position: fixed;
        bottom: 20px;
        right: 20px;
        width: 50px;
        height: 50px;
        border-radius: 50%;
        background: #3498db;
        color: white;
        border: none;
        cursor: pointer;
        font-size: 20px;
        opacity: 0;
        visibility: hidden;
        transition: all 0.3s ease;
        z-index: 1000;
        box-shadow: 0 2px 10px rgba(0,0,0,0.2);
    `;
    
    document.body.appendChild(backToTop);
    
    window.addEventListener('scroll', function() {
        if (window.scrollY > 300) {
            backToTop.style.opacity = '1';
            backToTop.style.visibility = 'visible';
        } else {
            backToTop.style.opacity = '0';
            backToTop.style.visibility = 'hidden';
        }
    });
    
    backToTop.addEventListener('click', function() {
        window.scrollTo({
            top: 0,
            behavior: 'smooth'
        });
    });
}

// 初始化返回顶部按钮
createBackToTop();
