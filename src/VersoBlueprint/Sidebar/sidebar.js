/*
 * Blueprint sidebar: adds "Blueprint Home", separators, the configured
 * external links and a light/dark switch to Verso's table of contents.
 * Configuration: <script type="application/json" id="verso-blueprint-sidebar-config">.
 * The theme switch sets html[data-theme] and stores "light" or "dark" under
 * localStorage key "verso-theme" (the key Verso's own theme toggle uses).
 */
(function () {
  const themeKey = "verso-theme";

  function readConfig() {
    const node = document.getElementById("verso-blueprint-sidebar-config");
    if (!node) return null;
    try {
      return JSON.parse(node.textContent || "{}");
    } catch (_err) {
      return null;
    }
  }

  function element(tag, className, text) {
    const el = document.createElement(tag);
    if (className) el.className = className;
    if (text !== undefined) el.textContent = text;
    return el;
  }

  function ruleRow() {
    const row = element("tr", "bp_sidebar_rule");
    const cell = element("td");
    cell.colSpan = 2;
    cell.appendChild(element("hr"));
    row.appendChild(cell);
    return row;
  }

  function effectiveTheme() {
    const explicit = document.documentElement.getAttribute("data-theme");
    if (explicit === "dark" || explicit === "light") return explicit;
    return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches
      ? "dark"
      : "light";
  }

  function hasThemeControl(toc) {
    return toc.querySelector("[data-verso-theme-toggle], .verso-theme-toggle, .theme-toggle") !== null;
  }

  function installThemeSwitch(toc) {
    const last = toc.querySelector(":scope > .last") || toc;
    if (hasThemeControl(toc)) return;
    const foot = element("div", "bp_sidebar_foot");
    const sun = element("span", "bp_theme_icon", "☀");
    sun.setAttribute("aria-hidden", "true");
    const moon = element("span", "bp_theme_icon", "☾");
    moon.setAttribute("aria-hidden", "true");
    const button = element("button", "bp_theme_switch");
    button.type = "button";
    button.setAttribute("role", "switch");
    button.setAttribute("aria-label", "Dark theme");
    function sync() {
      button.setAttribute("aria-checked", effectiveTheme() === "dark" ? "true" : "false");
    }
    button.addEventListener("click", function () {
      const next = effectiveTheme() === "dark" ? "light" : "dark";
      document.documentElement.setAttribute("data-theme", next);
      try {
        localStorage.setItem(themeKey, next);
      } catch (_err) {}
      sync();
    });
    if (window.matchMedia) {
      const query = window.matchMedia("(prefers-color-scheme: dark)");
      if (query.addEventListener) query.addEventListener("change", sync);
    }
    sync();
    foot.appendChild(sun);
    foot.appendChild(button);
    foot.appendChild(moon);
    last.appendChild(foot);
  }

  function install() {
    const config = readConfig();
    const toc = document.getElementById("toc");
    if (!config || !toc || toc.querySelector(".bp_sidebar_foot, .bp_sidebar_home")) return;
    const book = toc.querySelector(".split-toc.book table");
    if (book) {
      const body = book.tBodies[0] || book;
      const homeLink = toc.querySelector("a.toc-title");
      const home = element("tr", "bp_sidebar_home");
      const cell = element("td");
      cell.colSpan = 2;
      const link = element("a", "", config.homeLabel || "Blueprint Home");
      link.href = homeLink ? homeLink.getAttribute("href") || "./" : "./";
      cell.appendChild(link);
      home.appendChild(cell);
      body.insertBefore(home, body.firstChild);
      const firstUnnumbered = body.querySelector("tr.unnumbered");
      if (firstUnnumbered) body.insertBefore(ruleRow(), firstUnnumbered);
      const links = Array.isArray(config.links) ? config.links : [];
      if (links.length > 0) {
        body.appendChild(ruleRow());
        links.forEach(function (entry) {
          if (!entry || !entry.href) return;
          const row = element("tr", "unnumbered bp_sidebar_link");
          row.appendChild(element("td", "num"));
          const td = element("td");
          const a = element("a", "", entry.label || entry.href);
          a.href = entry.href;
          td.appendChild(a);
          row.appendChild(td);
          body.appendChild(row);
        });
      }
    }
    installThemeSwitch(toc);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", install);
  } else {
    install();
  }
})();
