/*
 * Blueprint sidebar: adds "Blueprint Home", separators, the configured
 * external links and a light/dark switch to Verso's table of contents, nests
 * the current chapter's sections under that chapter, and keeps the page header
 * (site title and search) at the top of the sidebar.
 * Configuration: <script type="application/json" id="verso-blueprint-sidebar-config">.
 * The theme switch sets html[data-theme] and stores "light" or "dark" under
 * localStorage key "verso-theme" (the key Verso's own theme toggle uses).
 * Page controls that would otherwise float over the page (the Blueprint style
 * switcher, a status legend with class "bp_status_legend") move into the
 * sidebar foot.
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

  function themeSwitch() {
    const wrap = element("div", "bp_sidebar_theme");
    const sun = element("span", "bp_theme_icon", "☀");
    sun.setAttribute("aria-hidden", "true");
    const moon = element("span", "bp_theme_icon", "☾");
    moon.setAttribute("aria-hidden", "true");
    const button = element("button", "bp_theme_switch");
    button.type = "button";
    button.setAttribute("role", "switch");
    button.setAttribute("aria-label", "Dark theme");
    button.title = "Dark theme";
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
    wrap.appendChild(sun);
    wrap.appendChild(button);
    wrap.appendChild(moon);
    return wrap;
  }

  function installFoot(toc) {
    const last = toc.querySelector(":scope > .last") || toc;
    const foot = element("div", "bp_sidebar_foot");
    foot.appendChild(element("div", "bp_sidebar_foot_extra"));
    const controls = element("div", "bp_sidebar_controls");
    if (!hasThemeControl(toc)) controls.appendChild(themeSwitch());
    foot.appendChild(controls);
    last.appendChild(foot);
    return foot;
  }

  // Move page controls that would float over the content into the foot. They
  // may be created after this script runs, so keep watching until the page has
  // loaded.
  function adoptControls(foot) {
    function adopt() {
      const switcher = document.getElementById("bp-style-switcher");
      const controls = foot.querySelector(".bp_sidebar_controls");
      if (switcher && switcher.parentElement !== controls) {
        controls.insertBefore(switcher, controls.firstChild);
      }
      const legend = document.querySelector("main .bp_status_legend");
      if (legend) foot.querySelector(".bp_sidebar_foot_extra").appendChild(legend);
    }
    adopt();
    if (!window.MutationObserver || !document.body) return;
    const observer = new MutationObserver(adopt);
    observer.observe(document.body, { childList: true, subtree: true });
    window.addEventListener("load", function () {
      adopt();
      observer.disconnect();
    });
  }

  function sameTarget(a, b) {
    return a.origin === b.origin && a.pathname === b.pathname && a.hash === b.hash;
  }

  // Verso shows one table of contents per level below the book's (the current
  // chapter's sections, then the current section's subsections, ...). Nest each
  // one under its entry in the book list, and keep only the book list.
  function nestSections(toc, bookBody) {
    const tocs = toc.querySelectorAll(".split-toc:not(.book)");
    tocs.forEach(function (splitToc) {
      const titleLink = splitToc.querySelector(":scope > .title a[href]");
      if (!titleLink) return;
      const entry = Array.prototype.find.call(bookBody.querySelectorAll("tr > td > a[href]"), function (a) {
        return sameTarget(a, titleLink);
      });
      if (!entry) return;
      const row = entry.closest("tr");
      const table = splitToc.querySelector(":scope > table");
      if (table && table.rows.length > 0) {
        const nested = element("tr", "bp_sidebar_sections");
        const cell = element("td");
        cell.colSpan = 2;
        table.classList.add("bp_sidebar_subtoc");
        cell.appendChild(table);
        nested.appendChild(cell);
        row.parentNode.insertBefore(nested, row.nextSibling);
      }
      splitToc.classList.add("bp_sidebar_nested");
    });
    toc.classList.add("bp_sidebar_nesting");
  }

  // Keep the sidebar below the page header, whose height follows the title.
  function trackHeader() {
    const header = document.querySelector("body > header");
    if (!header) return;
    const root = document.documentElement;
    function update() {
      const height = header.getBoundingClientRect().height;
      if (height > 0) root.style.setProperty("--bp-sidebar-head-height", height + "px");
    }
    update();
    if (window.ResizeObserver) new ResizeObserver(update).observe(header);
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
      nestSections(toc, body);
    }
    adoptControls(installFoot(toc));
    trackHeader();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", install);
  } else {
    install();
  }
})();
