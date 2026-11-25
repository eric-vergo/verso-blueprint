/*
 * Blueprint sidebar: adds "Blueprint Home", separators, the configured
 * external links and a light/dark switch to Verso's table of contents, shows
 * the document's outline as a tree, and keeps the page header (site title and
 * search) at the top of the sidebar.
 * The outline (parts, chapters and sections, with a part's chapters inside it)
 * comes from -verso-data/blueprint-sidebar-outline.js, which sets
 * window.versoBlueprintSidebarOutline. Each row with entries below it has a
 * disclosure button (aria-expanded, aria-controls); the title is a link. By
 * default parts are open, and so is every entry above the current page; the
 * rows the reader opens or closes are remembered for the site in
 * sessionStorage under "verso-blueprint-sidebar-tree". Right and Left on a
 * row open and close it (Left on a closed row moves to the row above it).
 * Without the outline, the current chapter's sections are nested under that
 * chapter as Verso lists them.
 * Configuration: <script type="application/json" id="verso-blueprint-sidebar-config">.
 * The theme switch sets html[data-theme] and stores "light" or "dark" under
 * localStorage key "verso-theme" (the key Verso's own theme toggle uses).
 * Page controls that would otherwise float over the page (the Blueprint style
 * switcher, a status legend with class "bp_status_legend") move into the
 * sidebar foot.
 * Long dotted names in entries (module names such as A.B.LongName) may wrap
 * after each dot, and an entry whose text is cut off shows it whole as its
 * tooltip.
 */
(function () {
  const themeKey = "verso-theme";
  const treeStateKey = "verso-blueprint-sidebar-tree";

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

  // The outline as a tree --------------------------------------------------

  function readOutline() {
    const outline = window.versoBlueprintSidebarOutline;
    if (!outline || !Array.isArray(outline.entries) || outline.entries.length === 0) return null;
    return outline;
  }

  function readTreeState() {
    try {
      const raw = sessionStorage.getItem(treeStateKey);
      const parsed = raw ? JSON.parse(raw) : null;
      return parsed && typeof parsed === "object" ? parsed : {};
    } catch (_err) {
      return {};
    }
  }

  function writeTreeState(state) {
    try {
      sessionStorage.setItem(treeStateKey, JSON.stringify(state));
    } catch (_err) {}
  }

  // A page's address without its fragment or "index.html", ending in "/".
  function pageKey(url) {
    let path = url.pathname.replace(/index\.html$/, "");
    if (!path.endsWith("/")) path += "/";
    return url.origin + path;
  }

  function resolve(href) {
    try {
      return new URL(href || "./", document.baseURI);
    } catch (_err) {
      return null;
    }
  }

  // The chain of entries from the top of the outline to the one whose page is
  // the current page, or null.
  function currentChain(entries, here) {
    for (const entry of entries) {
      const children = Array.isArray(entry.children) ? entry.children : [];
      const below = currentChain(children, here);
      if (below) return [entry].concat(below);
      if (entry.page !== undefined) {
        const url = resolve(entry.page);
        if (url && pageKey(url) === here) return [entry];
      }
    }
    return null;
  }

  function buildTree(outline, toc) {
    const saved = readTreeState();
    const chain = currentChain(outline.entries, pageKey(window.location)) || [];
    const current = chain.length > 0 ? chain[chain.length - 1] : null;
    let groupCount = 0;
    const root = element("ul", "bp_tree");

    function setOpen(item, open) {
      const button = item.querySelector(":scope > .bp_tree_row > .bp_tree_toggle");
      const group = item.querySelector(":scope > .bp_tree_group");
      if (!button || !group) return;
      button.setAttribute("aria-expanded", open ? "true" : "false");
      group.hidden = !open;
      item.classList.toggle("bp_tree_open", open);
    }

    function remember(item, open) {
      const key = item.getAttribute("data-key");
      if (!key) return;
      const state = readTreeState();
      state[key] = open;
      writeTreeState(state);
    }

    function itemFor(entry, level) {
      const item = element("li", "bp_tree_item");
      item.setAttribute("data-key", entry.href || "");
      item.setAttribute("data-kind", entry.part ? "part" : "entry");
      const row = element("div", "bp_tree_row");
      row.style.setProperty("--bp-tree-level", String(level));
      const children = Array.isArray(entry.children) ? entry.children : [];
      const link = element("a", "bp_tree_link");
      link.href = entry.href || "./";
      if (typeof entry.number === "string" && entry.number !== "") {
        link.appendChild(element("span", "bp_tree_number", entry.number));
      }
      const title = element("span", "bp_tree_title");
      // The title as Verso's table of contents writes it, from this site's own data.
      const template = document.createElement("template");
      template.innerHTML = typeof entry.title === "string" ? entry.title : "";
      title.appendChild(template.content);
      link.appendChild(title);
      if (entry === current) {
        row.classList.add("bp_tree_current");
        link.setAttribute("aria-current", "page");
      }
      if (children.length > 0) {
        const groupId = "bp-tree-group-" + ++groupCount;
        const button = element("button", "bp_tree_toggle");
        button.type = "button";
        button.setAttribute("aria-controls", groupId);
        button.setAttribute("aria-label", (title.textContent || "").trim());
        row.appendChild(button);
        row.appendChild(link);
        item.appendChild(row);
        const group = element("ul", "bp_tree_group");
        group.id = groupId;
        group.style.setProperty("--bp-tree-level", String(level));
        children.forEach(function (child) {
          group.appendChild(itemFor(child, level + 1));
        });
        item.appendChild(group);
        const onPath = chain.indexOf(entry) >= 0;
        const key = entry.href || "";
        let open = !!entry.part;
        if (Object.prototype.hasOwnProperty.call(saved, key)) open = saved[key] === true;
        if (onPath) open = true;
        setOpen(item, open);
        button.addEventListener("click", function (event) {
          event.preventDefault();
          const next = button.getAttribute("aria-expanded") !== "true";
          setOpen(item, next);
          remember(item, next);
        });
      } else {
        row.appendChild(element("span", "bp_tree_toggle_space"));
        row.appendChild(link);
        item.appendChild(row);
      }
      if (entry.part) item.classList.add("bp_tree_part");
      return item;
    }

    // Pages after the last part, or after the last numbered chapter, stand apart.
    let lastGrouped = -1;
    outline.entries.forEach(function (entry, i) {
      if (entry.part || typeof entry.number === "string") lastGrouped = i;
    });
    outline.entries.forEach(function (entry, i) {
      if (i === lastGrouped + 1 && lastGrouped >= 0) {
        const rule = element("li", "bp_tree_rule");
        rule.setAttribute("aria-hidden", "true");
        rule.appendChild(element("hr"));
        root.appendChild(rule);
      }
      root.appendChild(itemFor(entry, 0));
    });

    // Right opens a row (or moves into it), Left closes it (or moves to its parent).
    root.addEventListener("keydown", function (event) {
      if (event.key !== "ArrowRight" && event.key !== "ArrowLeft") return;
      if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
      const target = event.target;
      if (!target.classList || !(target.classList.contains("bp_tree_link") || target.classList.contains("bp_tree_toggle"))) return;
      const item = target.closest(".bp_tree_item");
      if (!item) return;
      const button = item.querySelector(":scope > .bp_tree_row > .bp_tree_toggle");
      const open = button && button.getAttribute("aria-expanded") === "true";
      if (event.key === "ArrowRight") {
        if (!button) return;
        if (!open) {
          setOpen(item, true);
          remember(item, true);
        } else {
          const first = item.querySelector(":scope > .bp_tree_group > .bp_tree_item > .bp_tree_row > .bp_tree_link");
          if (first) first.focus();
        }
      } else if (open) {
        setOpen(item, false);
        remember(item, false);
      } else {
        const parent = item.parentElement && item.parentElement.closest(".bp_tree_item");
        const link = parent && parent.querySelector(":scope > .bp_tree_row > .bp_tree_link");
        if (!link) return;
        link.focus();
      }
      event.preventDefault();
    });
    return root;
  }

  // Scroll the sidebar, not the page, so that the current row is in view.
  function revealCurrent(toc) {
    const row = toc.querySelector(".bp_tree_row.bp_tree_current");
    if (!row) return;
    let box = row.parentElement;
    while (box && box !== document.body) {
      const style = window.getComputedStyle(box);
      if ((style.overflowY === "auto" || style.overflowY === "scroll") && box.scrollHeight > box.clientHeight) break;
      box = box.parentElement;
    }
    if (!box || box === document.body) return;
    const boxRect = box.getBoundingClientRect();
    const rowRect = row.getBoundingClientRect();
    if (rowRect.top >= boxRect.top && rowRect.bottom <= boxRect.bottom) return;
    box.scrollTop += rowRect.top - boxRect.top - box.clientHeight / 3;
  }

  // Replace the rows of Verso's book list (after `home`) by the outline's tree.
  function installTree(toc, body, home, outline) {
    Array.prototype.slice.call(body.rows).forEach(function (row) {
      if (row !== home) row.remove();
    });
    body.appendChild(ruleRow());
    const row = element("tr", "bp_sidebar_tree_row");
    const cell = element("td");
    cell.colSpan = 2;
    cell.appendChild(buildTree(outline, toc));
    row.appendChild(cell);
    body.appendChild(row);
    // Verso's per-level lists of the current page say what the tree shows.
    toc.querySelectorAll(".split-toc:not(.book)").forEach(function (splitToc) {
      splitToc.classList.add("bp_sidebar_nested");
    });
    toc.classList.add("bp_sidebar_nesting", "bp_sidebar_has_tree");
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

  // Let the dotted names of `root`'s entries wrap after their dots.
  function wrapDottedNames(root) {
    root.querySelectorAll("tr > td > a code, tr > td > a, .bp_tree_title code, .bp_tree_title").forEach(function (el) {
      if (el.querySelector("code")) return;
      const walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT);
      const texts = [];
      while (walker.nextNode()) texts.push(walker.currentNode);
      texts.forEach(function (node) {
        const text = node.nodeValue || "";
        if (text.indexOf(".") < 0 || text.length < 20) return;
        const frag = document.createDocumentFragment();
        text.split(".").forEach(function (part, i, parts) {
          frag.appendChild(document.createTextNode(i < parts.length - 1 ? part + "." : part));
          if (i < parts.length - 1) frag.appendChild(document.createElement("wbr"));
        });
        node.parentNode.replaceChild(frag, node);
      });
    });
  }

  // An entry still cut off (a name without dots, a narrow sidebar) gets its text as tooltip.
  function titleCutEntries(root) {
    root.querySelectorAll("tr > td > a, .bp_tree_link").forEach(function (a) {
      const cell = a.classList.contains("bp_tree_link") ? null : a.closest("td");
      const cut = a.scrollWidth > a.clientWidth + 1 || (cell && cell.scrollWidth > cell.clientWidth + 1);
      if (cut && !a.hasAttribute("title")) a.setAttribute("title", (a.textContent || "").trim());
    });
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
      const outline = readOutline();
      if (outline) {
        installTree(toc, body, home, outline);
      } else {
        const firstUnnumbered = body.querySelector("tr.unnumbered");
        if (firstUnnumbered) body.insertBefore(ruleRow(), firstUnnumbered);
      }
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
      if (!outline) nestSections(toc, body);
      wrapDottedNames(body);
      titleCutEntries(body);
    }
    adoptControls(installFoot(toc));
    trackHeader();
    revealCurrent(toc);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", install);
  } else {
    install();
  }
})();
