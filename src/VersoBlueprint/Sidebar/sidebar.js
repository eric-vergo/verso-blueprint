/*
 * Blueprint sidebar: adds "Blueprint Home", separators, the configured
 * external links and a light/dark switch to Verso's table of contents, shows
 * the document's outline as a tree, and keeps the page header (site title and
 * search) at the top of the sidebar.
 * The outline (parts, chapters and sections, with a part's chapters inside it)
 * comes from -verso-data/blueprint-sidebar-outline.js, loaded asynchronously,
 * which sets window.versoBlueprintSidebarOutline; while it loads, the class
 * "bp-sidebar-pending" (set by an inline head script) keeps Verso's list out of
 * sight. Each row with entries below it has a disclosure button
 * (aria-expanded, aria-controls) out of the Tab order; the title is a link and
 * the row's one Tab stop. By default parts are open, and so is every entry
 * above the current page; the rows the reader opens or closes, and the
 * sidebar's scroll position, are kept for the site in sessionStorage under
 * "verso-blueprint-sidebar-tree" and "verso-blueprint-sidebar-scroll". On a
 * row, Right and Left open and close it (or move into it and to the row above
 * it), Up and Down move between the rows that can be seen, Home and End to the
 * ends. Without the outline, the current chapter's sections are nested under
 * that chapter as Verso lists them.
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

  const outlineFile = "blueprint-sidebar-outline.js";
  const scrollKey = "verso-blueprint-sidebar-scroll";
  const pendingClass = "bp-sidebar-pending";

  function readOutline() {
    const outline = window.versoBlueprintSidebarOutline;
    if (!outline || !Array.isArray(outline.entries) || outline.entries.length === 0) return null;
    return outline;
  }

  // Call `done` once, with the outline or null, when the outline file has run or failed. The
  // file loads asynchronously: it may have run before this script looks, or run later.
  function whenOutline(done) {
    let settled = false;
    function settle() {
      if (settled) return;
      settled = true;
      done(readOutline());
    }
    if (readOutline()) return settle();
    const script = document.querySelector('script[src$="' + outlineFile + '"]');
    if (script) {
      script.addEventListener("load", settle);
      script.addEventListener("error", settle);
    }
    // an asynchronous script has run or failed by the time the page has loaded
    if (!script || document.readyState === "complete") settle();
    else window.addEventListener("load", settle);
  }

  function readStored(key) {
    try {
      const raw = sessionStorage.getItem(key);
      const parsed = raw ? JSON.parse(raw) : null;
      return parsed && typeof parsed === "object" && !Array.isArray(parsed) ? parsed : {};
    } catch (_err) {
      return {};
    }
  }

  function writeStored(key, value) {
    try {
      sessionStorage.setItem(key, JSON.stringify(value));
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

  // The chain of entries from the top of the outline to the one `matches` accepts, or null.
  function chainTo(entries, matches) {
    for (const entry of entries) {
      const children = Array.isArray(entry.children) ? entry.children : [];
      const below = chainTo(children, matches);
      if (below) return [entry].concat(below);
      if (matches(entry)) return [entry];
    }
    return null;
  }

  // The entries above and at the current place: the entry whose page this is, else (on a page
  // that holds several entries, as a single-page site does) the entry the address's fragment
  // names, else none.
  function currentChain(entries) {
    const here = pageKey(window.location);
    const byPage = chainTo(entries, function (entry) {
      if (typeof entry.page !== "string") return false;
      const url = resolve(entry.page);
      return url !== null && pageKey(url) === here;
    });
    if (byPage) return byPage;
    if (!window.location.hash) return [];
    return chainTo(entries, function (entry) {
      const url = resolve(entry.href);
      return url !== null && url.hash === window.location.hash && pageKey(url) === here;
    }) || [];
  }

  // The rows the reader can see, in order: their links.
  function visibleLinks(root) {
    return Array.prototype.filter.call(root.querySelectorAll(".bp_tree_link"), function (a) {
      return !a.closest("ul[hidden]");
    });
  }

  function buildTree(outline) {
    const saved = readStored(treeStateKey);
    const chain = currentChain(outline.entries);
    const current = chain.length > 0 ? chain[chain.length - 1] : null;
    let groupCount = 0;
    const root = element("ul", "bp_tree");

    function setOpen(item, open) {
      const button = item.querySelector(":scope > .bp_tree_row > .bp_tree_toggle");
      const group = item.querySelector(":scope > .bp_tree_group");
      if (!button || !group) return;
      button.setAttribute("aria-expanded", open ? "true" : "false");
      group.hidden = !open;
    }

    function remember(item, open) {
      const state = readStored(treeStateKey);
      state[item.getAttribute("data-key") || ""] = open;
      writeStored(treeStateKey, state);
    }

    // The numbers of sibling rows take the width of the widest, so that their titles line up.
    function numberWidth(list, entries) {
      const widest = entries.reduce(function (n, entry) {
        return typeof entry.number === "string" ? Math.max(n, entry.number.length) : n;
      }, 0);
      if (widest > 0) list.style.setProperty("--bp-tree-number-width", widest + "ch");
    }

    function itemFor(entry, level) {
      const item = element("li", "bp_tree_item" + (entry.part ? " bp_tree_part" : ""));
      item.setAttribute("data-key", entry.href || "");
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
      if (children.length === 0) {
        row.appendChild(element("span", "bp_tree_toggle_space"));
        row.appendChild(link);
        item.appendChild(row);
        return item;
      }
      const groupId = "bp-tree-group-" + ++groupCount;
      const button = element("button", "bp_tree_toggle");
      button.type = "button";
      // one stop per row for Tab: the row's link; the arrow keys open and close the row
      button.tabIndex = -1;
      button.setAttribute("aria-controls", groupId);
      button.setAttribute("aria-label", (title.textContent || "").trim());
      row.appendChild(button);
      row.appendChild(link);
      item.appendChild(row);
      const group = element("ul", "bp_tree_group");
      group.id = groupId;
      group.style.setProperty("--bp-tree-level", String(level));
      numberWidth(group, children);
      children.forEach(function (child) {
        group.appendChild(itemFor(child, level + 1));
      });
      item.appendChild(group);
      const key = entry.href || "";
      let open = !!entry.part;
      if (Object.prototype.hasOwnProperty.call(saved, key)) open = saved[key] === true;
      if (chain.indexOf(entry) >= 0) open = true;
      setOpen(item, open);
      button.addEventListener("click", function (event) {
        event.preventDefault();
        const next = button.getAttribute("aria-expanded") !== "true";
        setOpen(item, next);
        remember(item, next);
      });
      return item;
    }

    // Pages after the last part, or after the last numbered chapter, stand apart.
    let lastGrouped = -1;
    outline.entries.forEach(function (entry, i) {
      if (entry.part || typeof entry.number === "string") lastGrouped = i;
    });
    numberWidth(root, outline.entries);
    outline.entries.forEach(function (entry, i) {
      if (i === lastGrouped + 1 && lastGrouped >= 0) {
        const rule = element("li", "bp_tree_rule");
        rule.setAttribute("aria-hidden", "true");
        rule.appendChild(element("hr"));
        root.appendChild(rule);
      }
      root.appendChild(itemFor(entry, 0));
    });

    // Keys on a row's link: Right opens the row (or moves into it), Left closes it (or moves to
    // the row above it), Enter or Space on the triangle toggles it, Up and Down move between the
    // rows that can be seen, Home and End to the first and last.
    root.addEventListener("keydown", function (event) {
      if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
      const target = event.target;
      if (!target.classList) return;
      if (!target.classList.contains("bp_tree_link") && !target.classList.contains("bp_tree_toggle")) return;
      const item = target.closest(".bp_tree_item");
      if (!item) return;
      const link = item.querySelector(":scope > .bp_tree_row > .bp_tree_link");
      const button = item.querySelector(":scope > .bp_tree_row > .bp_tree_toggle");
      const open = button !== null && button.getAttribute("aria-expanded") === "true";
      if (event.key === "ArrowDown" || event.key === "ArrowUp" || event.key === "Home" || event.key === "End") {
        const links = visibleLinks(root);
        const at = links.indexOf(link);
        const next =
          event.key === "Home" ? links[0] :
          event.key === "End" ? links[links.length - 1] :
          links[at + (event.key === "ArrowDown" ? 1 : -1)];
        if (next) next.focus();
      } else if (event.key === "ArrowRight") {
        if (!button) return;
        if (!open) {
          setOpen(item, true);
          remember(item, true);
        } else {
          const first = item.querySelector(":scope > .bp_tree_group > .bp_tree_item > .bp_tree_row > .bp_tree_link");
          if (first) first.focus();
        }
      } else if (event.key === "ArrowLeft") {
        if (open) {
          setOpen(item, false);
          remember(item, false);
        } else {
          const parent = item.parentElement && item.parentElement.closest(".bp_tree_item");
          const up = parent && parent.querySelector(":scope > .bp_tree_row > .bp_tree_link");
          if (!up) return;
          up.focus();
        }
      } else {
        return;
      }
      event.preventDefault();
    });
    return root;
  }

  // The element that scrolls the sidebar's list, or null.
  function scrollBox(toc) {
    let box = toc.querySelector(".bp_tree") || toc;
    while (box && box !== document.body && box !== document.documentElement) {
      const style = window.getComputedStyle(box);
      if ((style.overflowY === "auto" || style.overflowY === "scroll") && box.scrollHeight > box.clientHeight) {
        return box;
      }
      box = box.parentElement;
    }
    return null;
  }

  // Keep the sidebar where the reader left it when they move to another page of the site.
  function keepScroll(toc) {
    window.addEventListener("pagehide", function () {
      const box = scrollBox(toc);
      if (box) writeStored(scrollKey, { top: box.scrollTop });
    });
  }

  function restoreScroll(toc) {
    const top = readStored(scrollKey).top;
    const box = scrollBox(toc);
    if (box && typeof top === "number") box.scrollTop = top;
  }

  // Scroll the sidebar, not the page, so that the current row is in view, if it is not already.
  function revealCurrent(toc) {
    const row = toc.querySelector(".bp_tree_row.bp_tree_current, tr.bp_sidebar_home.bp_sidebar_current");
    const box = scrollBox(toc);
    if (!row || !box) return;
    const boxRect = box.getBoundingClientRect();
    const rowRect = row.getBoundingClientRect();
    if (rowRect.top >= boxRect.top && rowRect.bottom <= boxRect.bottom) return;
    box.scrollTop += rowRect.top - boxRect.top - box.clientHeight / 3;
  }

  // Replace the rows of Verso's book list by the outline's tree, after `home`.
  function installTree(toc, body, home, outline) {
    Array.prototype.slice.call(body.rows).forEach(function (row) {
      if (!/\bbp_sidebar_/.test(row.className)) row.remove();
    });
    const row = element("tr", "bp_sidebar_tree_row");
    const cell = element("td");
    cell.colSpan = 2;
    cell.appendChild(buildTree(outline));
    row.appendChild(cell);
    body.insertBefore(row, home.nextSibling);
    body.insertBefore(ruleRow(), row);
    // Verso's per-level lists of the current page say what the tree shows.
    toc.querySelectorAll(".split-toc:not(.book)").forEach(function (splitToc) {
      splitToc.classList.add("bp_sidebar_nested");
    });
    toc.classList.add("bp_sidebar_nesting");
    wrapDottedNames(row);
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
    const names = "tr > td > a code, tr > td > a, .bp_tree_title code, .bp_tree_title";
    root.querySelectorAll(names).forEach(function (el) {
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
    root.querySelectorAll("tr > td > a").forEach(function (a) {
      const cell = a.closest("td");
      const cut = a.scrollWidth > a.clientWidth + 1 || (cell && cell.scrollWidth > cell.clientWidth + 1);
      if (cut && !a.hasAttribute("title")) a.setAttribute("title", (a.textContent || "").trim());
    });
  }

  function install() {
    const config = readConfig();
    const toc = document.getElementById("toc");
    const root = document.documentElement;
    if (!config || !toc || toc.querySelector(".bp_sidebar_foot, .bp_sidebar_home")) {
      root.classList.remove(pendingClass);
      return;
    }
    const book = toc.querySelector(".split-toc.book table");
    adoptControls(installFoot(toc));
    trackHeader();
    keepScroll(toc);
    if (!book) {
      root.classList.remove(pendingClass);
      return;
    }
    const body = book.tBodies[0] || book;
    const homeLink = toc.querySelector("a.toc-title");
    const home = element("tr", "bp_sidebar_home");
    const cell = element("td");
    cell.colSpan = 2;
    const link = element("a", "", config.homeLabel || "Blueprint Home");
    link.href = homeLink ? homeLink.getAttribute("href") || "./" : "./";
    if (pageKey(link) === pageKey(window.location)) {
      home.classList.add("bp_sidebar_current");
      link.setAttribute("aria-current", "page");
    }
    cell.appendChild(link);
    home.appendChild(cell);
    body.insertBefore(home, body.firstChild);
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
    wrapDottedNames(body);
    titleCutEntries(body);
    // Verso's list stays hidden (`pendingClass`) until the outline has replaced it, or the
    // outline is known to be missing.
    whenOutline(function (outline) {
      if (outline) {
        installTree(toc, body, home, outline);
      } else {
        const firstUnnumbered = body.querySelector("tr.unnumbered:not(.bp_sidebar_link)");
        if (firstUnnumbered) body.insertBefore(ruleRow(), firstUnnumbered);
        nestSections(toc, body);
        body.querySelectorAll("tr.bp_sidebar_sections").forEach(wrapDottedNames);
        titleCutEntries(body);
      }
      root.classList.remove(pendingClass);
      restoreScroll(toc);
      revealCurrent(toc);
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", install);
  } else {
    install();
  }
})();
