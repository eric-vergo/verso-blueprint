  // Graph command runtime helpers.

  export function debounce(fn, waitMs) {
    let timeout = null;
    return function () {
      const args = arguments;
      clearTimeout(timeout);
      timeout = setTimeout(function () {
        fn.apply(null, args);
      }, waitMs);
    };
  }

  function readViewportHeight() {
    return window.innerHeight || document.documentElement.clientHeight || 900;
  }

  function parsePixelSize(value) {
    const size = parseFloat(value);
    return isFinite(size) ? size : NaN;
  }

  function normalizeGraphDirection(rawDirection) {
    const direction = String(rawDirection || "").trim().toUpperCase();
    if (direction === "LR" || direction === "RL" || direction === "BT") {
      return direction;
    }
    return "TB";
  }

  function normalizeGraphPack(rawPack) {
    if (rawPack === false) return false;
    if (rawPack === true) return true;
    const pack = rawPack === null || typeof rawPack === "undefined" ? "" : String(rawPack).trim().toLowerCase();
    if (pack === "") return false;
    if (pack === "false" || pack === "0" || pack === "no" || pack === "off") {
      return false;
    }
    return true;
  }

  function normalizeGraphLayout(rawLayout) {
    const layout = String(rawLayout || "").trim().toLowerCase();
    if (layout === "fill" || layout === "embed" || layout === "slide") return "fill";
    if (layout === "block" || layout === "single") return "block";
    return "page";
  }

  export function normalizeGraphOptions(rawOptions) {
    const options = rawOptions && typeof rawOptions === "object" ? rawOptions : {};
    return {
      direction: normalizeGraphDirection(options.direction),
      pack: normalizeGraphPack(Object.prototype.hasOwnProperty.call(options, "pack") ? options.pack : false)
    };
  }

  export function graphPackAttr(pack) {
    return normalizeGraphPack(pack) ? "true" : "false";
  }

  export function graphOptionsKey(options) {
    const normalized = normalizeGraphOptions(options);
    return normalized.direction + "|" + graphPackAttr(normalized.pack);
  }

  export function graphLayoutMode(graphRoot, options) {
    const opts = options && typeof options === "object" ? options : {};
    if (Object.prototype.hasOwnProperty.call(opts, "layout")) {
      return normalizeGraphLayout(opts.layout);
    }
    if (graphRoot instanceof Element) {
      const attrLayout = graphRoot.getAttribute("data-bp-graph-layout");
      if (attrLayout) return normalizeGraphLayout(attrLayout);
      const block = graphRoot.closest(".bp_graph_fullwidth");
      if (block instanceof Element) {
        const blockLayout = block.getAttribute("data-bp-graph-layout");
        if (blockLayout) return normalizeGraphLayout(blockLayout);
      }
    }
    try {
      const path = window.location && typeof window.location.pathname === "string"
        ? window.location.pathname
        : "";
      if (path.indexOf("/html-single/") >= 0 || /\/html-single\/?$/.test(path)) {
        return "block";
      }
    } catch (_err) {}
    return "page";
  }

  export function readPreviewBehaviorDefaults(panel, fallbackMode, fallbackPlacement) {
    if (!(panel instanceof Element)) {
      return {
        mode: fallbackMode,
        placement: fallbackPlacement
      };
    }
    return {
      mode: panel.getAttribute("data-bp-preview-mode") || fallbackMode,
      placement: panel.getAttribute("data-bp-preview-placement") || fallbackPlacement
    };
  }

  function readGraphCanvasFlowBottom(graphRoot, layoutMode) {
    if (!(graphRoot instanceof Element)) return 0;
    const block = graphRoot.closest(".bp_graph_fullwidth");
    if (layoutMode === "block" || layoutMode === "fill") {
      if (block instanceof Element) return block.getBoundingClientRect().bottom;
      return graphRoot.getBoundingClientRect().bottom;
    }
    const flowContainer = graphRoot.closest(".content-wrapper") || graphRoot.closest("main");
    if (!(flowContainer instanceof Element)) return 0;
    const rect = flowContainer.getBoundingClientRect();
    return rect.bottom;
  }

  function updateGraphCanvasOffset(graphRoot) {
    if (!(graphRoot instanceof Element)) return;
    const block = graphRoot.closest(".bp_graph_fullwidth");
    if (!(block instanceof HTMLElement)) return;
    block.style.setProperty(
      "--bp-graph-canvas-top",
      Math.max(0, Math.round(graphRoot.offsetTop)) + "px"
    );
  }

  function layoutGraphCanvasFill(graphRoot, graphState) {
    const rect = graphRoot.getBoundingClientRect();
    const parent = graphRoot.parentElement;
    const parentRect = parent instanceof Element ? parent.getBoundingClientRect() : null;
    const viewportHeight = readViewportHeight();
    const fallbackHeight = Math.max(280, Math.floor(viewportHeight * 0.7));
    let nextHeight = fallbackHeight;
    if (parentRect && parentRect.height > 0) {
      nextHeight = Math.floor(parentRect.bottom - rect.top);
    } else if (graphRoot.clientHeight > 0) {
      nextHeight = graphRoot.clientHeight;
    }
    nextHeight = Math.max(1, nextHeight);
    graphRoot.style.minHeight = "0px";
    graphRoot.style.maxHeight = "none";
    graphRoot.style.height = nextHeight + "px";
    graphRoot.style.resize = "none";
    if (graphState && typeof graphState === "object") {
      graphState.canvasAutoHeight = nextHeight;
    }
  }

  export function layoutGraphCanvas(graphRoot, graphState, options) {
    if (!(graphRoot instanceof Element)) return;
    updateGraphCanvasOffset(graphRoot);
    const layoutMode = graphLayoutMode(graphRoot, options);
    if (layoutMode === "fill") {
      layoutGraphCanvasFill(graphRoot, graphState);
      return;
    }
    const rect = graphRoot.getBoundingClientRect();
    const viewportHeight = readViewportHeight();
    const bottomGap = 20;
    const viewportMaxHeight = Math.max(280, Math.floor(viewportHeight * 0.84));
    const flowBottom = readGraphCanvasFlowBottom(graphRoot, layoutMode);
    const trailingHeight = Math.max(0, flowBottom - rect.bottom);
    const rawAvailableHeight = Math.floor(viewportHeight - rect.top - bottomGap - trailingHeight);
    // In a short window (or below a tall header) the room left under the controls
    // can be a sliver; the canvas then takes at least 60% of the viewport, so the
    // graph is read in a pane of useful height (the page scrolls a little instead).
    const readableHeight = Math.max(280, Math.floor(viewportHeight * 0.6));
    const availableHeight =
      layoutMode === "block" && rawAvailableHeight < 280
        ? viewportMaxHeight
        : rawAvailableHeight < readableHeight
          ? readableHeight
          : Math.max(1, rawAvailableHeight);
    const autoHeight = Math.min(viewportMaxHeight, availableHeight);
    const minHeight = Math.min(autoHeight, 280);
    const currentHeight = parsePixelSize(graphRoot.style.height);
    const state = graphState && typeof graphState === "object" ? graphState : null;

    graphRoot.style.minHeight = minHeight + "px";
    // Keep the initial auto-fit height flow-aware, but leave headroom for explicit
    // user resizing instead of clamping the canvas back to the auto height.
    graphRoot.style.maxHeight = viewportMaxHeight + "px";
    if (
      state &&
      Number.isFinite(currentHeight) &&
      Number.isFinite(state.canvasAutoHeight) &&
      Math.abs(currentHeight - state.canvasAutoHeight) > 1
    ) {
      state.canvasUserResized = true;
    }
    if (state && state.canvasUserResized && Number.isFinite(currentHeight)) {
      const clampedHeight = Math.max(minHeight, Math.min(currentHeight, viewportMaxHeight));
      if (Math.abs(clampedHeight - currentHeight) > 1) {
        graphRoot.style.height = clampedHeight + "px";
      }
      state.canvasAutoHeight = clampedHeight;
      return;
    }
    graphRoot.style.height = autoHeight + "px";
    if (state) state.canvasAutoHeight = autoHeight;
  }

  export function load(src) {
    return new Promise(function (resolve, reject) {
      const s = document.createElement("script");
      s.src = src;
      s.onload = resolve;
      s.onerror = reject;
      document.head.appendChild(s);
    });
  }

  export function graphNodeLabel(node) {
    if (!(node instanceof Element)) return "";
    const titleNode = node.querySelector("title");
    const titleTxt =
      titleNode && typeof titleNode.textContent === "string" ? titleNode.textContent.trim() : "";
    if (titleTxt) return titleTxt;
    const textNode = node.querySelector("text");
    const textTxt =
      textNode && typeof textNode.textContent === "string" ? textNode.textContent.trim() : "";
    return textTxt || "";
  }

  export function graphNodeId(node) {
    if (!(node instanceof Element)) return "";
    const id = node.getAttribute("id");
    return typeof id === "string" ? id.trim() : "";
  }

  export function ensureGraphBlockState(graphBlock) {
    if (!(graphBlock instanceof Element)) return {};
    const existing = graphBlock.__bpGraphState;
    if (existing && typeof existing === "object") return existing;
    const state = {
      previewActiveNode: null,
      previewController: null,
      previewRequestToken: 0,
      groupHoverAnchorNode: null,
      groupHoverController: null,
      groupHoverShownKey: "",
      groupHoverShownNodeId: "",
      graphData: null,
      graphviz: null,
      renderedVariantKey: "",
      renderedOptionsKey: "",
      canvasAutoHeight: null,
      canvasUserResized: false,
      renderToken: 0,
      renderFinalizedToken: 0,
      windowHandlersBound: false,
      blockResizeBound: false,
      resizeObserver: null,
      lastBlockWidth: 0,
      lastCanvasWidth: 0,
      lastCanvasHeight: 0
    };
    graphBlock.__bpGraphState = state;
    return state;
  }

  export function rememberGraphLayoutMeasurements(graphBlock, graphRoot, graphState) {
    if (
      !(graphBlock instanceof Element) ||
      !(graphRoot instanceof Element) ||
      !graphState ||
      typeof graphState !== "object"
    ) {
      return;
    }
    graphState.lastBlockWidth = Math.round(graphBlock.getBoundingClientRect().width);
    graphState.lastCanvasWidth = Math.round(graphRoot.clientWidth);
    graphState.lastCanvasHeight = Math.round(graphRoot.clientHeight);
  }

  export function resizeRenderedGraphToCanvas(graphRoot, graphState) {
    if (!(graphRoot instanceof Element)) return false;
    const svg = graphRoot.querySelector("svg");
    if (!(svg instanceof SVGElement)) return false;
    const nextWidth = Math.round(graphRoot.clientWidth);
    const nextHeight = Math.round(graphRoot.clientHeight);
    if (!(nextWidth > 0) || !(nextHeight > 0)) return false;
    svg.setAttribute("width", String(nextWidth));
    svg.setAttribute("height", String(nextHeight));
    if (graphState && typeof graphState === "object") {
      graphState.lastCanvasWidth = nextWidth;
      graphState.lastCanvasHeight = nextHeight;
    }
    return true;
  }

  // Smallest on-screen scale (CSS pixels per Graphviz point) the first view of a
  // graph uses. Fitting a large graph into a narrow pane can shrink nodes to a few
  // pixels; below this scale the graph starts readable instead, showing its roots.
  export const minReadableGraphScale = 0.5;

  // The rank that holds the graph's roots for a Graphviz `rankdir`: the axis and
  // whether it is the low or the high end of that axis.
  function rootEdge(direction) {
    switch (String(direction || "TB").toUpperCase()) {
      case "BT": return { axis: "y", low: false };
      case "LR": return { axis: "x", low: true };
      case "RL": return { axis: "x", low: false };
      default: return { axis: "y", low: true };
    }
  }

  // After a fitted render: keep node clicks working when the pointer moves a few
  // pixels during a click (d3-zoom otherwise takes it for a drag and swallows the
  // click), and when the fit made the graph unreadably small, zoom to
  // `minReadableGraphScale` with the roots' rank at the canvas's leading edge,
  // centred across it. Pan and zoom stay available. Returns the applied scale
  // (CSS pixels per point), or null when the fitted view was kept.
  export function applyReadableGraphZoom(graphRoot, graphviz, direction, minScale) {
    if (!(graphRoot instanceof Element) || !graphviz) return null;
    const zoom = typeof graphviz.zoomBehavior === "function" ? graphviz.zoomBehavior() : null;
    const selection = typeof graphviz.zoomSelection === "function" ? graphviz.zoomSelection() : null;
    if (!zoom || !selection) return null;
    if (typeof zoom.clickDistance === "function") zoom.clickDistance(6);
    const svg = graphRoot.querySelector("svg");
    const graph = svg ? svg.querySelector("g.graph") || svg.querySelector("g") : null;
    const d3 = typeof window !== "undefined" ? window.d3 : null;
    if (!svg || !graph || !d3 || typeof d3.zoomTransform !== "function" || !d3.zoomIdentity) return null;
    const ctm = svg.getScreenCTM();
    if (!ctm || !(ctm.a > 0)) return null;
    const current = d3.zoomTransform(svg);
    const pxPerPoint = ctm.a * current.k;
    const wanted = Number.isFinite(minScale) && minScale > 0 ? minScale : minReadableGraphScale;
    if (pxPerPoint >= wanted) return null;
    const nodes = Array.from(graph.querySelectorAll("g.node")).map(function (node) {
      try { return node.getBBox(); } catch (_err) { return null; }
    }).filter(function (box) { return box && box.width > 0; });
    if (nodes.length === 0) return null;
    const edge = rootEdge(direction);
    const lead = function (box) {
      return edge.axis === "y" ? (edge.low ? box.y : box.y + box.height) : (edge.low ? box.x : box.x + box.width);
    };
    const leadValues = nodes.map(lead);
    const extreme = edge.low ? Math.min.apply(null, leadValues) : Math.max.apply(null, leadValues);
    const rankSize = Math.max.apply(null, nodes.map(function (box) { return edge.axis === "y" ? box.height : box.width; }));
    const roots = nodes.filter(function (box) { return Math.abs(lead(box) - extreme) <= rankSize / 2; });
    const across = roots.map(function (box) { return edge.axis === "y" ? box.x + box.width / 2 : box.y + box.height / 2; });
    const centre = across.reduce(function (a, b) { return a + b; }, 0) / across.length;
    // the target point in the svg's own (viewBox) coordinates
    const rect = graphRoot.getBoundingClientRect();
    const margin = 24;
    const inv = ctm.inverse();
    const screen = svg.createSVGPoint();
    if (edge.axis === "y") {
      screen.x = rect.left + rect.width / 2;
      screen.y = edge.low ? rect.top + margin : rect.bottom - margin;
    } else {
      screen.x = edge.low ? rect.left + margin : rect.right - margin;
      screen.y = rect.top + rect.height / 2;
    }
    const target = screen.matrixTransform(inv);
    const k = wanted / ctm.a;
    const rx = edge.axis === "y" ? centre : extreme;
    const ry = edge.axis === "y" ? extreme : centre;
    selection.call(zoom.transform, d3.zoomIdentity.translate(target.x - k * rx, target.y - k * ry).scale(k));
    return wanted;
  }

  export function resetGraphvizForVariant(graphRoot, graphState) {
    let cachedGraphviz = null;
    if (graphState && typeof graphState === "object" && graphState.graphviz) {
      cachedGraphviz = graphState.graphviz;
    } else if (graphRoot instanceof Element && graphRoot.__graphviz__) {
      cachedGraphviz = graphRoot.__graphviz__;
    }
    // d3-graphviz caches zoom state on the canvas. Destroy the renderer first
    // so the replacement SVG gets fresh D3 zoom handlers.
    if (cachedGraphviz && typeof cachedGraphviz.destroy === "function") {
      cachedGraphviz.destroy();
    } else if (graphRoot instanceof Element && graphRoot.__graphviz__) {
      delete graphRoot.__graphviz__;
    }
    if (graphRoot instanceof Element) {
      graphRoot.querySelectorAll("svg").forEach(function (svg) {
        svg.remove();
      });
    }
    if (graphState && typeof graphState === "object") {
      graphState.graphviz = null;
      graphState.renderFinalizedToken = 0;
      graphState.lastCanvasWidth = 0;
      graphState.lastCanvasHeight = 0;
      graphState.renderedVariantKey = "";
      graphState.renderedOptionsKey = "";
    }
  }

  function readBehaviorSource(behaviorSource) {
    if (typeof behaviorSource === "function") {
      const behavior = behaviorSource();
      return behavior && typeof behavior === "object" ? behavior : null;
    }
    return behaviorSource && typeof behaviorSource === "object" ? behaviorSource : null;
  }

  function resetPanelPosition(panel) {
    if (!(panel instanceof Element)) return;
    panel.style.left = "";
    panel.style.top = "";
  }

  export function makeGroupPanelPositioner(graphBlock, behaviorSource) {
    return function (panel, anchorNode) {
      const behavior = readBehaviorSource(behaviorSource);
      if (!(panel instanceof Element) || !(graphBlock instanceof Element)) return;
      if (!behavior || !behavior.isAnchored) {
        resetPanelPosition(panel);
        return;
      }
      if (!(anchorNode instanceof Element)) return;
      const blockRect = graphBlock.getBoundingClientRect();
      const nodeRect = anchorNode.getBoundingClientRect();
      const panelRect = panel.getBoundingClientRect();
      const gap = 10;

      let left = nodeRect.right - blockRect.left + gap;
      if (left + panelRect.width > blockRect.width - gap) {
        left = nodeRect.left - blockRect.left - panelRect.width - gap;
      }
      let top = nodeRect.top - blockRect.top + (nodeRect.height - panelRect.height) / 2;

      left = Math.max(gap, Math.min(left, blockRect.width - panelRect.width - gap));
      top = Math.max(gap, Math.min(top, blockRect.height - panelRect.height - gap));
      panel.style.left = left + "px";
      panel.style.top = top + "px";
    };
  }

  export const graphRuntimeCore = {
    debounce,
    normalizeGraphOptions,
    graphPackAttr,
    graphOptionsKey,
    graphLayoutMode,
    readPreviewBehaviorDefaults,
    layoutGraphCanvas,
    load,
    graphNodeLabel,
    graphNodeId,
    ensureGraphBlockState,
    rememberGraphLayoutMeasurements,
    resizeRenderedGraphToCanvas,
    resetGraphvizForVariant,
    applyReadableGraphZoom,
    minReadableGraphScale,
    makeGroupPanelPositioner
  };

export default graphRuntimeCore;
