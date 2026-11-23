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

  export function graphNodeLabel(node) {
    if (!(node instanceof Element)) return "";
    const name = node.getAttribute("data-bp-node-name");
    if (typeof name === "string" && name.trim()) return name.trim();
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
      panZoom: null,
      drawingIndex: null,
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
    const svg = graphRoot.querySelector(":scope > svg");
    if (!(svg instanceof SVGElement)) return false;
    const nextWidth = Math.round(graphRoot.clientWidth);
    const nextHeight = Math.round(graphRoot.clientHeight);
    if (!(nextWidth > 0) || !(nextHeight > 0)) return false;
    if (graphState && graphState.panZoom) {
      graphState.panZoom.resize();
    } else {
      svg.setAttribute("width", String(nextWidth));
      svg.setAttribute("height", String(nextHeight));
    }
    if (graphState && typeof graphState === "object") {
      graphState.lastCanvasWidth = nextWidth;
      graphState.lastCanvasHeight = nextHeight;
    }
    return true;
  }

  // Smallest on-screen scale (CSS pixels per unit of the drawing) the first view of a
  // graph uses. Fitting a large graph into a narrow pane can shrink nodes to a few
  // pixels; below this scale the graph starts readable instead, showing its roots.
  export const minReadableGraphScale = 0.5;

  // A drawing that fits whole at this scale or above starts whole, although the fit is below
  // `minReadableGraphScale`: a picture cropped by a little hides more than slightly smaller
  // labels do (12 px labels are about 4.3 px high here, still legible at a glance and read by
  // zooming in). Below it the first view is the readable one, on the roots.
  export const wholeGraphScaleFloor = 0.36;

  // The largest scale a fitted view uses: a graph of a few nodes is not blown up to
  // fill the canvas.
  export const maxFittedGraphScale = 1.4;

  // The layer that holds the graph's roots for a direction: the axis and whether it
  // is the low or the high end of that axis.
  function rootEdge(direction) {
    switch (String(direction || "TB").toUpperCase()) {
      case "BT": return { axis: "y", low: false };
      case "LR": return { axis: "x", low: true };
      case "RL": return { axis: "x", low: false };
      default: return { axis: "y", low: true };
    }
  }

  // The size of a drawing, from the attributes it was written with.
  export function drawingSize(svg) {
    const read = function (name) {
      const value = parseFloat(svg.getAttribute("data-bp-drawing-" + name) || svg.getAttribute(name) || "");
      return isFinite(value) && value > 0 ? value : 0;
    };
    let width = read("width");
    let height = read("height");
    if (!(width > 0) || !(height > 0)) {
      const box = String(svg.getAttribute("viewBox") || "").trim().split(/[\s,]+/).map(parseFloat);
      if (box.length === 4 && box[2] > 0 && box[3] > 0) {
        width = box[2];
        height = box[3];
      }
    }
    return { width: width || 1, height: height || 1 };
  }

  // Where the first view of a drawing of `size` goes in a canvas of `canvas` (both
  // `{ width, height }`): fitted and centred, at most `maxFittedGraphScale`, whenever the
  // fit is at least `wholeGraphScaleFloor` (or `minScale`, when that is smaller); when the
  // fit is smaller still, at `minScale` with the roots' layer (`lead`,
  // the centre of the roots across the layers, in drawing units) at the canvas's
  // leading edge. Returns `{ k, x, y, readable }`.
  export function initialTransform(size, canvas, direction, lead, minScale) {
    const wanted = Number.isFinite(minScale) && minScale > 0 ? minScale : minReadableGraphScale;
    const fit = Math.min(canvas.width / size.width, canvas.height / size.height);
    if (fit >= Math.min(wanted, wholeGraphScaleFloor)) {
      const k = Math.min(fit, maxFittedGraphScale);
      return { k: k, x: (canvas.width - k * size.width) / 2, y: (canvas.height - k * size.height) / 2, readable: false };
    }
    const edge = rootEdge(direction);
    const margin = 24;
    const k = wanted;
    const centre = Number.isFinite(lead) ? lead : (edge.axis === "y" ? size.width : size.height) / 2;
    // Across the layers the roots are centred, but never so that the canvas shows empty room
    // beside a drawing that has more to show: a drawing that fits is centred whole, and a wider
    // one is kept against the canvas's sides.
    const across = function (room, extent) {
      if (k * extent <= room - 2 * margin) return (room - k * extent) / 2;
      return Math.max(room - margin - k * extent, Math.min(margin, room / 2 - k * centre));
    };
    if (edge.axis === "y") {
      return {
        k: k,
        x: across(canvas.width, size.width),
        y: edge.low ? margin : canvas.height - margin - k * size.height,
        readable: true
      };
    }
    return {
      k: k,
      x: edge.low ? margin : canvas.width - margin - k * size.width,
      y: across(canvas.height, size.height),
      readable: true
    };
  }

  // The centre, across the layers, of the nodes in the roots' layer of a drawing.
  function rootsCentre(svg, direction, size) {
    const edge = rootEdge(direction);
    const boxes = [];
    svg.querySelectorAll("g.node").forEach(function (node) {
      try {
        const box = node.getBBox();
        if (box && box.width > 0) boxes.push(box);
      } catch (_err) {}
    });
    if (boxes.length === 0) return NaN;
    const lead = function (box) {
      return edge.axis === "y" ? (edge.low ? box.y : box.y + box.height) : (edge.low ? box.x : box.x + box.width);
    };
    const leads = boxes.map(lead);
    const extreme = edge.low ? Math.min.apply(null, leads) : Math.max.apply(null, leads);
    const layer = Math.max.apply(null, boxes.map(function (box) { return edge.axis === "y" ? box.height : box.width; }));
    const roots = boxes.filter(function (box) { return Math.abs(lead(box) - extreme) <= layer / 2; });
    const across = roots.map(function (box) { return edge.axis === "y" ? box.x + box.width / 2 : box.y + box.height / 2; });
    const centre = across.reduce(function (a, b) { return a + b; }, 0) / across.length;
    return Number.isFinite(centre) ? centre : (edge.axis === "y" ? size.width : size.height) / 2;
  }

  // Pan and zoom of a drawing in its canvas. The drawing's `g.graph` gets a
  // transform; the `svg` element takes the size of the canvas. The wheel zooms about
  // the pointer, a drag pans (a press that moves less than a few pixels stays a
  // click), two fingers pinch, and the keys `+`, `-` and the arrows do the same from
  // the keyboard; `0` goes back to the first view and, pressed there, shows the whole
  // drawing. Nothing is animated. Returns the controller:
  // `fit()`, `resize()`, `transform()`, `setTransform({k, x, y})`, `destroy()`.
  export function createPanZoom(graphRoot, svg, options) {
    const opts = options && typeof options === "object" ? options : {};
    const group = svg.querySelector("g.graph") || svg.querySelector("g");
    const size = drawingSize(svg);
    svg.setAttribute("data-bp-drawing-width", String(size.width));
    svg.setAttribute("data-bp-drawing-height", String(size.height));
    svg.removeAttribute("viewBox");
    const state = { k: 1, x: 0, y: 0 };
    let minK = 0.05;
    const maxK = 8;
    const canvasSize = function () {
      return { width: Math.max(1, graphRoot.clientWidth), height: Math.max(1, graphRoot.clientHeight) };
    };
    const apply = function () {
      if (group) {
        group.setAttribute(
          "transform",
          "translate(" + state.x.toFixed(2) + "," + state.y.toFixed(2) + ") scale(" + state.k.toFixed(5) + ")"
        );
      }
      svg.setAttribute("data-bp-graph-scale", state.k.toFixed(4));
    };
    const sizeSvg = function () {
      const canvas = canvasSize();
      svg.setAttribute("width", String(canvas.width));
      svg.setAttribute("height", String(canvas.height));
      return canvas;
    };
    const fit = function () {
      const canvas = sizeSvg();
      let first = initialTransform(size, canvas, opts.direction, NaN, opts.minScale);
      if (first.readable) {
        // a mirrored drawing's own coordinates are those of the direction it was drawn for
        first = initialTransform(size, canvas, opts.direction, rootsCentre(svg, opts.geometry || opts.direction, size), opts.minScale);
      }
      minK = Math.min(first.k, Math.min(canvas.width / size.width, canvas.height / size.height)) * 0.5;
      state.k = first.k;
      state.x = first.x;
      state.y = first.y;
      apply();
      svg.setAttribute("data-bp-graph-readable", first.readable ? "1" : "0");
      return first;
    };
    // the whole drawing in the canvas, however small that makes it
    const whole = function () {
      const canvas = sizeSvg();
      const k = Math.min(canvas.width / size.width, canvas.height / size.height, maxFittedGraphScale);
      state.k = k;
      state.x = (canvas.width - k * size.width) / 2;
      state.y = (canvas.height - k * size.height) / 2;
      apply();
    };
    const zoomAbout = function (px, py, factor) {
      const k = Math.max(minK, Math.min(maxK, state.k * factor));
      const ratio = k / state.k;
      state.x = px - ratio * (px - state.x);
      state.y = py - ratio * (py - state.y);
      state.k = k;
      apply();
    };
    const local = function (ev) {
      const rect = svg.getBoundingClientRect();
      return { x: ev.clientX - rect.left, y: ev.clientY - rect.top };
    };
    const pointers = new Map();
    let dragged = false;
    let pinch = 0;
    const onWheel = function (ev) {
      ev.preventDefault();
      const unit = ev.deltaMode === 1 ? 16 : ev.deltaMode === 2 ? 400 : 1;
      const p = local(ev);
      zoomAbout(p.x, p.y, Math.exp(-ev.deltaY * unit * (ev.ctrlKey ? 0.01 : 0.0015)));
    };
    const onDown = function (ev) {
      if (ev.pointerType === "mouse" && ev.button !== 0) return;
      pointers.set(ev.pointerId, { x: ev.clientX, y: ev.clientY, startX: ev.clientX, startY: ev.clientY });
      if (pointers.size === 1) dragged = false;
      if (pointers.size === 2) {
        const pts = Array.from(pointers.values());
        pinch = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
      }
    };
    const onMove = function (ev) {
      const p = pointers.get(ev.pointerId);
      if (!p) return;
      const dx = ev.clientX - p.x;
      const dy = ev.clientY - p.y;
      p.x = ev.clientX;
      p.y = ev.clientY;
      if (pointers.size === 1) {
        // a press that moves less than this stays a click on a node
        if (!dragged && Math.hypot(ev.clientX - p.startX, ev.clientY - p.startY) < 6) return;
        if (!dragged) {
          dragged = true;
          try { svg.setPointerCapture(ev.pointerId); } catch (_err) {}
          svg.setAttribute("data-bp-graph-panning", "1");
        }
        state.x += dx;
        state.y += dy;
        apply();
      } else if (pointers.size === 2) {
        dragged = true;
        const pts = Array.from(pointers.values());
        const distance = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
        const rect = svg.getBoundingClientRect();
        if (pinch > 0 && distance > 0) {
          zoomAbout((pts[0].x + pts[1].x) / 2 - rect.left, (pts[0].y + pts[1].y) / 2 - rect.top, distance / pinch);
        }
        pinch = distance;
      }
    };
    const onUp = function (ev) {
      if (!pointers.has(ev.pointerId)) return;
      pointers.delete(ev.pointerId);
      try { svg.releasePointerCapture(ev.pointerId); } catch (_err) {}
      if (pointers.size === 0) svg.removeAttribute("data-bp-graph-panning");
    };
    // the click that ends a drag is not a click on what lies under the pointer
    const onClick = function (ev) {
      if (!dragged) return;
      dragged = false;
      ev.preventDefault();
      ev.stopPropagation();
    };
    const onDouble = function (ev) {
      if (ev.target instanceof Element && ev.target.closest("g.node")) return;
      const p = local(ev);
      zoomAbout(p.x, p.y, ev.shiftKey ? 1 / 1.6 : 1.6);
    };
    const onKey = function (ev) {
      if (ev.target !== svg || ev.metaKey || ev.ctrlKey || ev.altKey) return;
      const canvas = canvasSize();
      const step = 60;
      switch (ev.key) {
        case "+": case "=": zoomAbout(canvas.width / 2, canvas.height / 2, 1.25); break;
        case "-": case "_": zoomAbout(canvas.width / 2, canvas.height / 2, 0.8); break;
        case "0": {
          // back to the first view; from the first view, the whole drawing
          const before = state.k + "," + state.x + "," + state.y;
          fit();
          if (before === state.k + "," + state.x + "," + state.y) whole();
          break;
        }
        case "ArrowLeft": state.x += step; apply(); break;
        case "ArrowRight": state.x -= step; apply(); break;
        case "ArrowUp": state.y += step; apply(); break;
        case "ArrowDown": state.y -= step; apply(); break;
        default: return;
      }
      ev.preventDefault();
    };
    svg.addEventListener("wheel", onWheel, { passive: false });
    svg.addEventListener("pointerdown", onDown);
    svg.addEventListener("pointermove", onMove);
    svg.addEventListener("pointerup", onUp);
    svg.addEventListener("pointercancel", onUp);
    svg.addEventListener("click", onClick, true);
    svg.addEventListener("dblclick", onDouble);
    svg.addEventListener("keydown", onKey);
    if (!svg.hasAttribute("tabindex")) svg.setAttribute("tabindex", "0");
    const controller = {
      fit: fit,
      whole: whole,
      // the canvas changed size: the point at its centre stays at its centre
      resize: function () {
        const before = { width: parseFloat(svg.getAttribute("width")) || 0, height: parseFloat(svg.getAttribute("height")) || 0 };
        const canvas = sizeSvg();
        state.x += (canvas.width - before.width) / 2;
        state.y += (canvas.height - before.height) / 2;
        apply();
      },
      transform: function () { return { k: state.k, x: state.x, y: state.y }; },
      setTransform: function (next) {
        if (!next || !(next.k > 0)) return;
        state.k = next.k;
        state.x = Number.isFinite(next.x) ? next.x : state.x;
        state.y = Number.isFinite(next.y) ? next.y : state.y;
        apply();
      },
      zoomBy: function (factor) {
        const canvas = canvasSize();
        zoomAbout(canvas.width / 2, canvas.height / 2, factor);
      },
      destroy: function () {
        svg.removeEventListener("wheel", onWheel);
        svg.removeEventListener("pointerdown", onDown);
        svg.removeEventListener("pointermove", onMove);
        svg.removeEventListener("pointerup", onUp);
        svg.removeEventListener("pointercancel", onUp);
        svg.removeEventListener("click", onClick, true);
        svg.removeEventListener("dblclick", onDouble);
        svg.removeEventListener("keydown", onKey);
      }
    };
    fit();
    return controller;
  }

  // A drawing's labels are sized for a sans-serif face of Helvetica's metrics. Where
  // the page's face is wider, a label that would pass its node's outline is drawn
  // at the width that fits. Drawings of very many nodes are left as they are.
  export function fitDrawingLabels(svg, limit) {
    const nodes = svg.querySelectorAll("g.node");
    if (nodes.length > (limit || 1500)) return 0;
    let fitted = 0;
    const todo = [];
    nodes.forEach(function (node) {
      const outline = node.querySelector(":scope > path, :scope > ellipse");
      if (!outline) return;
      let room = 0;
      try { room = outline.getBBox().width; } catch (_err) { return; }
      const ellipse = outline.localName === "ellipse";
      node.querySelectorAll(":scope > text").forEach(function (text) {
        let length = 0;
        try { length = text.getComputedTextLength(); } catch (_err) { return; }
        const most = (ellipse ? room * 0.82 : room) - 8;
        if (length > most && most > 8) todo.push([text, most]);
      });
    });
    todo.forEach(function (entry) {
      entry[0].setAttribute("textLength", entry[1].toFixed(1));
      entry[0].setAttribute("lengthAdjust", "spacingAndGlyphs");
      fitted += 1;
    });
    return fitted;
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

  // Route tracing. Pointing at an edge, or pointing at or focusing a node, highlights the whole
  // route of each edge concerned, from the port it leaves to the arrowhead it reaches, and dims
  // the rest of the drawing. Everything it needs was written into the drawing when the site was
  // built (`Informal.GraphLayout.withRouteData`): an edge's `data-from` and `data-to`, the path
  // data of its own parts of shared stems (`data-stems`), and the arrowheads by port
  // (`data-node`) or by edge (`data-edge`). The page draws those stem parts as given and
  // computes nothing about the layout.
  const traceNamespace = "http://www.w3.org/2000/svg";

  function traceGroup(svg) {
    let group = svg.querySelector("g.edges > g.bp_graph_trace");
    if (!group) {
      const edges = svg.querySelector("g.edges");
      if (!edges) return null;
      group = document.createElementNS(traceNamespace, "g");
      group.setAttribute("class", "bp_graph_trace");
      edges.appendChild(group);
    }
    return group;
  }

  // Highlight the routes of `edges` (elements `path.edge`) and their nodes; an empty list
  // clears the highlight.
  export function traceRoutes(svg, edges) {
    svg.querySelectorAll("[data-bp-traced]").forEach(function (el) {
      el.removeAttribute("data-bp-traced");
    });
    const group = traceGroup(svg);
    if (group) group.replaceChildren();
    if (!edges || edges.length === 0) {
      svg.removeAttribute("data-bp-tracing");
      return;
    }
    svg.setAttribute("data-bp-tracing", "1");
    const nodeIds = new Set();
    edges.forEach(function (edge) {
      edge.setAttribute("data-bp-traced", "1");
      const from = edge.getAttribute("data-from") || "";
      const to = edge.getAttribute("data-to") || "";
      if (from) nodeIds.add(from);
      if (to) nodeIds.add(to);
      const stems = edge.getAttribute("data-stems") || "";
      if (stems && group) {
        const piece = document.createElementNS(traceNamespace, "path");
        piece.setAttribute("d", stems);
        piece.setAttribute("data-bp-traced", "1");
        const width = edge.getAttribute("stroke-width");
        if (width) piece.setAttribute("stroke-width", width);
        group.appendChild(piece);
      }
      const index = edge.getAttribute("data-edge");
      svg.querySelectorAll("g.heads > path").forEach(function (head) {
        const own = index !== null && head.getAttribute("data-edge") === index;
        const port = to && head.getAttribute("data-port") === "in" && head.getAttribute("data-node") === to;
        if (own || port) head.setAttribute("data-bp-traced", "1");
      });
    });
    svg.querySelectorAll("g.node").forEach(function (node) {
      if (nodeIds.has(node.getAttribute("id") || "")) node.setAttribute("data-bp-traced", "1");
    });
  }

  // The edges whose route starts or ends at a node.
  function edgesOfNode(svg, node) {
    const id = node.getAttribute("id") || "";
    if (!id) return [];
    return Array.from(svg.querySelectorAll("g.edges > path.edge")).filter(function (edge) {
      return edge.getAttribute("data-from") === id || edge.getAttribute("data-to") === id;
    });
  }

  // Bind route tracing to a drawing shown in the page: pointer over an edge or a node, and
  // keyboard focus on a node. An edge is hard to hit at its drawn width, so a transparent wider
  // copy of every edge lies under the pointer (`g.bp_graph_edge_hits`).
  export function bindRouteTracing(svg) {
    if (!svg || svg.getAttribute("data-bp-route-tracing") === "1") return;
    const edges = Array.from(svg.querySelectorAll("g.edges > path.edge"));
    if (edges.length === 0 || !edges[0].hasAttribute("data-from")) return;
    svg.setAttribute("data-bp-route-tracing", "1");
    const edgesGroup = svg.querySelector("g.edges");
    const hits = document.createElementNS(traceNamespace, "g");
    hits.setAttribute("class", "bp_graph_edge_hits");
    edges.forEach(function (edge) {
      const hit = document.createElementNS(traceNamespace, "path");
      hit.setAttribute("d", edge.getAttribute("d") || "");
      hit.setAttribute("data-bp-hit-edge", edge.getAttribute("data-edge") || "");
      hits.appendChild(hit);
    });
    edgesGroup.parentNode.insertBefore(hits, edgesGroup.nextSibling);
    const byIndex = new Map(edges.map(function (edge) { return [edge.getAttribute("data-edge"), edge]; }));
    let current = null;
    const show = function (key, list) {
      if (current === key) return;
      current = key;
      traceRoutes(svg, list);
    };
    svg.addEventListener("pointerover", function (ev) {
      const target = ev.target instanceof Element ? ev.target : null;
      if (!target) return;
      const hit = target.closest("[data-bp-hit-edge]");
      if (hit) {
        const edge = byIndex.get(hit.getAttribute("data-bp-hit-edge"));
        show("edge:" + hit.getAttribute("data-bp-hit-edge"), edge ? [edge] : []);
        return;
      }
      const node = target.closest("g.node");
      if (node) {
        show("node:" + (node.getAttribute("id") || ""), edgesOfNode(svg, node));
        return;
      }
      show(null, []);
    });
    svg.addEventListener("pointerleave", function () { show(null, []); });
    svg.addEventListener("focusin", function (ev) {
      const node = ev.target instanceof Element ? ev.target.closest("g.node") : null;
      if (node) show("node:" + (node.getAttribute("id") || ""), edgesOfNode(svg, node));
    });
    svg.addEventListener("focusout", function (ev) {
      const next = ev.relatedTarget instanceof Element ? ev.relatedTarget.closest("g.node") : null;
      if (!next || !svg.contains(next)) show(null, []);
    });
    svg.addEventListener("keydown", function (ev) {
      if (ev.key === "Escape") show(null, []);
    });
  }

  export const graphRuntimeCore = {
    debounce,
    normalizeGraphOptions,
    graphPackAttr,
    graphOptionsKey,
    graphLayoutMode,
    readPreviewBehaviorDefaults,
    layoutGraphCanvas,
    graphNodeLabel,
    graphNodeId,
    ensureGraphBlockState,
    rememberGraphLayoutMeasurements,
    resizeRenderedGraphToCanvas,
    minReadableGraphScale,
    wholeGraphScaleFloor,
    maxFittedGraphScale,
    drawingSize,
    initialTransform,
    createPanZoom,
    fitDrawingLabels,
    traceRoutes,
    bindRouteTracing,
    makeGroupPanelPositioner
  };

export default graphRuntimeCore;
