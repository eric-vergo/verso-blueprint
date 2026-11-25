"""Browser checks for the names on the dependency graph's nodes.

A node with a Lean statement shows the short name of its statement's first declaration in the
code face; a node without one (`aids_proof_only`, whose only declaration is attached to its proof)
shows its number. These checks cover both labels on the showcase's graph, that no label overflows
its node's box and no two boxes overlap at desktop and phone widths in the light and dark themes,
the `Node text` switch in the graph options and the reader's choice being remembered, finding a
node by its number or its Lean name through the page's fragments, and the accessible name keeping
the number and the status words.
"""

import pytest
from playwright.sync_api import Page, expect

from support import wait_for_graph_rendered

NAMED = "aids_sectioned"
NAMED_ID = "bp-node-aids-005Fsectioned"
UNNAMED = "aids_proof_only"
UNNAMED_ID = "bp-node-aids-005Fproof-005Fonly"

# the reader's choice, kept for the site (served from the root here)
STORAGE_KEY = "bp-graph-node-text:/"


def graph_node_data(page: Page, label: str) -> dict:
    return page.evaluate(
        """(label) => document.querySelector('.bp_graph_fullwidth').__bpGraphData.nodes
            .find((n) => n.label === label)""",
        label,
    )


def open_graph(page: Page, server: str, fragment: str = "", width: int = 1440,
               height: int = 900, theme: str = "light") -> None:
    page.set_viewport_size({"width": width, "height": height})
    page.emulate_media(color_scheme=theme)
    page.goto(server + "/Dependency-Graph/" + fragment, wait_until="domcontentloaded")
    wait_for_graph_rendered(page)


def visible_label(page: Page, node_id: str) -> str:
    return page.evaluate(
        """(id) => Array.from(document.querySelectorAll(
                `.bp_graph_canvas > svg g.node[id='${id}'] > text`))
            .filter((t) => getComputedStyle(t).display !== 'none')
            .map((t) => t.textContent).join(' / ')""",
        node_id,
    )


GEOMETRY = """() => {
  const svg = document.querySelector('.bp_graph_canvas > svg');
  const nodes = Array.from(svg.querySelectorAll('g.node'));
  const boxes = nodes.map((n) => {
    const o = n.querySelector(':scope > path, :scope > ellipse').getBBox();
    const texts = Array.from(n.querySelectorAll(':scope > text'))
      .filter((t) => getComputedStyle(t).display !== 'none');
    return { id: n.id, o, ellipse: !!n.querySelector(':scope > ellipse'),
             texts: texts.map((t) => ({ box: t.getBBox(), text: t.textContent })) };
  });
  const overflow = [];
  boxes.forEach((b) => b.texts.forEach((t) => {
    if (t.box.x < b.o.x - 0.5 || t.box.x + t.box.width > b.o.x + b.o.width + 0.5) {
      overflow.push(b.id + ': ' + t.text);
    }
  }));
  const overlap = [];
  for (let i = 0; i < boxes.length; i++) {
    for (let j = i + 1; j < boxes.length; j++) {
      const a = boxes[i].o, c = boxes[j].o;
      if (a.x < c.x + c.width && c.x < a.x + a.width && a.y < c.y + c.height && c.y < a.y + a.height) {
        overlap.push(boxes[i].id + ' / ' + boxes[j].id);
      }
    }
  }
  return { nodes: boxes.length, overflow, overlap,
           shown: boxes.reduce((n, b) => n + b.texts.length, 0) };
}"""


class TestGraphNodeNames:
    def test_a_node_with_a_lean_statement_shows_its_short_name_in_code_face(self, server: str, page: Page):
        open_graph(page, server)
        node = page.locator(f".bp_graph_canvas > svg g.node[id='{NAMED_ID}']")
        expect(node).to_have_count(1)
        name = node.locator("text.bp_graph_label_name")
        expect(name).to_have_count(1)
        expect(name).to_be_visible()
        assert name.text_content() == "aidSectioned"
        expect(node.locator("text.bp_graph_label_number")).to_be_hidden()
        # the site's code face, not the face of the number labels
        name_face = name.evaluate("(t) => getComputedStyle(t).fontFamily")
        code_face = page.evaluate(
            """() => { const probe = document.createElement('code');
                 probe.style.fontFamily = 'var(--verso-code-font-family)';
                 document.body.appendChild(probe);
                 const face = getComputedStyle(probe).fontFamily; probe.remove(); return face; }""")
        number_face = node.locator("text.bp_graph_label_number").evaluate(
            "(t) => getComputedStyle(t).fontFamily")
        assert name_face == code_face, (name_face, code_face)
        assert name_face != number_face

    def test_a_node_without_a_lean_statement_shows_its_number(self, server: str, page: Page):
        open_graph(page, server)
        data = graph_node_data(page, UNNAMED)
        assert data["leanNames"] == [], "a declaration attached only to the proof names no statement"
        node = page.locator(f".bp_graph_canvas > svg g.node[id='{UNNAMED_ID}']")
        expect(node.locator("text.bp_graph_label_name")).to_have_count(0)
        assert visible_label(page, UNNAMED_ID) == data["title"]
        assert data["title"].startswith("Theorem ")

    @pytest.mark.parametrize("theme", ["light", "dark"])
    @pytest.mark.parametrize("width,height", [(1440, 900), (390, 844)])
    @pytest.mark.parametrize("node_text", ["name", "number"])
    def test_labels_stay_inside_their_boxes_and_boxes_do_not_overlap(
            self, server: str, page: Page, theme: str, width: int, height: int, node_text: str):
        page.add_init_script(
            f"try {{ localStorage.setItem('{STORAGE_KEY}', '{node_text}'); }} catch (e) {{}}")
        open_graph(page, server, width=width, height=height, theme=theme)
        assert page.get_attribute(".bp_graph_fullwidth", "data-bp-graph-node-text") == node_text
        geometry = page.evaluate(GEOMETRY)
        assert geometry["nodes"] > 20
        assert geometry["shown"] >= geometry["nodes"], "every node shows a label"
        assert geometry["overflow"] == [], geometry["overflow"]
        assert geometry["overlap"] == [], geometry["overlap"]

    def test_the_switch_in_the_graph_options_is_remembered(self, server: str, page: Page):
        open_graph(page, server)
        page.evaluate(f"() => localStorage.removeItem('{STORAGE_KEY}')")
        open_graph(page, server)
        title = graph_node_data(page, NAMED)["title"]
        assert visible_label(page, NAMED_ID) == "aidSectioned"
        page.locator(".bp_graph_options_button").click()
        select = page.locator(".bp_graph_node_text_select")
        expect(select).to_be_visible()
        expect(select).to_have_value("name")
        expect(select.locator("option")).to_have_text(["Lean name", "Number"])
        select.select_option("number")
        assert visible_label(page, NAMED_ID) == title
        assert visible_label(page, UNNAMED_ID) == graph_node_data(page, UNNAMED)["title"]
        assert page.evaluate(f"() => localStorage.getItem('{STORAGE_KEY}')") == "number"
        # a reload, and another view of the graph, keep the reader's choice
        open_graph(page, server)
        expect(page.locator(".bp_graph_node_text_select")).to_have_value("number")
        assert visible_label(page, NAMED_ID) == title
        page.evaluate(
            "() => document.querySelector('.bp_graph_fullwidth').__bpGraphController.setNodeText('name')")
        assert visible_label(page, NAMED_ID) == "aidSectioned"
        page.evaluate(f"() => localStorage.removeItem('{STORAGE_KEY}')")

    def test_without_scripts_the_drawing_shows_the_site_default(self, server: str, browser):
        context = browser.new_context(java_script_enabled=False)
        page = context.new_page()
        try:
            page.goto(server + "/Dependency-Graph/", wait_until="domcontentloaded")
            node = page.locator(f".bp_graph_first_drawing svg g.node[id='{NAMED_ID}']")
            expect(node.locator("text.bp_graph_label_name")).to_be_visible()
            expect(node.locator("text.bp_graph_label_number")).to_be_hidden()
        finally:
            context.close()

    def test_a_node_is_found_by_its_number_or_its_lean_name(self, server: str, page: Page):
        open_graph(page, server)
        data = graph_node_data(page, NAMED)
        full = data["leanNames"][0]["name"]
        # the node view by number, with its kind or alone
        for query in (data["title"].replace(" ", "%20"), data["title"].split(" ")[-1]):
            open_graph(page, server, "#node=" + query)
            page.wait_for_selector(".bp_graph_preview .bp_node_view", timeout=60000)
            assert page.evaluate(
                "() => document.querySelector('.bp_graph_fullwidth').__bpGraphState.nodeViewLabel") == NAMED
        # the neighbourhood view by the short name and by the full name
        for query in ("aidSectioned", full):
            open_graph(page, server, "#ego=" + query + "&k=1")
            canvas = page.locator(".bp_graph_canvas")
            expect(canvas).to_have_attribute("data-bp-active-view", "ego")
            expect(canvas).to_have_attribute("data-bp-graph-ego", NAMED)

    def test_the_accessible_name_keeps_the_number_and_the_status_words(self, server: str, page: Page):
        open_graph(page, server)
        data = graph_node_data(page, NAMED)
        node = page.locator(f".bp_graph_canvas > svg g.node[id='{NAMED_ID}']")
        label = node.get_attribute("aria-label") or ""
        status = data["visual"]["tooltip"]
        assert label.startswith(f"{data['title']} ({NAMED}), Lean name {data['leanNames'][0]['name']}: "), label
        assert label.endswith(status), (label, status)
        unnamed = page.locator(f".bp_graph_canvas > svg g.node[id='{UNNAMED_ID}']")
        unnamed_label = unnamed.get_attribute("aria-label") or ""
        assert unnamed_label.startswith(graph_node_data(page, UNNAMED)["title"]), unnamed_label
        assert "Lean name" not in unnamed_label
        assert unnamed_label.endswith("No Lean declaration")

    def test_another_sites_choice_does_not_apply_here(self, server: str, page: Page):
        """The reader's choice is kept per site: a choice made on another site of the same origin
        leaves this one on its author's default."""
        page.add_init_script(
            "try { localStorage.setItem('bp-graph-node-text:/another-site/', 'number'); } catch (e) {}")
        open_graph(page, server)
        assert page.get_attribute(".bp_graph_fullwidth", "data-bp-graph-node-text") == "name"
        assert visible_label(page, NAMED_ID) == "aidSectioned"

    def test_a_named_node_shows_its_number_and_full_names_on_hover(self, server: str, page: Page):
        open_graph(page, server)
        data = graph_node_data(page, NAMED)
        node = page.locator(f".bp_graph_canvas > svg g.node[id='{NAMED_ID}']")
        title = node.locator(":scope > title")
        expect(title).to_have_count(1)
        lines = (title.text_content() or "").split("\n")
        assert lines[0] == f"{data['title']} ({NAMED})", lines
        assert lines[1:] == [d["name"] + ("" if d["present"] else " (not found)")
                             for d in data["leanNames"]], lines
        assert node.get_attribute("data-bp-node-name") == NAMED
        # a declaration named but not found is marked so in the hover, and still named
        missing = page.evaluate(
            """() => document.querySelector('.bp_graph_fullwidth').__bpGraphData.nodes
                .find((n) => (n.leanNames || []).some((d) => !d.present))""")
        assert missing, "the showcase has a node whose declaration is missing"
        node_id = page.evaluate(
            """(label) => Array.from(document.querySelectorAll('.bp_graph_canvas > svg g.node'))
                .find((n) => n.getAttribute('data-bp-node-name') === label).id""", missing["label"])
        hover = page.locator(f".bp_graph_canvas > svg g.node[id='{node_id}'] > title").text_content()
        gone = [d["name"] for d in missing["leanNames"] if not d["present"]]
        assert all(f"{name} (not found)" in hover for name in gone), hover

    def test_no_two_nodes_read_the_same(self, server: str, page: Page):
        """After shortening, no two labels on the graph are the same text, nor the same text around
        their ellipses; nodes showing one declaration carry their numbers under it."""
        open_graph(page, server)
        labels = page.evaluate(
            """() => Array.from(document.querySelectorAll('.bp_graph_canvas > svg g.node'))
                .map((n) => Array.from(n.querySelectorAll(':scope > text'))
                  .filter((t) => getComputedStyle(t).display !== 'none')
                  .map((t) => t.textContent).join('|'))""")
        assert len(labels) == len(set(labels)), sorted(l for l in labels if labels.count(l) > 1)

        def around(label: str) -> str:
            head, _, rest = label.partition("…")
            return head[:4] + "…" + rest[-4:]
        cut = [l for l in labels if "…" in l and "|" not in l.split("…")[-1]]
        keys = [around(l) for l in cut]
        assert len(keys) == len(set(keys)), [l for l in cut if keys.count(around(l)) > 1]
        # the showcase attaches `Nat.add` to several nodes: each shows its number under it
        adds = [l for l in labels if l.split("|")[0] == "add"]
        assert len(adds) >= 2 and all(len(l.split("|")) == 2 for l in adds), adds
