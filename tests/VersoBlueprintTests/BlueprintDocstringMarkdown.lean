/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Vergo
-/

import VersoBlueprintTests.Blueprint.Support
import VersoBlueprint.CodeSite.Main

/-!
Docstrings rendered from Markdown when the site is built (`Informal.Docstring.markdownDocstringToHtml`,
through Verso's Markdown renderer), with docstring text treated as untrusted input: raw HTML,
text that looks like markup or script, links with unusual schemes, and very long input. The same
renderer serves declaration panels (`Informal.renderPlainDecl`) and the declaration cards of sites
generated from compiled-code data (`Informal.CodeSite.docHtml`).
-/

namespace Verso.VersoBlueprintTests.BlueprintDocstringMarkdown

open Informal
open Verso.VersoBlueprintTests.Blueprint.Support

/-- A docstring rendered as the site writes it. -/
def render (doc : String) : String :=
  (Informal.Docstring.markdownDocstringToHtml doc).render

/-! ## Raw HTML is text -/

-- Inline HTML, an HTML block and an HTML comment are parsed as text and written escaped: the
-- page gets no element, attribute or comment from them.
/-- info: "<p>A &lt;b onclick=\"x()\"&gt;bold&lt;/b&gt; word and &lt;img src=x onerror=alert(1)&gt;.</p>" -/
#guard_msgs in
#eval render "A <b onclick=\"x()\">bold</b> word and <img src=x onerror=alert(1)>."

/-- info: "<p>&lt;div&gt;\n&lt;script&gt;alert(1)&lt;/script&gt;\n&lt;/div&gt;</p><p>&lt;!-- a comment --&gt;</p>" -/
#guard_msgs in
#eval render "<div>\n<script>alert(1)</script>\n</div>\n\n<!-- a comment -->"

/-- info: "<p>&lt;style&gt;body{display:none}&lt;/style&gt;&lt;iframe src=\"https://example.com\"&gt;&lt;/iframe&gt;</p>" -/
#guard_msgs in
#eval render "<style>body{display:none}</style><iframe src=\"https://example.com\"></iframe>"

/-! ## Text that looks like markup -/

-- A closing tag, a script element split by an entity, CDATA, a template expression and a
-- literal `&lt;` all stay text; entities are decoded once and escaped again on output.
/-- info: "<p>&lt;/div&gt;&lt;/pre&gt;&lt;script&gt;alert(1)&lt;/script&gt; &lt;![CDATA[x]]&gt; {{x}} &lt;b&gt; &amp;</p>" -/
#guard_msgs in
#eval render "</div></pre><scr&#105;pt>alert(1)</script> <![CDATA[x]]> {{x}} &lt;b&gt; &amp;"

-- Code spans and code blocks keep script-like text as escaped code.
/-- info: "<p><code>&lt;script&gt;alert(1)&lt;/script&gt;</code></p><pre><code>&lt;/code&gt;&lt;/pre&gt;&lt;script&gt;alert(2)&lt;/script&gt;\n</code></pre>" -/
#guard_msgs in
#eval render "`<script>alert(1)</script>`\n\n```\n</code></pre><script>alert(2)</script>\n```"

/-! ## Links -/

-- Links and images keep relative targets and the `http`, `https` and `mailto` schemes (images
-- also `data`); any other scheme, however it is spelled, leaves the link's text (or the image's
-- alternative text) and no link.
/-- info: "<p>a b c d e f</p>" -/
#guard_msgs in
#eval render "[a](javascript:alert(1)) [b](JaVaScRiPt:alert(1)) [c](java&#x09;script:alert(1)) \
  [d](vbscript:msgbox(1)) [e](data:text/html,<script>alert(1)</script>) [f](file:///etc/passwd)"

/-- info: "<p>javascript:alert(1) g h i j</p>" -/
#guard_msgs in
#eval render "<javascript:alert(1)> [g](%6Aavascript:alert(1)) [h]( javascript:alert(1)) \
  ![i](javascript:alert(1)) [j](\\javascript:alert(1))"

-- Allowed targets are kept. In an attribute value `&` and `"` are escaped, so a target cannot end
-- its attribute; the angle brackets left in the quoted value are inert there.
/-- info: "<p><a href=\"https://example.com/?q=&quot;><script>alert(1)</script>\">k</a> <a href=\"mailto:a@b.c\">l</a> <a href=\"../Chapter/#x\">m</a> <img src=\"data:image/png;base64,AAAA\" alt=\"n\" title=\"t&quot;itle\"/> <a href=\"https://example.org/x\">https://example.org/x</a></p>" -/
#guard_msgs in
#eval render "[k](https://example.com/?q=\"><script>alert(1)</script>) [l](mailto:a@b.c) \
  [m](../Chapter/#x) ![n](data:image/png;base64,AAAA \"t\\\"itle\") https://example.org/x"

/-! ## Very long input -/

-- A paragraph of a million characters and ten thousand list items are rendered in full; two
-- thousand nested quotations give two thousand `blockquote` elements; ten thousand emphasis
-- markers and a hundred thousand brackets are rendered without a link and without failing.
/-- info: true -/
#guard_msgs in
#eval
  let long := String.ofList (List.replicate 1000000 'a')
  let out := render long
  out == "<p>" ++ long ++ "</p>"

/-- info: true -/
#guard_msgs in
#eval
  let items := String.join (List.replicate 10000 "- <x>\n")
  let out := render items
  countSubstr out "<li>&lt;x&gt;</li>" == 10000 && !hasSubstr out "<x>"

/-- info: (2000, true) -/
#guard_msgs in
#eval
  let depth := 2000
  let nested := String.join (List.replicate depth "> ") ++ "deep"
  let out := render nested
  (countSubstr out "<blockquote>", hasSubstr out "deep")

/-- info: (42508, true, 100007, true) -/
#guard_msgs in
#eval
  let emph := String.join (List.replicate 5000 "*") ++ "x" ++ String.join (List.replicate 5000 "*")
  let brackets := String.join (List.replicate 50000 "[") ++ String.join (List.replicate 50000 "]")
  let out1 := render emph
  let out2 := render brackets
  (out1.length, hasSubstr out1 "x", out2.length, !hasSubstr out2 "<a")

/-! ## The renderer's users -/

-- A declaration panel from text alone and a declaration card of a generated site render the
-- docstring the same way.
/-- info: true -/
#guard_msgs in
#eval
  let doc := "Raw <script>alert(1)</script> and [x](javascript:alert(1))."
  let panel := (renderPlainDecl `Demo.x "def" "x : Nat" (some doc)).html
  let card := CodeSite.docHtml doc
  hasSubstr panel "<div class=\"docstring\">" && hasSubstr panel (render doc) &&
    card == render doc && !hasSubstr panel "<script" && !hasSubstr panel "javascript:"

end Verso.VersoBlueprintTests.BlueprintDocstringMarkdown
