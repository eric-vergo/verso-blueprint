import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual

namespace PreviewRuntimeShowcase.Chapters.Motion

/-- A script-free animated figure: a dot turning about a centre, once every four seconds, with a
still picture of its first frame and a caption link to the switch. The figure announces its motion
with `data-bp-motion` and uses the hook classes of `Informal.Motion`. -/
def figureHtml : String := r##"<figure class="bp_motion_demo" data-bp-motion="" id="bp-motion-demo">
<div class="bp_motion_live">
<svg id="bp-motion-demo-svg" width="120" height="120" viewBox="-60 -60 120 120" role="img" aria-label="A dot turning about a centre">
<circle r="40" fill="none" stroke="currentColor" stroke-opacity="0.4" stroke-width="2"/>
<circle r="3" fill="currentColor"/>
<g id="bp-motion-demo-arm">
<animateTransform attributeName="transform" type="rotate" from="0" to="360" dur="4s" repeatCount="indefinite"/>
<circle id="bp-motion-demo-dot" cx="40" cy="0" r="9" fill="currentColor"/>
</g>
</svg>
</div>
<div class="bp_motion_stills">
<svg width="120" height="120" viewBox="-60 -60 120 120" role="img" aria-label="A dot on a circle about a centre">
<circle r="40" fill="none" stroke="currentColor" stroke-opacity="0.4" stroke-width="2"/>
<circle r="3" fill="currentColor"/>
<circle cx="40" cy="0" r="9" fill="currentColor"/>
</svg>
</div>
<figcaption>A dot turning about a centre. <a class="bp_motion_link" href="#bp-motion">Animations can be turned off in the page menu.</a></figcaption>
</figure>"##

open Verso Doc Elab Genre Manual in
block_extension Block.motionFigure where
  data := Lean.Json.null
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ _ => pure (.raw figureHtml)
  toTeX := some fun _ _ _ _ _ => pure .empty

open Verso Doc Elab in
@[block_command]
public meta def motion_figure : BlockCommandOf Unit
  | () => ``(Block.other Block.motionFigure #[])

end PreviewRuntimeShowcase.Chapters.Motion

open PreviewRuntimeShowcase.Chapters.Motion

#doc (Manual) "Animated Figures" =>

%%%
number := false
%%%

A figure that moves by itself, written as inline SVG with a declarative animation and no script.
The page shows a switch that turns animations off.

{motion_figure}
