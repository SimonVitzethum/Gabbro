/- Accepted images read product, floating, string and wide integer sum payloads. -/
module
public import Stage0.Senke.Anweisung.Faelle.Sum.Statement
public import Stage0.Senke.Anweisung.Faelle.Gleit.Proben
@[expose] public section

namespace Gabbro.Stage0.Senke.SumSpanProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR ControlProbe FloatProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev fields : List Ty := [.int 0 (2 ^ 100), .bool]
abbrev schema : List (Option Ty) :=
  [none, some (.prod 7 fields), some (.fl (0, 1) (10, 1)), some (.str 4), some (.int (-(2 ^ 100)) (2 ^ 100))]

/-- Every payload arm reads its bound value; the product arm uses both fields. -/
def arms {Γ : Ctx} : Arms D (vertragVon D entry) false Γ [] [] schema :=
  .cons (returnBlock 42 (by decide) (by decide))
    (.cons (.cons (.ite
      (.and (.eq (.prodGet (.var .here) .head) (.lit (2 ^ 80 + 7)))
        (.prodGet (.var .here) (.tail .head)))
      (returnBlock 42 (by decide) (by decide)) (returnBlock 0 (by decide) (by decide))) .nil)
    (.cons (.cons (.ite (.flle (.var .here) (.var .here))
      (returnBlock 42 (by decide) (by decide)) (returnBlock 0 (by decide) (by decide))) .nil)
    (.cons (.cons (.ite (.and (.eq (.strLen (.var .here)) (.lit 3))
        (.eq (.strGet (.var .here) (.lit 2)) (.lit 255)))
      (returnBlock 42 (by decide) (by decide)) (returnBlock 0 (by decide) (by decide))) .nil)
    (.cons (.cons (.ite (.eq (.var .here) (.lit (-(2 ^ 80) + 7)))
      (returnBlock 42 (by decide) (by decide)) (returnBlock 0 (by decide) (by decide))) .nil) .nil))))

/-- Construction, binding and dispatch all use the ordinary compiler traversal. -/
def dispatch {Γ : Ctx} (value : Expr D Γ [] (.sum schema)) :
    Block D (vertragVon D entry) false Γ [] [] :=
  .bind value (.cons (.onTag (.var .here) arms) .nil)

def product : Expr D [] [] (.sum schema) :=
  .case schema ⟨1, by decide⟩ (.val (.prod 7
    (.cons (.widen (by decide) (by decide) (.lit (2 ^ 80 + 7))) (.cons .tru .nil))))

def string : Expr D [] [] (.sum schema) :=
  .case schema ⟨3, by decide⟩ (.val (.strLit
    [⟨65, by decide, by decide⟩, ⟨0, by decide, by decide⟩, ⟨255, by decide, by decide⟩] (by decide)))

def wide : Expr D [] [] (.sum schema) :=
  .case schema ⟨4, by decide⟩ (.val (.widen (by decide) (by decide) (.lit (-(2 ^ 80) + 7))))

def bare : Expr D [] [] (.sum schema) := .case schema ⟨0, by decide⟩ .empty

def floating : Block D (vertragVon D entry) false [] [] [] :=
  .floatLit (3, 2) (0, 1) (10, 1)
    (dispatch (.case schema ⟨2, by decide⟩ (.val (.var .here))))

def images : List (Except String (List Runner.B)) :=
  [blockImageOf (dispatch product), blockImageOf (dispatch string),
    blockImageOf (dispatch wide), blockImageOf (dispatch bare), blockImageOf floating]

/-- All payload kinds, including the zero-padding bare case, reach whole images. -/
theorem sumSpan_images_zeuge : images.all (·.isOk) = true := by decide +kernel

/-- The new layout retains the complete high limbs and the trailing product flag. -/
theorem sumSpan_encoding_zeuge :
    let layout := layU ControlProbe.u (fun _ => none) 65536
    encodeWords layout (.sum schema) (eval ControlProbe.initial product ControlProbe.initial .nil) =
      [1, 7, 65536, 1, 0, 0] := by decide +kernel

/-- A schema with 257 bare schema is no longer rejected by the old packed-tag limit. -/
def manyCases : List (Option Ty) := List.replicate 257 none

def lastBare : Expr D [] [] (.sum manyCases) :=
  .case manyCases ⟨256, by decide⟩ .empty

theorem sumSpan_many_tags_zeuge :
    (lowE (layU ControlProbe.u (fun _ => none) 65536) lastBare 4).isSome = true := by decide +kernel

/-- The complete payload relation is the premise supplied to the generic dispatcher;
    it includes the product's high limb, not just the tag or first payload word. -/
theorem sumSpan_payload_width_zeuge :
    valueWords (.sum schema) = 6 ∧ payloadWords (some (.prod 7 fields)) = 3 ∧
      sumFits schema = false := by decide +kernel

end Gabbro.Stage0.Senke.SumSpanProbe
