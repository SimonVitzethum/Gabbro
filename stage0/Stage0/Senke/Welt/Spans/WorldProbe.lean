/- Joint inhabited full-world fixture with two genuine three-word table cells. -/
import Stage0.Senke.Welt.Spans.StoreWorld
import Stage0.Senke.Welt.Spans.SpanProbe
namespace Gabbro.Stage0.Senke.WorldProbe
set_option maxHeartbeats 1000000
open Gabbro.Grammatik Runner.IR Runner.Mem
abbrev shape := SpanProbe.shape
@[reducible] def D : Deklaration := { GRegion.rD with typ := fun _ _ => shape }
def layout : Lay D where
  regionCells _ := 2
  col _ _ := 8192
  ga g := nomatch g
  lo := 8192
  hi := 8240
  tor _ := none
  byte _ := none

def first : Wert D shape := SpanProbe.value
def second : Wert D shape := fun i => ⟨i.val + 4, by omega, by have := i.isLt; omega⟩
def world : World D where
  slots _ k _ := if k = 0 then first else second
  globs g := nomatch g
  spur := []
def memory : Runner.Mem where
  b a := if a.toNat = 8192 then 1 else if a.toNat = 8200 then 2 else if a.toNat = 8208 then 3
    else if a.toNat = 8216 then 4 else if a.toNat = 8224 then 5 else if a.toNat = 8232 then 6 else 0
  rd _ := true
  wr _ := true

theorem layout_in : LayIn layout := by
  refine ⟨fun t f k hk => ?_, (fun g => nomatch g), by decide⟩
  change (k : Int) < 2 at hk
  change 8192 ≤ 8192 + 24 * k ∧ 8192 + 24 * k + 24 ≤ 8240
  omega

theorem layout_apart : LayDis layout := by
  constructor
  · intro c c' hc hc' ne
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t; cases t'; cases f; cases f'
        have different : k ≠ k' := by intro eq; subst k'; exact ne rfl
        change 8192 + 24 * k + 24 ≤ 8192 + 24 * k' ∨ 8192 + 24 * k' + 24 ≤ 8192 + 24 * k
        omega
  · intro c c' hc hc' eq
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t; cases t'; cases f; cases f'
        change 8192 + 24 * k = 8192 + 24 * k' at eq
        have same : k = k' := by omega
        subst k'; rfl
  · intro c hc
    cases c with
    | glob g => nomatch g
    | elem t f k => change (8192 + 24 * k) % 8 = 8192 % 8; omega

theorem world_at : WeltAt memory layout world := by
  refine ⟨fun t f k hk => ?_, (fun g => nomatch g), fun _ _ _ => rfl⟩
  change (k : Int) < 2 at hk
  have cases : k = 0 ∨ k = 1 := by omega
  rcases cases with rfl | rfl
  · constructor
    · intro i; trivial
    · change WordsAt memory 8192 0 [1, 2, 3]
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
      rcases cases with rfl | rfl | rfl <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
  · constructor
    · intro i; trivial
    · change WordsAt memory 8216 0 [4, 5, 6]
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
      rcases cases with rfl | rfl | rfl <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem full_world_update_zeuge :
    WeltAt (writeSpan memory 8192 (encodeWords layout shape second)) layout
      (world.storeSlot () 0 () second) ∧ layout.elem () () 1 = 8216 :=
by
  constructor
  · exact weltAt_slot (D := D) (L := layout) (m := memory) (σ := world) (t := ()) (f := ()) (kn := 0) (v := second)
      world_at layout_in layout_apart (by decide) (by intro i; trivial)
  · rfl
end Gabbro.Stage0.Senke.WorldProbe
