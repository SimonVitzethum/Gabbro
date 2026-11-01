/- Subject: Large-lower-bound tag decoding on actual code bytes and frame memory. -/
import Stage0.Senke.Anweisung.Faelle.Tag
import Stage0.Senke.Ausdruck.Aggregat.Proben

namespace Gabbro.Stage0.Senke.TagDecodeProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open AggregateProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def payload := (wordConstant 5 (2 ^ 32)).1

def decoder : List II :=
  [ci 1 5 8 0, ci 12 4 4 5] ++ payload ++ [ci 3 4 4 5]

def code : List II := Case.code ++ decoder

def memory : Runner.Mem where
  b a := ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem pre [Kern] : PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    ?_, ?_, ?_, trivial, wstab_true _ _⟩
  · apply codeAt_bytes code 0 (by decide +kernel)
    intro i hi
    have hs : (code.flatMap encII).length < 2 ^ 64 := by decide +kernel
    refine ⟨rfl, rfl, ?_⟩
    simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.getElem?_eq_getElem hi, Option.getD_some]
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

/-- The real constructor leaves 10753 (tag 1, offset 42); the decoder recovers
    2^32 + 42. Both phases use their generic memory simulation theorem. -/
theorem simulation_zeuge [Kern] :
    tagPayloadC 4 (some (2 ^ 32, 2 ^ 32 + 100)) = some decoder ∧
    Case.top = 7 ∧ decoder.length = 20 ∧
    PreS layout memory 0 65536 64 4 code (Env.nil : Env D []) ∧
    Ok memory 0 65536 64 4 code (· = BitVec.ofInt 64 (2 ^ 32 + 42)) := by
  have hw : ∀ m, WeltAt m layout world := by
    intro m
    refine ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), ?_⟩
    · intro x hl hh
      change 65536 ≤ x at hl
      change x < 65536 at hh
      omega
  have hl : lowE layout Case.expr 4 = some (Case.code, Case.top) := by decide +kernel
  have hp := pre
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp, ?_⟩
  have packed : Ok memory 0 65536 64 4 Case.code (· = 10753) :=
    (lowE_ok world world (W := fun _ => True) (fun m _ => hw m) hLay
      Case.expr 4 Case.code Case.top hl (by decide +kernel) memory 0 .nil hp.left
      |>.word (wordCompatB_sound _ (by decide +kernel))).mono
      (fun _ hn => hn.2.trans (by decide +kernel))
  apply ok_seq hp packed (hK := by decide)
  intro m w hp hr he
  have run := tagPayload_ok (L := layout) (lo := 2 ^ 32) (hi := 2 ^ 32 + 100)
    (v := ⟨2 ^ 32 + 42, by decide, by decide⟩) (by decide) hp hr
    (by rw [he]; decide +kernel)
  exact run

/-- The actual statement dispatcher accepts all three one-word lower-bound domains. -/
theorem dispatcher_zeuge (A : D.Fn → Nat) (frame : FrameLayout) (ens : List II × Nat)
    (pr : List Nat) (ex : Int × Int) :
    ∀ lower ∈ ([2 ^ 32, -(2 ^ 32) - 100, 2 ^ 64 - 101] : List Int),
      let cs := [none, some (lower, lower + 100)]
      let arms : Arms D (vertragVon D (⟨0, by decide⟩ : D.Fn)) false [.sum cs] [] [] cs :=
        .cons .nil (.cons .nil .nil)
      ∃ c top, lowS 0 A layout frame ens pr ex (.onTag (.var .here) arms) = some (c, top) := by
  intro lower hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

end Gabbro.Stage0.Senke.TagDecodeProbe
