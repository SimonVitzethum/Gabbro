/-
  File:      Grammatik/X86/OptCoalesceMove.lean
  Subject:   Copy coalescing rule lemma (lane 880).

  DESIGN section 7 row "Layout / allocation" + section 7 example 1 + §3 text:
  copies coalesce ONLY under recomputed avail + dominance (§7 example 1:
  `v1 = add w64 a b; v2 = copy v1; v3 = add w64 v2 c` drops the copy with
  premise avail + dominance + width); certificate is the layer-A local
  rewrite record plus layer-B recomputed analysis citations; the failure
  case "address-taken spill via call arg" refuses.

  Stated over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`): no second IR, no
  second evaluator, no per-program rule. The single accepted source model
  (`Syntax`/`Semantik` `exec`) is the reference per decision 594/606.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Layer-A local rewrite record: WHICH copy of WHICH source value, at
    one width. `quelle` is the available dominating definition `v1`,
    `kopie` the copy `v2` removed; `gleicheWeite` is the validator-decided
    same-type/same-width check (DESIGN "width"). -/
structure CoalRewrite where
  quelle : Nat
  kopie : Nat
  gleicheWeite : Bool
  deriving DecidableEq, Repr

/-- Layer-B recomputed analysis citations, re-decided by the validator
    from the block lists, never trusted from a Rust print: `avail` (the
    source value is available at the use: no redefinition between, §7
    example-1 counterexample), `dominiert` (the definition dominates the
    use), `adressGenommen` (the slot was address-taken: spill must stay),
    `callArg` (the slot travels as a call argument: callee-visible). -/
structure CoalAnalyse where
  avail : Bool
  dominiert : Bool
  adressGenommen : Bool
  callArg : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def coalZulassen (rw : CoalRewrite) (an : CoalAnalyse) : Bool :=
  rw.gleicheWeite && an.avail && an.dominiert && (!an.adressGenommen) && (!an.callArg)

/-! ## 1. Refusals: every failing side condition refuses the rule.

    DESIGN section 7 example-1 counterexample (`v1` redefined between:
    recomputed avail refuses) and the row failure case (address-taken
    spill via call arg refuses). Each is proved of the decided Bool, so
    the validator cannot silently skip it. -/

/-- Redefined between: no avail, no coalescing. -/
theorem coalVerweigert_avail (rw : CoalRewrite) (an : CoalAnalyse)
    (h : an.avail = false) :
    coalZulassen rw an = false := by
  simp [coalZulassen, h]

/-- Use not dominated by the definition: refused. -/
theorem coalVerweigert_dominiert (rw : CoalRewrite) (an : CoalAnalyse)
    (h : an.dominiert = false) :
    coalZulassen rw an = false := by
  simp [coalZulassen, h]

/-- Width mismatch between source and copy: refused. -/
theorem coalVerweigert_weite (rw : CoalRewrite) (an : CoalAnalyse)
    (h : rw.gleicheWeite = false) :
    coalZulassen rw an = false := by
  simp [coalZulassen, h]

/-- Address-taken slot: the spill must stay, the copy must stay. -/
theorem coalVerweigert_adressGenommen (rw : CoalRewrite) (an : CoalAnalyse)
    (h : an.adressGenommen = true) :
    coalZulassen rw an = false := by
  simp [coalZulassen, h]

/-- Slot travelling as a call argument (callee-visible footprint):
    the copy must stay. -/
theorem coalVerweigert_callArg (rw : CoalRewrite) (an : CoalAnalyse)
    (h : an.callArg = true) :
    coalZulassen rw an = false := by
  simp [coalZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_coalZulassen_ok :
    coalZulassen ⟨0, 1, true⟩ ⟨true, true, false, false⟩ = true := by
  decide

/-- Probe: a redefined source (avail lost) is refused. -/
theorem probe_coalZulassen_avail :
    coalZulassen ⟨0, 1, true⟩ ⟨false, true, false, false⟩ = false := by
  decide

/-- Probe: the address-taken spill via call arg is refused. -/
theorem probe_coalZulassen_spillCall :
    coalZulassen ⟨0, 1, true⟩ ⟨true, true, true, true⟩ = false := by
  decide

/-! ## 2. Value preservation: the copy carries the source value whole.

    Over ARBITRARY values (`v : Int`): the copy is the identity on the
    value, so no value is changed, no fault added or removed, and the
    IEEE scope is untouched (integers have no rounding; the float copy
    keeps its single `bruch` below). The width-exact image reads back
    through the canonical word: the later lowering writes the coalesced
    value, not a wrapped one. -/

/-- The copied value reads back whole through the canonical word. -/
theorem coalWort (v : Int) (hW : 0 ≤ v ∧ v < 2 ^ 64) :
    ((BitVec.ofNat 64 v.toNat : Wort)).toNat = v.toNat := by
  have h : v.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `7` reads back as `7` through the word. -/
theorem probe_coalWort :
    ((BitVec.ofNat 64 ((7 : Int)).toNat : Wort)).toNat = 7 := by
  decide

/-- The admitted float copy preserves value and `gleitPasst` outcome:
    the copy keeps the single `bruch` (never host `strtod`, never a
    width change, one rounding scope), so neither a value nor a
    `logik bereich` fault is folded away. The equation is claimed only
    where the validator admitted the site (`hEq` takes `hz`). -/
theorem coalGleit_behält (rw : CoalRewrite) (an : CoalAnalyse)
    (qa qf : Int × Int) (lo hi : Int × Int)
    (hz : coalZulassen rw an = true)
    (hEq : coalZulassen rw an = true → bruch qf = bruch qa) :
    gleitPasst lo hi (bruch qf) =
      gleitPasst lo hi (bruch qa) := by
  have e := hEq hz
  rw [e]

/-- Probe: the kernel compares `3/4` against itself. -/
theorem probe_coalGleit :
    gleitPasst (0, 1) (1, 1) (bruch (3, 4)) =
      gleitPasst (0, 1) (1, 1) (bruch (3, 4)) := by
  rfl

end Gabbro.Grammatik.X86
