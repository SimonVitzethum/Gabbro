/-
  File:      Grammatik/CFormenFZeuge.lean
  Subject:   The witness of `CFormenF.lean` on the emitted C of a corpus
             program: `klemmen` of `beispiele/26-gleitkomma.gab`.

  THE SOURCE:
      const HALB : f64 = 0.5;
      impl fn klemmen(x : f64) -> Anteil        -- Anteil = f64 in 0.0 .. 1.0
      { narrow x to 0.0 .. 1.0 else { return HALB; } return x; }

  THE EMITTED C (`gabbro emit beispiele/26-gleitkomma.gab`, 2026-09-14,
  the binary of the main checkout):
      #define HALB 0.5
      static double klemmen(double x) {
          if (!(x >= 0.0 && x <= 1.0)) {
              return HALB;
          }
          return x;
      }
  After preprocessing `return HALB;` is `return 0.5;`. In the model `x` is C
  local 0, and every literal is the bit pattern of its correctly rounded
  value (`kNull_bits`, `kEins_bits`, `kHalb_bits` pin them).

  THE GABBRO BODY (the model binds the constant, `Block.gleitLit`, since an
  `Endblock` has no float literal; C inlines it):
      let halb = 0.5 rounded in 0 .. 1;
      narrow x to 0 .. 1 else { return halb; }
      return x;
  The parameter's range `lo0 .. hi0` is free: the theorem holds for every
  one (the model's floats are finite and range-carrying; an unranged `f64`
  parameter is a range the certificate names).

  `klemmen_corr`: the body corresponds to the emitted C under the
  judgement of CFormenR.lean (`BlockSemG`, no ghost, no channel), for every
  context `X` -- both branches, from every related state. The inline
  literal is handled here per program (CFormenF.lean CUTS).
  `klemmen_lauf`: the C condition on `x = 2.0` evaluates to `0` (the check
  fails, `return 0.5`), on `x = 0.25` to `1`, by computation.
  `klemmen_maschine`: under the named assumption `gleitkomma_ieee`, the
  machine's comparisons on those bits give the same answers.
-/
import Grammatik.CFormenF

namespace Gabbro.Grammatik

open Gleitkomma (f64 wf)

variable {D : Deklaration}

/-! ## 1. The Gabbro body -/

/-- `Anteil = f64 in 0.0 .. 1.0`. -/
abbrev kAnteil : Ty := .fl (0, 1) (1, 1)

/-- The contract of `klemmen`: pure, answers an `Anteil`. -/
abbrev kV (D : Deklaration) : Vertrag D where
  schreibt := fun _ => false
  gschreibt := fun _ => false
  erg := some kAnteil
  gruende := 0
  haelt := []
  produziert := []

/-- The context after `let halb`: `halb`, then the parameter `x`. -/
abbrev kΓ (lo0 hi0 : Int × Int) : Ctx := [kAnteil, .fl lo0 hi0]

/-- `else { return halb; }` -/
def kSonst (lo0 hi0 : Int × Int) : Endblock D (kV D) false (kΓ lo0 hi0) [] :=
  .ret (.wert (.var .hier)) (List.Perm.refl _)

/-- `return x;` (the narrowed `x`). -/
def kRest (lo0 hi0 : Int × Int) : Block D (kV D) false (kAnteil :: kΓ lo0 hi0) [] [] :=
  .cons (.ret (.wert (.var .hier)) (List.Perm.refl _)) .nil

/-- `narrow x to 0 .. 1 else { return halb; } return x;` -/
def kNarrow (lo0 hi0 : Int × Int) : Block D (kV D) false (kΓ lo0 hi0) [] [] :=
  .gleitNarrow (.var (.dort .hier)) (0, 1) (1, 1) (kSonst lo0 hi0) (kRest lo0 hi0)

/-- The body: `let halb = 0.5 rounded; …`. -/
def kBlock (lo0 hi0 : Int × Int) : Block D (kV D) false [.fl lo0 hi0] [] [] :=
  .gleitLit (1, 2) (0, 1) (1, 1) (kNarrow lo0 hi0)

/-- `0.5` in `0 .. 1`: the value `halb` is bound to. -/
def kHalb : Gleit (0, 1) (1, 1) := ⟨bruch (1, 2), by decide, by decide, by decide⟩

/-! ## 2. The emitted C -/

/-- `x >= 0.0 && x <= 1.0`, `x` in C local 0. -/
def kCond : CX :=
  .land (.fcmp .ge f64 (.var 0) (.lit (fEin f64 (bruch (0, 1)))))
    (.fcmp .le f64 (.var 0) (.lit (fEin f64 (bruch (1, 1)))))

/-- The body of `klemmen` as emitted (`double` is the `uint64_t` bit
    container of the model). -/
def kC : CS :=
  .seq (.ite (.lnot kCond) (.ret (some (.int false .w64, .lit (fEin f64 (bruch (1, 2)))))) .skip)
    (.ret (some (.int false .w64, .var 0)))

/-- The literals are the IEEE doubles the C text denotes. -/
theorem kNull_bits : fEin f64 (bruch (0, 1)) = 0 := by decide
theorem kEins_bits : fEin f64 (bruch (1, 1)) = 0x3FF0000000000000 := by decide
theorem kHalb_bits : fEin f64 (bruch (1, 2)) = 0x3FE0000000000000 := by decide

/-- The locals of the certificate: `x` is C local 0. -/
def kK (lo0 hi0 : Int × Int) : CEnvLay D [.fl lo0 hi0] := ⟨[0], [], []⟩

/-! ## 3. The correspondence -/

/-- **`klemmen` corresponds to its emitted C**, for every context and every
    parameter range. -/
theorem klemmen_corr (X : TVCtx D) (lo0 hi0 : Int × Int) :
    BlockSemG X 0 G0 (kK lo0 hi0) (kBlock lo0 hi0) kC := by
  intro σ st ρG ρC hc hrel _
  have hrel0 := (envRelG0 X (kK lo0 hi0) ρG ρC st).mp hrel
  have hx : ρC 0 = .int (fEin f64 (ρG.get .hier).x) ∧ wf f64 (ρG.get .hier).x :=
    hrel0.1 _ .hier
  -- the condition, by the general lemma (the C `x` is `ecorr_var`)
  obtain ⟨st1, h1, hs1⟩ :=
    narrowCondF_ge_le X G0 (kK lo0 hi0) (ecorr_var X (kK lo0 hi0) (Λ := []) .hier) (0, 1) (1, 1)
      σ st ρG ρC hc hrel
  have h1' : ev X.EL.lay X.orc X.fr kCond st ρC =
      some (.int (b2i (gleitPasst (0, 1) (1, 1) (ρG.get .hier).x).isSome), st1) := h1
  have hc1 : corrW X.EL σ st1 := corrW_same hc hs1
  -- the Gabbro side: `halb` binds `0.5`
  have hH : gleitPasst (0, 1) (1, 1) (bruch (1, 2)) = some kHalb := gleitPasst_selbst kHalb
  have hex1 : execBlock X.O X.passes X.R (kBlock (D := D) lo0 hi0) σ ρG =
      match gleitPasst (0, 1) (1, 1) (bruch (1, 2)) with
      | some v => (execBlock X.O X.passes X.R (kNarrow lo0 hi0) σ (.cons v ρG)).schrumpf
      | none => .logik .bereich := rfl
  rw [hex1, hH]
  simp only [kNarrow, execBlock, eval, Expr.orte]
  split
  next v hgp0 =>
      -- the check passes: `return x;` with the narrowed value
      have hgp : gleitPasst (0, 1) (1, 1) (ρG.get .hier).x = some v := hgp0
      rw [hgp] at h1'
      have hout : ((execBlock X.O X.passes X.R (kRest (D := D) lo0 hi0) (σ.lese [] [])
          (.cons v (.cons kHalb ρG))).schrumpf).schrumpf =
          .zurueck (((σ.lese [] []).lese [] [])) v := rfl
      rw [hout]
      have hvx := gleitPasst_x hgp
      have hev : ev X.EL.lay X.orc X.fr (.var 0) st1 ρC =
          some (.int (fEin f64 (ρG.get .hier).x), st1) := by simp only [ev, hx.1]
      refine ⟨_, Exec.seqN (Exec.iteF (ev_lnot h1' (truth_b2i _)) rfl Exec.skip)
        (Exec.retS hev (convV_fEin _ hx.2)), ?_⟩
      refine ⟨st1, _, rfl, hc1, _, rfl, ?_, ?_⟩
      · show CVal.int (fEin f64 (ρG.get .hier).x) = .int (fEin f64 v.x)
        rw [hvx]
      · show wf f64 v.x
        rw [hvx]; exact hx.2
  next hgp0 =>
      -- the check fails: `return 0.5;`
      have hgp : gleitPasst (0, 1) (1, 1) (ρG.get .hier).x = none := hgp0
      rw [hgp] at h1'
      have hout : ((execEnd X.O X.passes X.R (kSonst (D := D) lo0 hi0) (σ.lese [] [])
          (.cons kHalb ρG)).zuAusgang).schrumpf =
          .zurueck ((σ.lese [] []).lese [] []) kHalb := rfl
      rw [hout]
      refine ⟨_, Exec.seqX (Exec.iteT (ev_lnot h1' (truth_b2i _)) rfl
        (Exec.retS (rfl : ev X.EL.lay X.orc X.fr (.lit (fEin f64 (bruch (1, 2)))) st1 ρC = _)
          (convV_fEin _ (bruch_wf _)))) rfl, ?_⟩
      exact ⟨st1, _, rfl, hc1, _, rfl, rfl, bruch_wf _⟩

/-! ## 4. Runs, and the machine under the named assumption -/

/-- The C condition, computed: `x = 2.0` fails the check (`return 0.5`),
    `x = 0.25` passes it (`return x`). -/
theorem klemmen_lauf (L : CLayout) (orc : DevOrc) (fr : Nat) (st : CSt) :
    ev L orc fr kCond st (fun _ => .int 0x4000000000000000) = some (.int 0, st) ∧
    ev L orc fr kCond st (fun _ => .int 0x3FD0000000000000) = some (.int 1, st) := by
  constructor <;> rfl

/-- **The named assumption at work**: whatever float unit the built binary
    runs on, if it meets `gleitkomma_ieee`, its `>=`/`<=` on the bits of
    `2.0` against the literals `0.0`/`1.0` answer `true`/`false` -- the check
    fails and `klemmen(2.0)` returns `0.5`. -/
theorem klemmen_maschine (u : FloatUnit) (hu : gleitkomma_ieee u) :
    u.cmp .ge f64 0x4000000000000000 (fEin f64 (bruch (0, 1))) = true ∧
    u.cmp .le f64 0x4000000000000000 (fEin f64 (bruch (1, 1))) = false := by
  rw [(hu f64 (Or.inr rfl)).2.1, (hu f64 (Or.inr rfl)).2.1]
  constructor <;> decide

/-- The assumption is inhabited, so `klemmen_maschine` is not vacuous. -/
theorem klemmen_maschine_zeuge :
    annexF.cmp .ge f64 0x4000000000000000 (fEin f64 (bruch (0, 1))) = true :=
  (klemmen_maschine annexF gleitkomma_ieee_annexF).1

#print axioms klemmen_corr
#print axioms klemmen_lauf
#print axioms klemmen_maschine
#print axioms kHalb_bits

end Gabbro.Grammatik
