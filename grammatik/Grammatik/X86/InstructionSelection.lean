/-
  File:      Grammatik/X86/InstructionSelection.lean
  Subject:   Invariant-derived register-only instruction selection over real bytes.

  Lane 600: connects the accepted source facts (`InvariantenOpt`: literal-zero
  justification, stability-gated loads; `StaerkeReduktion`: value facts) to an
  actual encoded pilot-instruction choice. Three register-only rules: zeroing
  (`movImm64 0` vs `xor dst dst`), add-zero elimination, self-move elimination.
  Every rule reuses source `eval`/`execBlock` and the canonical decoded `schritt`;
  no new interpreter, no new IR. Flag liveness and alias equality are checked
  data; Rust-provided metadata is never trusted.
-/
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86.Anweisungswahl

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.InvariantenOpt

/-- Zeroing choice: flags-live keeps the preserving 10-byte `movImm64 0`,
    flags-dead takes the clobbering 3-byte `xor dst dst`. -/
def waehleNull (flagsLive : Bool) (dst : Register) : List Befehl :=
  if flagsLive then [.movImm64 dst 0] else [.xorReg64 dst dst]

/-- Add-zero elimination: with a justified zero in `src` and dead flags the
    `add` vanishes; with live flags it is kept. -/
def waehleAddNull (flagsLive : Bool) (dst src : Register) : List Befehl :=
  if flagsLive then [.addReg64 dst src] else []

/-- Self-move elimination: `mov dst dst` is a no-op; a move between two
    different registers is kept (checked alias equality). -/
def waehleSelbstMov (dst src : Register) : List Befehl :=
  if dst = src then [] else [.movReg64 dst src]

/-- Flag/branch checker: a clobbering `xor` under live flags is refused. -/
def wahlOk (flagsLive : Bool) (wahl : List Befehl) : Bool :=
  match flagsLive, wahl with
  | true, [.xorReg64 _ _] => false
  | _, _ => true

/-- Invariant-gated elimination: the tag records which leg discharges the
    site guarantee; without a held stability fact nothing is eliminated. -/
def waehleInv (s : InvScope) (stabil : Bool) : Option (List Befehl) :=
  match s with
  | .ruhe => if stabil then some [] else none
  | .sicht => if stabil then some [] else none
  | .wechsel => if stabil then some [] else none

/-! ## 2. Target value facts: what the chosen instructions compute. -/

/-- `xor v v` is zero: the clobbering zeroing choice really zeroes. -/
theorem xor_selbst_null (v : Wort) : (xor64 v v).1 = 0 := by
  simp [xor64]

/-- `add x 0` is `x`: the eliminated add is a value identity. -/
theorem add_null_ident (x : Wort) : (add64 x 0).1 = x := by
  simp [add64]

/-! ## 3. Real byte sequences: the choices differ on the wire. -/

/-- The preserving zeroing choice is 10 bytes, the clobbering one 3:
    selection is a length claim, not just a value claim. -/
theorem null_laengen (dst : Register) :
    (encode (.movImm64 dst 0)).length = 10 ∧
      (encode (.xorReg64 dst dst)).length = 3 := by
  cases dst <;> decide

/-- Pinned bytes of the clobbering zeroing of `rax`. -/
theorem pin_xor_rax : encode (.xorReg64 .rax .rax) =
    [natByte 72, natByte 49, natByte 192] := by
  decide

/-- Pinned bytes of the preserving zeroing of `rax`: 10 bytes. -/
theorem pin_mov0_rax : encode (.movImm64 .rax 0) =
    [natByte 72, natByte 184, natByte 0, natByte 0, natByte 0,
     natByte 0, natByte 0, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Both pinned choices decode back to themselves (accepted round trip). -/
theorem runde_null_rax (suffix : List Byte) :
    decode (encode (.xorReg64 .rax .rax) ++ suffix) =
      some (⟨.xorReg64 .rax .rax, (encode (.xorReg64 .rax .rax)).length⟩,
        suffix) ∧
    decode (encode (.movImm64 .rax 0) ++ suffix) =
      some (⟨.movImm64 .rax 0, (encode (.movImm64 .rax 0)).length⟩,
        suffix) :=
  ⟨roundtrip _ _, roundtrip _ _⟩

/-! ## 4. Executed-step observations: both choices zero the register. -/

/-- Executed `movImm64 dst 0` zeroes `dst` through the canonical step. -/
theorem schritt_null_mov (s : Zustand) (dst : Register) :
    (schritt ⟨.movImm64 dst 0, 10⟩ s).map (fun s' => s'.register dst) =
      some 0 := by
  have h := schritt_movImm64 ⟨.movImm64 dst 0, 10⟩ s dst 0 rfl rfl
  rw [h]
  simp [schrittRegister, regSet]

/-- Executed `xor dst dst` zeroes `dst` through the canonical step. -/
theorem schritt_null_xor (s : Zustand) (dst : Register) :
    (schritt ⟨.xorReg64 dst dst, 3⟩ s).map (fun s' => s'.register dst) =
      some 0 := by
  have h := schritt_xorReg64 ⟨.xorReg64 dst dst, 3⟩ s dst dst rfl rfl
  rw [h]
  have hz : (xor64 (s.register dst) (s.register dst)).1 = 0 :=
    xor_selbst_null _
  simp [schrittRegister, regSet, hz]

/-- Value agreement: the two executed choices observe the same register. -/
theorem schritt_null_gleich (s : Zustand) (dst : Register) :
    (schritt ⟨.xorReg64 dst dst, 3⟩ s).map (fun s' => s'.register dst) =
      (schritt ⟨.movImm64 dst 0, 10⟩ s).map
        (fun s' => s'.register dst) := by
  rw [schritt_null_xor, schritt_null_mov]

/-! ## 5. Flag observations: the value agreement costs the flags. -/

/-- `xor v v` sets ZF: the clobbering choice leaves a set zero flag. -/
theorem xor_selbst_zf (v : Wort) : (xor64 v v).2.zf = true := by
  simp [xor64, zfTest]

/-- A following `je` diverges: under live flags (`zf = false`) the preserving
    choice falls through while the clobbering choice would take the branch.
    Missing flag liveness is therefore rejected, not ignored. -/
theorem zweig_weicht_ab (s : Zustand) (dst : Register)
    (hdead : s.flags.zf = false) :
    bedingung .e s.flags = false ∧
      bedingung .e (xor64 (s.register dst) (s.register dst)).2 = true := by
  simp [bedingung, hdead, xor_selbst_zf]

/-- The selector keeps `mov` under live flags. -/
theorem waehleNull_le (dst : Register) :
    waehleNull true dst = [.movImm64 dst 0] := rfl

/-- The selector takes `xor` only under dead flags. -/
theorem waehleNull_tot (dst : Register) :
    waehleNull false dst = [.xorReg64 dst dst] := rfl

/-- The checker refuses the clobbering choice under live flags. -/
theorem wahlOk_verweigert_xor_le (dst : Register) :
    wahlOk true [.xorReg64 dst dst] = false := rfl

/-- The checker allows the preserving choice under live flags. -/
theorem wahlOk_erlaubt_mov (dst : Register) :
    wahlOk true [.movImm64 dst 0] = true := rfl

/-- The checker allows the clobbering choice under dead flags. -/
theorem wahlOk_erlaubt_tot (dst : Register) :
    wahlOk false [.xorReg64 dst dst] = true := rfl

/-! ## 6. Elimination rules: add-zero and self-move. -/

/-- Executed `add dst src` with `src` holding zero keeps `dst`'s value. -/
theorem schritt_addNull_wert (s : Zustand) (dst src : Register)
    (h0 : s.register src = 0) :
    (schritt ⟨.addReg64 dst src, 3⟩ s).map (fun s' => s'.register dst) =
      some (s.register dst) := by
  have h := schritt_addReg64 ⟨.addReg64 dst src, 3⟩ s dst src rfl rfl
  rw [h]
  have hz : (add64 (s.register dst) (s.register src)).1 = s.register dst := by
    rw [h0]
    exact add_null_ident _
  simp [schrittRegister, regSet, hz]

/-- Add-zero elimination preserves the value observation under dead flags. -/
theorem waehleAddNull_tot (dst src : Register) :
    waehleAddNull false dst src = [] := rfl

/-- Add-zero is kept under live flags: the flags would change. -/
theorem waehleAddNull_le (dst src : Register) :
    waehleAddNull true dst src = [.addReg64 dst src] := rfl

/-- Self-move elimination: `mov dst dst` is kept nowhere. -/
theorem waehleSelbstMov_gleich (r : Register) :
    waehleSelbstMov r r = [] := by
  simp [waehleSelbstMov]

/-- A move between two different registers is kept: the alias check fires. -/
theorem waehleSelbstMov_fremd (dst src : Register) (h : dst ≠ src) :
    waehleSelbstMov dst src = [.movReg64 dst src] := by
  simp [waehleSelbstMov, h]

/-- Executed self-move is a value identity through the canonical step. -/
theorem schritt_selbstMov_ident (s : Zustand) (r : Register) :
    (schritt ⟨.movReg64 r r, 3⟩ s).map (fun s' => s'.register r) =
      some (s.register r) := by
  have h := schritt_movReg64 ⟨.movReg64 r r, 3⟩ s r r rfl rfl
  rw [h]
  simp [schrittRegister, regSet]

/-! ## 7. Source connection: a justified zero, never trusted metadata. -/

/-- `add a b` with a COMPUTED literal zero (`alsLitOpt`, which producer and
    checker both re-run) preserves the value against the real `eval`. -/
theorem quelle_add_lit_null {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) (σ₀ σ : World D) (ρ : Env D Γ)
    (h : alsLitOpt b = some 0) :
    (eval σ₀ (.add a b) σ ρ).n = (eval σ₀ a σ ρ).n := by
  have hb : (eval σ₀ b σ ρ).n = 0 := eval_alsLit b 0 σ₀ σ ρ h
  have hval : (eval σ₀ (.add a b) σ ρ).n =
      (eval σ₀ a σ ρ).n + (eval σ₀ b σ ρ).n := rfl
  rw [hval, hb, Int.add_zero]

/-- Joint witness: the source fact on literals, the table-writing contract,
    and the memory-changing run of the witness program, together. -/
theorem quelle_add_lit_null_zeuge :
    (eval (σ₀ := wWorld0)
        (@Expr.add wD [] [] 3 3 0 0 (@Expr.lit wD [] [] 3)
          (@Expr.lit wD [] [] 0))
        wWorld0 Env.nil).n =
      (eval (σ₀ := wWorld0) (@Expr.lit wD [] [] 3) wWorld0 Env.nil).n ∧
    wV.schreibt () = true ∧
    (match execBlock wO 5 wR wRest wWorld0 Env.nil with
      | .ok σ' _ => (σ'.slots () 0 ()).n = 5
      | _ => False) := by
  refine ⟨quelle_add_lit_null _ _ _ _ _ rfl, wit_schreibt, wit_step⟩

/-! ## 8. Invariant scope: an entry fact dies at the writer. -/

/-- The example invariant: the witness slot still reads zero. -/
def invBeispiel : Expr wD [] [] .bool :=
  .eq (Expr.slot (D := wD) (Γ := []) (Λ := []) () ()
    wIdx (fun _ hw => False.elim (List.not_mem_nil hw))) (.lit 0)

/-- Entry holds: the slot reads zero at the start. -/
theorem inv_am_eintritt :
    wahr? (eval wWorld0 invBeispiel wWorld0 Env.nil) = true := by
  decide

/-- Site check: at any world whose slot reads five the invariant is false,
    so an entry fact is unusable there without a fresh site guarantee. -/
theorem inv_standort_falsch (σ' : World wD)
    (hslot : (σ'.slots () 0 ()).n = 5) :
    wahr? (eval σ' invBeispiel σ' Env.nil) = false := by
  have hidx : (eval σ' wIdx σ' Env.nil).n = 0 := rfl
  simp [invBeispiel, eval, wahr?, hidx, hslot]

/-- The writer kills the entry fact on the actual witness run: after the
    table-writing block the invariant is false, hence `waehleInv` with no
    held stability refuses (`none`). -/
theorem inv_nach_lauf_falsch :
    match execBlock wO 5 wR wRest wWorld0 Env.nil with
    | .ok σ' _ => wahr? (eval σ' invBeispiel σ' Env.nil) = false
    | _ => True := by
  cases h : execBlock wO 5 wR wRest wWorld0 Env.nil with
  | ok σ' x =>
    have hs : (σ'.slots () 0 ()).n = 5 := by
      have hw := wit_step
      rw [h] at hw
      exact hw
    exact inv_standort_falsch σ' hs
  | zurueck σ' v => trivial
  | grund σ' r => trivial
  | leave h' σ' ρ => trivial
  | next h' σ' ρ => trivial
  | logik e => trivial
  | hardware e => trivial

/-- No held stability, no elimination: the ungated choice refuses. -/
theorem waehleInv_verweigert (s : InvScope) :
    waehleInv s false = none := by
  cases s <;> rfl

/-- Held stability eliminates, at every scope tag. -/
theorem waehleInv_erlaubt (s : InvScope) :
    waehleInv s true = some [] := by
  cases s <;> rfl

/- CUTS (what is proved above vs. what stays open):
   PROVED: register-only selection functions (`waehleNull`, `waehleAddNull`,
   `waehleSelbstMov`, `wahlOk`, `waehleInv`) over the pilot `Befehl`; value
   facts (`xor_selbst_null`, `add_null_ident`); real byte comparison
   (`null_laengen`: 10 vs 3, pinned `pin_xor_rax`/`pin_mov0_rax`, decode round
   trips `runde_null_rax`); executed-step value observations
   (`schritt_null_mov`, `schritt_null_xor`, `schritt_null_gleich`,
   `schritt_addNull_wert`, `schritt_selbstMov_ident`); flag cost with a
   diverging following branch (`xor_selbst_zf`, `zweig_weicht_ab`) and the
   checker verdicts (`wahlOk_*`, `waehleNull_*`, `waehleAddNull_*`,
   `waehleSelbstMov_*`); the source connection through a COMPUTED literal
   zero (`quelle_add_lit_null` with joint table-writing, memory-changing
   witness `quelle_add_lit_null_zeuge`); the entry-vs-site discipline
   (`inv_am_eintritt`, `inv_standort_falsch`, `inv_nach_lauf_falsch` on the
   actual witness run, `waehleInv_*` refusal without held stability).
   OPEN, explicitly not claimed: multiply/shift strength at byte level (the
   pilot has no `shl`/`imul` forms; the value facts stay source-level in
   `StaerkeReduktion`); discharge of `InvScope` tags (needs the goal legs at
   the use site); memory aliasing beyond register equality (no load/store
   rule here); cost/budget transfer (shorter bytes change timing, unmodelled);
   call-log (`Folge`) preservation; interleaving transfer under concurrency
   (sequential `schritt`/`lauf` only); atomics, MMIO, narrow widths;
   hardware correspondence (decoder/step are checked models, not silicon
   proof); any claim beyond the 14 pilot forms.
-/

#print axioms xor_selbst_null
#print axioms add_null_ident
#print axioms null_laengen
#print axioms runde_null_rax
#print axioms schritt_null_gleich
#print axioms xor_selbst_zf
#print axioms zweig_weicht_ab
#print axioms wahlOk_verweigert_xor_le
#print axioms schritt_addNull_wert
#print axioms schritt_selbstMov_ident
#print axioms quelle_add_lit_null
#print axioms quelle_add_lit_null_zeuge
#print axioms inv_am_eintritt
#print axioms inv_standort_falsch
#print axioms inv_nach_lauf_falsch
#print axioms waehleInv_verweigert

end Gabbro.Grammatik.X86.Anweisungswahl
