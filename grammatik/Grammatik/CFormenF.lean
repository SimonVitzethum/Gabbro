/-
  File:      Grammatik/CFormenF.lean
  Subject:   T4, floating point: the C float forms the emitter produces and
             their correspondence to Gabbro's float blocks, under the named
             assumption `gleitkomma_ieee`.

  THE EMITTED C (emit.rs, read 2026-09-14; one run of `gabbro emit` on
  `beispiele/26-gleitkomma.gab`):
    * `f64 -> double`, `f32 -> float`; a float local is `double c = …;`;
    * arithmetic `a + b`, `a - b`, `a * b`, `a / b` bare, operands of ONE
      float type (mixed `float`/`double` is refused, `CForm doubleTyp`);
    * comparisons `a < b`, `a <= b`, `a > b`, `a >= b` bare;
    * literals as the shortest round-trip decimal of the `f64` bits
      (`gleitkommatext`), with `f` where the node computes in `float`;
    * `narrow x to lo .. hi else { … }` as
      `if (!(x >= LO && x <= HI)) { … }` (the check STAYS, W6 inverted);
    * `narrow x to finite else { … }` as `if (!isfinite(x)) { … }`;
    * the unit prelude `KOPF_GLEITKOMMA` (`#include <float.h>`,
      `_Static_assert(FLT_EVAL_METHOD == 0, …)`), `#include <math.h>`.

  THE C MODEL (CFormen.lean): a float value is its bit pattern
  (`fEin`/`fAus`), the operators compute C11 Annex F -- the exact result
  rounded once to nearest-even -- by the kernel-computable model of
  `Gleitkomma.lean`: `CX.fbin`, `CX.fcmp`, `CX.fvon` (integer to float),
  `CX.fin` (`isfinite`). A float local is a bit container of type
  `uint64_t` for the model's conversion at `=` (floats are never converted
  to integers by an emitted `=`; CUTS).

  THE NAMED ASSUMPTION (`dokumente/GLEITKOMMA.md` section 4): the float
  unit of the built binary computes what Annex F prescribes on binary32
  and binary64 -- `gleitkomma_ieee`, a premise over a `FloatUnit`, with
  `annexF` its witness (the model itself). It is what the seven machine
  facts of GLEITKOMMA.md (RNE, SSE2, no contraction, `FLT_EVAL_METHOD ==
  0`, no fast-math, no FTZ/DAZ, a stable mode) jointly promise.

  THE FORMS (Gabbro side: Syntax.lean «F»; the model computes `Ty.fl`
  in binary64, so the correspondence is for `double`):
    F1  `double c = a op b;`             Block.gleit       gsem_gleit
    F2  `double c = LIT;`                Block.gleitLit    gsem_gleitLit
    F3  `double c = n;` (int to float)   Block.gleitVon    gsem_gleitVon
    F4  `a < b` / `a <= b` / `>` / `>=`  Expr.fllt/flle    ecorr_fllt/_flle/_flgt/_flge
    F5  `if (!(x >= LO && x <= HI)) {…}` Block.gleitNarrow gsem_gleitNarrow + narrowCondF_ge_le
    F6  `if (!isfinite(x)) {…}`          Block.gleitNarrow gsem_gleitNarrow + narrowCondF_endlich
    F7  a float local, `return x;`       (pass (i)/(G))    ecorr_var, scorr_ret (ValCorr .fl)
-/
import Grammatik.CFormenR

namespace Gabbro.Grammatik

open Gleitkomma (f64 f32 wf)

variable {D : Deklaration}

/-! ## 1. Values: bits and back -/

theorem fEin_toNat (F : Gleitkomma.Format) (x : Gleitkomma.GBits F) :
    (fEin F x).toNat = Gleitkomma.zuBits F x := by
  unfold fEin; exact Int.toNat_natCast _

theorem fAus_fEin (F : Gleitkomma.Format) (hF : F.dicht) (x : Gleitkomma.GBits F) (hw : wf F x) :
    fAus F (fEin F x) = x := by
  unfold fAus; rw [fEin_toNat]; exact Gleitkomma.ausBits_zuBits F hF x hw

theorem cGleitOp_f64 (op : GleitOp) (x y : GFloat) : cGleitOp op f64 x y = gleitRechne op x y := by
  cases op <;> rfl

theorem gleitRechne_wf (op : GleitOp) (x y : GFloat) (hx : wf f64 x) (hy : wf f64 y) :
    wf f64 (gleitRechne op x y) := by
  cases op
  · exact Gleitkomma.add_wf f64 Gleitkomma.f64_p x y hx hy
  · exact Gleitkomma.sub_wf f64 Gleitkomma.f64_p x y hx hy
  · exact Gleitkomma.mul_wf f64 Gleitkomma.f64_p x y hx hy
  · exact Gleitkomma.div_wf f64 Gleitkomma.f64_p x y hx hy

theorem bruch_wf (q : Int × Int) : wf f64 (bruch q) := Gleitkomma.rundeBruch_wf f64 Gleitkomma.f64_p _

theorem gleitAusInt_wf (z : Int) : wf f64 (gleitAusInt z) :=
  Gleitkomma.ofInt_wf f64 Gleitkomma.f64_p z

/-- C's `a op b` on the bits of two model values is the bits of the model's
    result. -/
theorem cFloatBin_ein (op : GleitOp) (x y : GFloat) (hx : wf f64 x) (hy : wf f64 y) :
    cFloatBin op f64 (fEin f64 x) (fEin f64 y) = fEin f64 (gleitRechne op x y) := by
  unfold cFloatBin
  rw [fAus_fEin f64 Gleitkomma.f64_dicht x hx, fAus_fEin f64 Gleitkomma.f64_dicht y hy,
    cGleitOp_f64]

theorem cFloatCmp_lt_ein (x y : GFloat) (hx : wf f64 x) (hy : wf f64 y) :
    cFloatCmp .lt f64 (fEin f64 x) (fEin f64 y) = gleitLt x y := by
  unfold cFloatCmp
  rw [fAus_fEin f64 Gleitkomma.f64_dicht x hx, fAus_fEin f64 Gleitkomma.f64_dicht y hy]; rfl

theorem cFloatCmp_le_ein (x y : GFloat) (hx : wf f64 x) (hy : wf f64 y) :
    cFloatCmp .le f64 (fEin f64 x) (fEin f64 y) = gleitLe x y := by
  unfold cFloatCmp
  rw [fAus_fEin f64 Gleitkomma.f64_dicht x hx, fAus_fEin f64 Gleitkomma.f64_dicht y hy]; rfl

theorem cFloatCmp_gt_ein (x y : GFloat) (hx : wf f64 x) (hy : wf f64 y) :
    cFloatCmp .gt f64 (fEin f64 x) (fEin f64 y) = gleitLt y x := by
  unfold cFloatCmp
  rw [fAus_fEin f64 Gleitkomma.f64_dicht x hx, fAus_fEin f64 Gleitkomma.f64_dicht y hy]; rfl

theorem cFloatCmp_ge_ein (x y : GFloat) (hx : wf f64 x) (hy : wf f64 y) :
    cFloatCmp .ge f64 (fEin f64 x) (fEin f64 y) = gleitLe y x := by
  unfold cFloatCmp
  rw [fAus_fEin f64 Gleitkomma.f64_dicht x hx, fAus_fEin f64 Gleitkomma.f64_dicht y hy]; rfl

theorem cFloatVonInt_ein (z : Int) : cFloatVonInt f64 z = fEin f64 (gleitAusInt z) := rfl

/-- `gleitEndlich` is the class test (the class generalised BEFORE the two
    matchers meet, so the kernel never evaluates a stuck float). -/
theorem gleitEndlich_endlichK (x : GFloat) :
    gleitEndlich x = Gleitkomma.endlichK (Gleitkomma.klasse f64 x) := by
  unfold gleitEndlich Gleitkomma.endlichK
  generalize Gleitkomma.klasse f64 x = k
  cases k <;> rfl

theorem cFloatEndlich_ein (x : GFloat) (hx : wf f64 x) :
    cFloatEndlich f64 (fEin f64 x) = gleitEndlich x := by
  have e1 : cFloatEndlich f64 (fEin f64 x) =
      Gleitkomma.endlichK (Gleitkomma.klasse f64 (fAus f64 (fEin f64 x))) := rfl
  rw [e1, gleitEndlich_endlichK, fAus_fEin f64 Gleitkomma.f64_dicht x hx]

/-- The bits of a model value fit the `uint64_t` container. -/
theorem fEin_range (x : GFloat) (hx : wf f64 x) :
    CIT.u64.lo ≤ fEin f64 x ∧ fEin f64 x ≤ CIT.u64.hi := by
  have h := Gleitkomma.zuBits_lt f64 Gleitkomma.f64_dicht x hx
  have e : f64.ebits + f64.fracBits + 1 = 64 := by decide
  rw [e] at h
  have hlo : CIT.u64.lo = 0 := rfl
  have hhi : CIT.u64.hi = 2 ^ 64 - 1 := rfl
  rw [hlo, hhi]
  unfold fEin
  constructor
  · exact Int.natCast_nonneg _
  · have : ((Gleitkomma.zuBits f64 x : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by exact_mod_cast h
    omega

/-- The conversion at `=`, generic (no literal for the kernel to unfold). -/
theorem convV_int_of_conv (s : Bool) (w : CWidth) (v : Int) (h : conv ⟨s, w⟩ v = some v) :
    convV (.int s w) (.int v) = some (.int v) := by
  simp only [convV, h]

/-- The model's conversion at `=` into the float container keeps the bits. -/
theorem convV_fEin (x : GFloat) (hx : wf f64 x) :
    convV (.int false .w64) (.int (fEin f64 x)) = some (.int (fEin f64 x)) :=
  convV_int_of_conv false .w64 _ (conv_id (fEin_range x hx))

/-- A range check passes exactly for a finite value between the rounded
    bounds; its result is the value itself. -/
theorem gleitPasst_x {lo hi : Int × Int} {y : GFloat} {v : Gleit lo hi}
    (h : gleitPasst lo hi y = some v) : v.x = y := by
  unfold gleitPasst at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem gleitPasst_isSome {lo hi : Int × Int} (v : Gleit lo hi) (lo' hi' : Int × Int) :
    (gleitPasst lo' hi' v.x).isSome = (gleitLe (bruch lo') v.x && gleitLe v.x (bruch hi')) := by
  unfold gleitPasst
  by_cases h : gleitEndlich v.x = true ∧ gleitLe (bruch lo') v.x = true ∧ gleitLe v.x (bruch hi') = true
  · rw [dif_pos h, h.2.1, h.2.2]; rfl
  · rw [dif_neg h]
    have he := v.endlich
    cases h1 : gleitLe (bruch lo') v.x <;> cases h2 : gleitLe v.x (bruch hi') <;> simp_all

/-- A value passes the check of its own range. -/
theorem gleitPasst_selbst {lo hi : Int × Int} (v : Gleit lo hi) : gleitPasst lo hi v.x = some v := by
  unfold gleitPasst
  rw [dif_pos ⟨v.endlich, v.lo_le, v.le_hi⟩]

/-! ## 2. Evaluation rules of the float forms -/

theorem ev_fbin {L : CLayout} {orc : DevOrc} {fr : Nat} {op : GleitOp} {F : Gleitkomma.Format}
    {l r : CX} {st st1 st2 : CSt} {ρ : CLok} {a b : Int}
    (hl : ev L orc fr l st ρ = some (.int a, st1)) (hr : ev L orc fr r st1 ρ = some (.int b, st2)) :
    ev L orc fr (.fbin op F l r) st ρ = some (.int (cFloatBin op F a b), st2) := by
  simp only [ev, hl, hr]

theorem ev_fcmp {L : CLayout} {orc : DevOrc} {fr : Nat} {op : CCmp} {F : Gleitkomma.Format}
    {l r : CX} {st st1 st2 : CSt} {ρ : CLok} {a b : Int}
    (hl : ev L orc fr l st ρ = some (.int a, st1)) (hr : ev L orc fr r st1 ρ = some (.int b, st2)) :
    ev L orc fr (.fcmp op F l r) st ρ = some (.int (b2i (cFloatCmp op F a b)), st2) := by
  simp only [ev, hl, hr]

theorem ev_fvon {L : CLayout} {orc : DevOrc} {fr : Nat} {F : Gleitkomma.Format} {t : CIT}
    {e : CX} {st st1 : CSt} {ρ : CLok} {a : Int}
    (he : ev L orc fr e st ρ = some (.int a, st1)) (hc : conv t a = some a) :
    ev L orc fr (.fvon F t e) st ρ = some (.int (cFloatVonInt F a), st1) := by
  simp only [ev, he, hc]

theorem ev_fin {L : CLayout} {orc : DevOrc} {fr : Nat} {F : Gleitkomma.Format}
    {e : CX} {st st1 : CSt} {ρ : CLok} {a : Int}
    (he : ev L orc fr e st ρ = some (.int a, st1)) :
    ev L orc fr (.fin F e) st ρ = some (.int (b2i (cFloatEndlich F a)), st1) := by
  simp only [ev, he]

/-! ## 3. The named assumption: the machine's float unit is Annex F -/

/-- What the float instructions of a built binary compute, on bit
    patterns: the four operators, the six comparisons, integer to float,
    and the class test behind `isfinite`. -/
structure FloatUnit where
  bin : GleitOp → Gleitkomma.Format → Int → Int → Int
  cmp : CCmp → Gleitkomma.Format → Int → Int → Bool
  vonInt : Gleitkomma.Format → Int → Int
  endlich : Gleitkomma.Format → Int → Bool

/-- The unit C11 Annex F describes: the model (`CFormen.lean`'s `ev`). -/
def annexF : FloatUnit := ⟨cFloatBin, cFloatCmp, cFloatVonInt, cFloatEndlich⟩

/-- **THE NAMED ASSUMPTION `gleitkomma_ieee`** (dokumente/GLEITKOMMA.md
    section 4): on binary32 and binary64 the float unit `u` of the built
    binary computes exactly what Annex F prescribes -- every `+ - * /` and
    every integer conversion the exact result rounded once to nearest-even,
    every comparison IEEE's (NaN unordered, signed zeros equal), `isfinite`
    the class test. Items 1-7 of GLEITKOMMA.md (RNE mode, SSE2, no
    contraction, `FLT_EVAL_METHOD == 0`, no fast-math, no FTZ/DAZ, a stable
    mode) are what make a C compiler's float code satisfy it. -/
def gleitkomma_ieee (u : FloatUnit) : Prop :=
  ∀ F, (F = f32 ∨ F = f64) →
    (∀ op a b, u.bin op F a b = cFloatBin op F a b) ∧
    (∀ op a b, u.cmp op F a b = cFloatCmp op F a b) ∧
    (∀ z, u.vonInt F z = cFloatVonInt F z) ∧
    (∀ a, u.endlich F a = cFloatEndlich F a)

/-- The assumption is satisfiable: Annex F's own unit meets it. -/
theorem gleitkomma_ieee_annexF : gleitkomma_ieee annexF :=
  fun _ _ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- THE BRIDGE: under the assumption, what the machine's unit computes on
    the bits of two model values is the bits of the model's (Gabbro's)
    result -- the C semantics' `ev (.fbin …)` is the machine's. -/
theorem maschine_fbin (u : FloatUnit) (hu : gleitkomma_ieee u) (op : GleitOp) (x y : GFloat)
    (hx : wf f64 x) (hy : wf f64 y) :
    u.bin op f64 (fEin f64 x) (fEin f64 y) = fEin f64 (gleitRechne op x y) := by
  rw [(hu f64 (Or.inr rfl)).1, cFloatBin_ein op x y hx hy]

theorem maschine_fcmp_le (u : FloatUnit) (hu : gleitkomma_ieee u) (x y : GFloat)
    (hx : wf f64 x) (hy : wf f64 y) :
    u.cmp .le f64 (fEin f64 x) (fEin f64 y) = gleitLe x y := by
  rw [(hu f64 (Or.inr rfl)).2.1, cFloatCmp_le_ein x y hx hy]

theorem maschine_fcmp_lt (u : FloatUnit) (hu : gleitkomma_ieee u) (x y : GFloat)
    (hx : wf f64 x) (hy : wf f64 y) :
    u.cmp .lt f64 (fEin f64 x) (fEin f64 y) = gleitLt x y := by
  rw [(hu f64 (Or.inr rfl)).2.1, cFloatCmp_lt_ein x y hx hy]

theorem maschine_fvon (u : FloatUnit) (hu : gleitkomma_ieee u) (z : Int) :
    u.vonInt f64 z = fEin f64 (gleitAusInt z) := by
  rw [(hu f64 (Or.inr rfl)).2.2.1]; rfl

theorem maschine_fin (u : FloatUnit) (hu : gleitkomma_ieee u) (x : GFloat) (hx : wf f64 x) :
    u.endlich f64 (fEin f64 x) = gleitEndlich x := by
  rw [(hu f64 (Or.inr rfl)).2.2.2, cFloatEndlich_ein x hx]

/-! ## 4. Expressions (pass (i)): a float local and the comparisons -/

section Ausdruck

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- Running a corresponding float expression: its bits, a well-formed
    value, and a state still related. -/
theorem ExprCorr.runF {lo hi : Int × Int} {c : CX} {e : Expr D Γ Λ (.fl lo hi)}
    (h : ExprCorr X K c e) {σ : World D} {st : CSt} {ρG : Env D Γ} {ρC : CLok}
    (hc : corrW X.EL σ st) (he : EnvRel X.EL K ρG ρC) :
    ∃ st', ev X.EL.lay X.orc X.fr c st ρC = some (.int (fEin f64 (eval σ e σ ρG).x), st') ∧
      wf f64 (eval σ e σ ρG).x ∧ corrW X.EL σ st' := by
  obtain ⟨v, st', h1, h2, h3⟩ := h.run X K hc he
  have h2' : v = .int (fEin f64 (eval σ e σ ρG).x) ∧ wf f64 (eval σ e σ ρG).x := h2
  obtain ⟨e2, hw⟩ := h2'
  subst e2
  exact ⟨st', h1, hw, h3⟩

/-- The float comparison scheme: both operands correspond, the C
    comparison on their bits is the Gabbro truth value. -/
theorem ecorr_fcmp (op : CCmp) {l1 h1 l2 h2 : Int × Int} {ca cb : CX}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)} {e : Expr D Γ Λ .bool}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b)
    (hop : ∀ (σ : World D) (ρG : Env D Γ), wf f64 (eval σ a σ ρG).x → wf f64 (eval σ b σ ρG).x →
      cFloatCmp op f64 (fEin f64 (eval σ a σ ρG).x) (fEin f64 (eval σ b σ ρG).x) =
        wahr? (eval σ e σ ρG)) :
    ExprCorr X K (.fcmp op f64 ca cb) e := by
  intro σ st ρG ρC hc he
  obtain ⟨st1, h1', hwa, hc1⟩ := ha.runF X K hc he
  obtain ⟨st2, h2', hwb, -⟩ := hb.runF X K hc1 he
  refine ⟨.int (b2i (wahr? (eval σ e σ ρG))), st2, ?_, ?_⟩
  · rw [ev_fcmp h1' h2', hop σ ρG hwa hwb]
  · show CVal.int (b2i (wahr? (eval σ e σ ρG))) = .int (encW .bool (eval σ e σ ρG))
    rfl

/-- F4. `a < b` on doubles. -/
theorem ecorr_fllt {l1 h1 l2 h2 : Int × Int} {ca cb : CX}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) :
    ExprCorr X K (.fcmp .lt f64 ca cb) (.fllt a b) :=
  ecorr_fcmp X K .lt ha hb (fun σ ρG hx hy => cFloatCmp_lt_ein _ _ hx hy)

/-- F4. `a <= b` on doubles. -/
theorem ecorr_flle {l1 h1 l2 h2 : Int × Int} {ca cb : CX}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) :
    ExprCorr X K (.fcmp .le f64 ca cb) (.flle a b) :=
  ecorr_fcmp X K .le ha hb (fun σ ρG hx hy => cFloatCmp_le_ein _ _ hx hy)

/-- F4. `a > b` on doubles is Gabbro's `b < a`. -/
theorem ecorr_flgt {l1 h1 l2 h2 : Int × Int} {ca cb : CX}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) :
    ExprCorr X K (.fcmp .gt f64 ca cb) (.fllt b a) :=
  ecorr_fcmp X K .gt ha hb (fun σ ρG hx hy => cFloatCmp_gt_ein _ _ hx hy)

/-- F4. `a >= b` on doubles is Gabbro's `b <= a`. -/
theorem ecorr_flge {l1 h1 l2 h2 : Int × Int} {ca cb : CX}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) :
    ExprCorr X K (.fcmp .ge f64 ca cb) (.flle b a) :=
  ecorr_fcmp X K .ge ha hb (fun σ ρG hx hy => cFloatCmp_ge_ein _ _ hx hy)

end Ausdruck

/-! ## 5. The float blocks (with ghosts and a channel) -/

section Bloecke

variable (X : TVCtx D) (m : Nat) (G : GCtx) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
  {l : Bool}

/-- A float expression under ghosts: its cell-read form evaluates to its
    bits. -/
theorem ExprCorr.runFG {Λ : List (Res D)} {lo hi : Int × Int} {c : CX} {e : Expr D Γ Λ (.fl lo hi)}
    (h : ExprCorr X K c e) {σ : World D} {st : CSt} {ρG : Env D Γ} {ρC : CLok}
    (hc : corrW X.EL σ st) (hrel : EnvRelG X G K ρG ρC st) :
    ∃ st', ev X.EL.lay X.orc X.fr (c.zs G.gs) st ρC =
        some (.int (fEin f64 (eval σ e σ ρG).x), st') ∧
      wf f64 (eval σ e σ ρG).x ∧ corrW X.EL σ st' ∧ SameML st st' := by
  obtain ⟨st1, h1, hw, hc1⟩ := h.runF X K hc hrel.1
  have hs1 := ev_same X.EL.lay X.orc X.fr c st _ _ st1 h1
  refine ⟨st1, ?_, hw, hc1, hs1⟩
  rw [ev_zs G.gs c st st ρC (SameML.refl _)]; exact h1

/-- The same at a later state with the memory of the first (the second
    operand of a binary form). -/
theorem ExprCorr.runFG' {Λ : List (Res D)} {lo hi : Int × Int} {c : CX} {e : Expr D Γ Λ (.fl lo hi)}
    (h : ExprCorr X K c e) {σ : World D} {st st1 : CSt} {ρG : Env D Γ} {ρC : CLok}
    (hc : corrW X.EL σ st) (hrel : EnvRelG X G K ρG ρC st) (hs : SameML st st1) :
    ∃ st', ev X.EL.lay X.orc X.fr (c.zs G.gs) st1 ρC =
        some (.int (fEin f64 (eval σ e σ ρG).x), st') ∧
      wf f64 (eval σ e σ ρG).x ∧ SameML st1 st' := by
  obtain ⟨st2, h2, hw, -, hs2⟩ := h.runFG X G K (corrW_same hc hs) (envRelG_same hs hrel)
  exact ⟨st2, h2, hw, hs2⟩

/-- F1. `double c = a op b; rest` against `Block.gleit op a b lo hi rest`:
    C computes the bits of Gabbro's result (Annex F is the model); where
    Gabbro's range check fails the outcome is `logik bereich` (was
    `hardware ieee` until 2026-09-15, verdict F1): the user's obligation
    excludes it, and a failure outcome carries no correspondence duty. -/
theorem gsem_gleit {Λ Λ' : List (Res D)} (op : GleitOp) {l1 h1 l2 h2 lo hi : Int × Int}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'} {ca cb : CX} {x : Nat} {cr : CS}
    (hK : K.okB = true) (hf : K.freshB x = true) (hg : x ∉ geister G.gs)
    (hkx : ∀ κ, G.kan = some κ → x ≠ κ.wx ∧ x ≠ κ.gx)
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b)
    (hr : BlockSemG X m G (K.push (.fl lo hi) x) rest cr) :
    BlockSemG X m G K (Block.gleit op a b lo hi rest)
      (.seq (.set x (.int false .w64) ((CX.fbin op f64 ca cb).zs G.gs)) cr) := by
  intro σ st ρG ρC hcw hrel hnf
  have hc' : corrW X.EL (σ.lese Λ (a.orte ++ b.orte)) st := (corrW_lese _ _ _ _ _).mpr hcw
  obtain ⟨st1, h1, hwa, hc1, hs1⟩ := ha.runFG X G K hc' hrel
  obtain ⟨st2, h2, hwb, hs2⟩ := hb.runFG' X G K hc' hrel hs1
  have hs12 := hs1.trans hs2
  have hev : ev X.EL.lay X.orc X.fr ((CX.fbin op f64 ca cb).zs G.gs) st ρC =
      some (.int (fEin f64 (gleitRechne op
        (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρG).x
        (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρG).x)), st2) := by
    show ev X.EL.lay X.orc X.fr (.fbin op f64 (ca.zs G.gs) (cb.zs G.gs)) st ρC = _
    rw [ev_fbin h1 h2, cFloatBin_ein op _ _ hwa hwb]
  have hex : execBlock X.O X.passes X.R (Block.gleit op a b lo hi rest) σ ρG =
      match gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρG).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρG).x) with
      | some v => (execBlock X.O X.passes X.R rest (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρG)).schrumpf
      | none => .logik .bereich := rfl
  rw [hex] at hnf ⊢
  cases hgp : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρG).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρG).x) with
  | none => rw [hgp] at hnf; exact Bool.noConfusion hnf
  | some v =>
      rw [hgp] at hnf
      simp only [] at hnf ⊢
      rw [istFehler_schrumpf] at hnf
      have hvx := gleitPasst_x hgp
      have hwv : wf f64 v.x := by rw [hvx]; exact gleitRechne_wf op _ _ hwa hwb
      have hvc : ValCorr X.EL (.fl lo hi) v (.int (fEin f64 v.x)) := ⟨rfl, hwv⟩
      rw [← hvx] at hev
      have hr1 := envRelG_push hK hf hg hkx (envRelG_same hs12 hrel) (τ := .fl lo hi) v _ hvc
      obtain ⟨o, hx2, hO⟩ := hr _ st2 _ _ (corrW_same hc' hs12) hr1 hnf
      exact ⟨o, Exec.seqN (Exec.set hev (convV_fEin _ hwv)) hx2, stOutG_schrumpf X m G _ o hO⟩

/-- F2. `double c = LIT; rest` against `Block.gleitLit q lo hi rest`: the
    C literal denotes the correctly rounded value of `q` (Annex F's
    decimal conversion; the emitter prints the shortest round-trip text of
    exactly those bits). -/
theorem gsem_gleitLit {Λ Λ' : List (Res D)} (q : Int × Int) {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'} {x : Nat} {cr : CS}
    (hK : K.okB = true) (hf : K.freshB x = true) (hg : x ∉ geister G.gs)
    (hkx : ∀ κ, G.kan = some κ → x ≠ κ.wx ∧ x ≠ κ.gx)
    (hr : BlockSemG X m G (K.push (.fl lo hi) x) rest cr) :
    BlockSemG X m G K (Block.gleitLit q lo hi rest)
      (.seq (.set x (.int false .w64) (.lit (fEin f64 (bruch q)))) cr) := by
  intro σ st ρG ρC hcw hrel hnf
  have hex : execBlock X.O X.passes X.R (Block.gleitLit q lo hi rest) σ ρG =
      match gleitPasst lo hi (bruch q) with
      | some v => (execBlock X.O X.passes X.R rest σ (.cons v ρG)).schrumpf
      | none => .logik .bereich := rfl
  rw [hex] at hnf ⊢
  cases hgp : gleitPasst lo hi (bruch q) with
  | none => rw [hgp] at hnf; exact Bool.noConfusion hnf
  | some v =>
      rw [hgp] at hnf
      simp only [] at hnf ⊢
      rw [istFehler_schrumpf] at hnf
      have hvx := gleitPasst_x hgp
      have hwv : wf f64 v.x := by rw [hvx]; exact bruch_wf q
      have hvc : ValCorr X.EL (.fl lo hi) v (.int (fEin f64 v.x)) := ⟨rfl, hwv⟩
      have hev : ev X.EL.lay X.orc X.fr (.lit (fEin f64 (bruch q))) st ρC =
          some (.int (fEin f64 v.x), st) := by rw [hvx]; rfl
      have hr1 := envRelG_push hK hf hg hkx hrel (τ := .fl lo hi) v _ hvc
      obtain ⟨o, hx2, hO⟩ := hr _ st _ _ hcw hr1 hnf
      exact ⟨o, Exec.seqN (Exec.set hev (convV_fEin _ hwv)) hx2, stOutG_schrumpf X m G _ o hO⟩

/-- F3. `double c = n; rest` (the integer converted, 6.3.1.4p2) against
    `Block.gleitVon e lo hi rest`; `t` is the integer's C type. -/
theorem gsem_gleitVon {Λ Λ' : List (Res D)} (t : CIT) {l1 h1 : Int} {lo hi : Int × Int}
    {e : Expr D Γ Λ (.int l1 h1)} {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'} {ce : CX} {x : Nat}
    {cr : CS} (hK : K.okB = true) (hf : K.freshB x = true) (hg : x ∉ geister G.gs)
    (hkx : ∀ κ, G.kan = some κ → x ≠ κ.wx ∧ x ≠ κ.gx)
    (he : ExprCorr X K ce e) (ht : t.holds l1 h1)
    (hr : BlockSemG X m G (K.push (.fl lo hi) x) rest cr) :
    BlockSemG X m G K (Block.gleitVon e lo hi rest)
      (.seq (.set x (.int false .w64) ((CX.fvon f64 t ce).zs G.gs)) cr) := by
  intro σ st ρG ρC hcw hrel hnf
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hcw
  obtain ⟨st1, h1, hc1⟩ := he.runI X K hc' hrel.1
  have hs1 := ev_same X.EL.lay X.orc X.fr ce st _ _ st1 h1
  have h1' : ev X.EL.lay X.orc X.fr (ce.zs G.gs) st ρC =
      some (.int (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n, st1) := by
    rw [ev_zs G.gs ce st st ρC (SameML.refl _)]; exact h1
  have r1 := (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).lo_le
  have r2 := (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).le_hi
  have hcv : conv t (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n =
      some (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n :=
    conv_id ⟨by have := ht.1; omega, by have := ht.2; omega⟩
  have hex : execBlock X.O X.passes X.R (Block.gleitVon e lo hi rest) σ ρG =
      match gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n) with
      | some v => (execBlock X.O X.passes X.R rest (σ.lese Λ e.orte) (.cons v ρG)).schrumpf
      | none => .logik .bereich := rfl
  rw [hex] at hnf ⊢
  cases hgp : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).n) with
  | none => rw [hgp] at hnf; exact Bool.noConfusion hnf
  | some v =>
      rw [hgp] at hnf
      simp only [] at hnf ⊢
      rw [istFehler_schrumpf] at hnf
      have hvx := gleitPasst_x hgp
      have hwv : wf f64 v.x := by rw [hvx]; exact gleitAusInt_wf _
      have hvc : ValCorr X.EL (.fl lo hi) v (.int (fEin f64 v.x)) := ⟨rfl, hwv⟩
      have hev : ev X.EL.lay X.orc X.fr ((CX.fvon f64 t ce).zs G.gs) st ρC =
          some (.int (fEin f64 v.x), st1) := by
        show ev X.EL.lay X.orc X.fr (.fvon f64 t (ce.zs G.gs)) st ρC = _
        rw [ev_fvon h1' hcv, hvx]; rfl
      have hr1 := envRelG_push hK hf hg hkx (envRelG_same hs1 hrel) (τ := .fl lo hi) v _ hvc
      obtain ⟨o, hx2, hO⟩ := hr _ st1 _ _ hc1 hr1 hnf
      exact ⟨o, Exec.seqN (Exec.set hev (convV_fEin _ hwv)) hx2, stOutG_schrumpf X m G _ o hO⟩

/-- The emitted float `narrow` check's condition: from related states it
    says whether the value passes the target range (`gleitPasst`). -/
def NarrowCondF {Λ : List (Res D)} {lo hi : Int × Int} (cc : CX) (e : Expr D Γ Λ (.fl lo hi))
    (lo' hi' : Int × Int) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRelG X G K ρG ρC st →
    ∃ st', ev X.EL.lay X.orc X.fr cc st ρC =
        some (.int (b2i (gleitPasst lo' hi' (eval σ e σ ρG).x).isSome), st') ∧
      SameML st st'

/-- F5. The emitted `x >= LO && x <= HI`: the literals are the correctly
    rounded bounds, the comparisons Annex F's. -/
theorem narrowCondF_ge_le {Λ : List (Res D)} {lo hi : Int × Int} {ce : CX}
    {e : Expr D Γ Λ (.fl lo hi)} (he : ExprCorr X K ce e) (lo' hi' : Int × Int) :
    NarrowCondF X G K
      (.land (.fcmp .ge f64 (ce.zs G.gs) (.lit (fEin f64 (bruch lo'))))
        (.fcmp .le f64 (ce.zs G.gs) (.lit (fEin f64 (bruch hi'))))) e lo' hi' := by
  intro σ st ρG ρC hc hrel
  obtain ⟨st1, h1, hw, -, hs1⟩ := he.runFG X G K hc hrel
  have hge := ev_fcmp (op := .ge) (F := f64) h1
    (rfl : ev X.EL.lay X.orc X.fr (.lit (fEin f64 (bruch lo'))) st1 ρC = _)
  rw [cFloatCmp_ge_ein _ _ hw (bruch_wf lo')] at hge
  rw [gleitPasst_isSome (show Gleit lo hi from eval σ e σ ρG) lo' hi']
  cases hlo : gleitLe (bruch lo') (eval σ e σ ρG).x with
  | false =>
      rw [hlo] at hge
      refine ⟨st1, ?_, hs1⟩
      rw [ev_land_F hge rfl]; rfl
  | true =>
      rw [hlo] at hge
      obtain ⟨st2, h2, -, hs2⟩ := he.runFG' X G K hc hrel hs1
      have hle := ev_fcmp (op := .le) (F := f64) h2
        (rfl : ev X.EL.lay X.orc X.fr (.lit (fEin f64 (bruch hi'))) st2 ρC = _)
      rw [cFloatCmp_le_ein _ _ hw (bruch_wf hi')] at hle
      refine ⟨st2, ?_, hs1.trans hs2⟩
      rw [ev_land_T hge rfl hle (truth_b2i _)]
      rfl

/-- F6. The emitted `isfinite(x)` for `narrow x to finite`: the model's
    value is finite and in its range, so the check passes on both sides
    (the `else` of `narrow … finite` is dead in C AND in the model -- a
    model float is finite by type). -/
theorem narrowCondF_endlich {Λ : List (Res D)} {lo hi : Int × Int} {ce : CX}
    {e : Expr D Γ Λ (.fl lo hi)} (he : ExprCorr X K ce e) :
    NarrowCondF X G K (.fin f64 (ce.zs G.gs)) e lo hi := by
  intro σ st ρG ρC hc hrel
  obtain ⟨st1, h1, hw, -, hs1⟩ := he.runFG X G K hc hrel
  refine ⟨st1, ?_, hs1⟩
  rw [ev_fin h1, cFloatEndlich_ein _ hw, gleitPasst_selbst (show Gleit lo hi from eval σ e σ ρG),
    (show Gleit lo hi from eval σ e σ ρG).endlich]
  rfl

/-- F5/F6. `narrow e to lo' .. hi' else { sonst } rest` on a float against
    `if (!(cond)) { sonst } rest`: the narrowed value is related through a
    C position `y` of the certificate (`gleitNarrow_bind_var`: for a local,
    its own C local). -/
theorem gsem_gleitNarrow {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int × Int}
    {e : Expr D Γ Λ (.fl lo hi)} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.fl lo' hi' :: Γ) Λ Λ'} {cc : CX} {csonst crest : CS} (y : Nat)
    (hc : NarrowCondF X G K cc e lo' hi')
    (hbind : ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok) (v : Wert D (.fl lo' hi')),
      corrW X.EL σ st → EnvRelG X G K ρG ρC st → v.x = (eval σ e σ ρG).x →
      EnvRelG X G (K.push (.fl lo' hi') y) (.cons v ρG) ρC st)
    (hs : EndSemG X m false G K sonst csonst)
    (hr : BlockSemG X m G (K.push (.fl lo' hi') y) rest crest) :
    BlockSemG X m G K (Block.gleitNarrow e lo' hi' sonst rest)
      (.seq (.ite (.lnot cc) csonst .skip) crest) := by
  intro σ st ρG ρC hcw hrel hnf
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hcw
  obtain ⟨st1, h1, hs1⟩ := hc _ st ρG ρC hc' hrel
  have hc1 := corrW_same hc' hs1
  have hrel1 := envRelG_same hs1 hrel
  have hex : execBlock X.O X.passes X.R (Block.gleitNarrow e lo' hi' sonst rest) σ ρG =
      match gleitPasst lo' hi' (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).x with
      | some v => (execBlock X.O X.passes X.R rest (σ.lese Λ e.orte) (.cons v ρG)).schrumpf
      | none => (execEnd X.O X.passes X.R sonst (σ.lese Λ e.orte) ρG).zuAusgang := rfl
  rw [hex] at hnf ⊢
  cases hgp : gleitPasst lo' hi' (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG).x with
  | some v =>
      rw [hgp] at hnf h1
      simp only [] at hnf ⊢
      rw [istFehler_schrumpf] at hnf
      have hr2 := hbind _ st1 ρG ρC v hc1 hrel1 (gleitPasst_x hgp)
      obtain ⟨o, hx, hO⟩ := hr _ st1 _ ρC hc1 hr2 hnf
      exact ⟨o, Exec.seqN (Exec.iteF (ev_lnot h1 (truth_b2i _)) rfl Exec.skip) hx,
        stOutG_schrumpf X m G _ o hO⟩
  | none =>
      rw [hgp] at hnf h1
      simp only [] at hnf ⊢
      rw [endIstFehler_zu] at hnf
      obtain ⟨o, hx, hO⟩ := hs _ st1 ρG ρC hc1 hrel1 hnf
      obtain ⟨hO', hab⟩ := endOutG_zu0 X m G _ o hO
      exact ⟨o, Exec.seqX (Exec.iteT (ev_lnot h1 (truth_b2i _)) rfl hx) hab, hO'⟩

/-- `narrow x …` of a float local `x`: the narrowed value sits in `x`'s own
    C local (the same bits). -/
theorem gleitNarrow_bind_var {Λ : List (Res D)} {lo hi lo' hi' : Int × Int}
    (x : Var Γ (.fl lo hi)) :
    ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok) (v : Wert D (.fl lo' hi')),
      corrW X.EL σ st → EnvRelG X G K ρG ρC st →
      v.x = (eval σ (Expr.var (Λ := Λ) x) σ ρG).x →
      EnvRelG X G (K.push (.fl lo' hi') (K.loc x)) (.cons v ρG) ρC st := by
  intro σ st ρG ρC v _ hrel hv
  refine ⟨⟨fun τ y => ?_, hrel.1.2.1, hrel.1.2.2⟩, hrel.2⟩
  cases y with
  | hier =>
      have h : ghostify X.EL.lay X.fr G.gs ρC st (K.loc x) = .int (fEin f64 (ρG.get x).x)
          ∧ wf f64 (ρG.get x).x := hrel.1.1 _ x
      have hv' : v.x = (ρG.get x).x := hv
      show ghostify X.EL.lay X.fr G.gs ρC st (K.loc x) = .int (fEin f64 v.x) ∧ wf f64 v.x
      rw [hv']; exact h
  | dort y => exact hrel.1.1 _ y

end Bloecke

/-
CUTS: what this file does not do, by name.
- `float` (binary32) has C forms (`CX.fbin … f32`, the `f` literals) and
  the named assumption covers it, but NO correspondence: `Ty.fl` carries
  no width and the model computes every float in binary64, so an `f32`
  program's model value is its binary64 value, which `float` arithmetic
  does not compute. Lifting needs a width in `Ty.fl` (a Syntax change).
- Floats in MEMORY (a table field or a global of float type) have no
  correspondence: `corrW` relates cells through `encW`, which has no float
  case (`tyFits (.fl …) _ = false`). Float locals and parameters are
  covered.
- The C float local is a bit container of type `uint64_t` for `=`; an
  emitted `=` that converts a float to an integer (or back, implicitly)
  is not a form here (the emitter writes neither; `roh` truncation of a
  float for a register write has no C lowering in the corpus).
- A float literal INSIDE an expression or a `return` (`x >= 0.0`, `return
  HALB;`) is inline in C, while the model binds it (`Block.gleitLit`); the
  pass-(i) judgement quantifies over every value of the bound variable, so
  the inline literal is covered per program (`CFormenFZeuge.lean`), not by
  a general lemma.
- NaN, infinities and signed-zero INPUTS never reach a Gabbro float
  (finite by type); the C forms compute them (the model is total), but no
  correspondence speaks about them.
- The machine bridge (`maschine_*`) is per operation; the closing theorem
  would carry `gleitkomma_ieee` as one premise over the whole run's float
  unit (the C semantics `ev` is Annex F by definition).
-/

#print axioms gsem_gleit
#print axioms gsem_gleitLit
#print axioms gsem_gleitVon
#print axioms gsem_gleitNarrow
#print axioms narrowCondF_ge_le
#print axioms narrowCondF_endlich
#print axioms ecorr_fllt
#print axioms ecorr_flge
#print axioms maschine_fbin
#print axioms gleitkomma_ieee_annexF

end Gabbro.Grammatik
