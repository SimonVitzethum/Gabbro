/-
  File:      Grammatik/X86/OptCseLoad.lean
  Subject:   Redundant-load CSE rule lemma (lane 864).

  DESIGN rows: OPTIMIZER section 3.7 A1 (load reuse over proved
  sameness), section 3.3 V1/V2 (no CSE across invalidation), section
  5.2 (no motion across atomics/locks/fences/calls/MMIO), section 7.2
  alias row (certificate carries sameness proof, validator rechecks).
  Status: PROPOSED rule with proved generic lemmas.

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`): the
  validator-decided side conditions for one load-CSE site (same
  object/width/align, token order, stability by ownership, held lock
  or immutability, pure index, no hoist above publish-acquire), the
  refusal of every violated side condition, value/word/IEEE
  preservation, and the two-bind window connection with its exact
  handoff (same slots/globs/locks/env values downstream, spur differs
  by exactly the eliminated read event). No `ensures` is derived, no
  refusal becomes a warning, no faulting form is speculated above its
  guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one load-CSE site
    (DESIGN section 7.2 alias row): same object (table, field and
    index VALUE identity, recomputed from the avail facts), same width,
    same alignment, token order (the dominating load reaches the site
    with no intervening store, atomic, fence, call or lock op),
    stability (exclusive ownership OR held-lock cover OR immutable
    carrier, discharged by the named leg, never by thread-local token
    reasoning alone), a pure index (no carrier read inside the index),
    and no hoist above a publish-acquire edge. -/
structure CseLoadCert where
  gleichObj : Bool
  breiteOk : Bool
  ausrOk : Bool
  tokenOk : Bool
  stabilOk : Bool
  idxRein : Bool
  keinPublishHoist : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never
    to a warning. -/
def cseLoadZulassen (c : CseLoadCert) : Bool :=
  c.gleichObj && c.breiteOk && c.ausrOk && c.tokenOk &&
    c.stabilOk && c.idxRein && c.keinPublishHoist

/-! ## 1. Refusals: every violated side condition refuses the rule.

    The precise refusal case where the rule must NOT fire: a hoist of
    the load above a publish-acquire edge (`keinPublishHoist = false`
    forces `false`), an intervening store/atomic/fence/call/lock op
    (`tokenOk = false`), a carrier without ownership, held-lock cover
    or immutability (`stabilOk = false`), a different object, width or
    alignment, or an impure index. All are proved of the decided Bool,
    so the validator cannot silently skip them. -/

/-- A hoist above publish-acquire refuses the rule. -/
theorem cseLoadVerweigert_publish (c : CseLoadCert)
    (h : c.keinPublishHoist = false) :
    cseLoadZulassen c = false := by
  simp [cseLoadZulassen, h]

/-- An intervening invalidation (store, atomic, fence, call, lock op)
    refuses the rule. -/
theorem cseLoadVerweigert_token (c : CseLoadCert)
    (h : c.tokenOk = false) :
    cseLoadZulassen c = false := by
  simp [cseLoadZulassen, h]

/-- A carrier without ownership, held-lock cover or immutability
    refuses the rule. -/
theorem cseLoadVerweigert_stabil (c : CseLoadCert)
    (h : c.stabilOk = false) :
    cseLoadZulassen c = false := by
  simp [cseLoadZulassen, h]

/-- A different object refuses the rule. -/
theorem cseLoadVerweigert_objekt (c : CseLoadCert)
    (h : c.gleichObj = false) :
    cseLoadZulassen c = false := by
  simp [cseLoadZulassen, h]

/-- A width or alignment mismatch refuses the rule. -/
theorem cseLoadVerweigert_weite (c : CseLoadCert)
    (h : c.breiteOk = false ∨ c.ausrOk = false) :
    cseLoadZulassen c = false := by
  rcases h with h | h <;> simp [cseLoadZulassen, h]

/-- An impure index refuses the rule. -/
theorem cseLoadVerweigert_idx (c : CseLoadCert)
    (h : c.idxRein = false) :
    cseLoadZulassen c = false := by
  simp [cseLoadZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_cseLoadZulassen_ok :
    cseLoadZulassen ⟨true, true, true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a publish-hoist certificate is refused. -/
theorem probe_cseLoadZulassen_publish :
    cseLoadZulassen ⟨true, true, true, true, true, true, false⟩ = false := by
  decide

/-- Probe: an invalidated-token certificate is refused. -/
theorem probe_cseLoadZulassen_token :
    cseLoadZulassen ⟨true, true, true, false, true, true, true⟩ = false := by
  decide

/-! ## 2. Value, word and IEEE preservation.

    The reused value IS the reloaded value: both are the carrier slot
    at the same index. The width-exact value reads back whole through
    the canonical word (the validator-decided `hW`, DESIGN section 7
    recomputation). For float carriers the same value equality carries
    the `gleitPasst` outcome, in the single kernel rounding scope --
    no reassociation, no width change, no NaN-payload reasoning
    (OPTIMIZER section 3.9 F2-F4 stay refused). -/

/-- The reused integer value reads back whole through the word. -/
theorem cseLoadWort (v : Int) (hW : 0 ≤ v ∧ v < 2 ^ 64) :
    ((BitVec.ofNat 64 v.toNat : Wort)).toNat = v.toNat := by
  have h : v.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `100` reads back as `100` through the word. -/
theorem probe_cseLoadWort :
    ((BitVec.ofNat 64 ((100 : Int)).toNat : Wort)).toNat = 100 := by
  decide

/-- The reused float value keeps the `gleitPasst` outcome: same pushed
    value, same `logik bereich` outcome, so neither a value nor a fault
    is folded away by the reuse. -/
theorem cseLoadGleit_behält (vNeu vAlt lo hi : Int × Int)
    (hEq : vNeu = vAlt) :
    gleitPasst lo hi (bruch vNeu) = gleitPasst lo hi (bruch vAlt) := by
  rw [hEq]

/-- Probe: the kernel compares `0.5` against `0 .. 1` the same way. -/
theorem probe_cseLoadGleit :
    gleitPasst (0, 1) (1, 1) (bruch (1, 2)) =
      gleitPasst (0, 1) (1, 1) (bruch (1, 2)) := by
  rfl

/-! ## 3. Certificate shape: local rewrite record plus recomputed
    analysis citations (DESIGN section 7.2 alias row).

    The Rust pass emits the site pair plus citation ids; the validator
    recomputes sameness (region/range proof recheck), token order
    (no-store scan between the cited sites) and purity (index-orte
    recomputation) from the source text. Nothing is trusted from Rust:
    a wrong citation refuses through `cseLoadZulassen`. -/

/-- The exact certificate shape: the dominating load site, the reuse
    site, the availability citation (dominating bind id, avail-fact
    id), the purity-trace citation, and the decided side conditions. -/
structure CseLoadRewrite where
  ladestelle : Nat
  nutzungsstelle : Nat
  zitatVerfuegbar : Nat × Nat
  zitatReinheit : Nat
  zert : CseLoadCert
  deriving DecidableEq, Repr

/-- Validator admission of one rewrite record. -/
def cseLoadRewritePrueft (w : CseLoadRewrite) : Bool :=
  cseLoadZulassen w.zert

/-- Admission of the record is admission of its side conditions. -/
theorem cseLoadRewrite_prueft (w : CseLoadRewrite) :
    cseLoadRewritePrueft w = cseLoadZulassen w.zert := by
  rfl

/-- Probe: an all-true record is admitted. -/
theorem probe_cseLoadRewrite_ok :
    cseLoadRewritePrueft ⟨3, 7, (3, 0), 1,
      ⟨true, true, true, true, true, true, true⟩⟩ = true := by
  decide

/-- Probe: a publish-hoist record is refused. -/
theorem probe_cseLoadRewrite_publish :
    cseLoadRewritePrueft ⟨3, 7, (3, 0), 1,
      ⟨true, true, true, true, true, true, false⟩⟩ = false := by
  decide

/-! ## 4. Connection: the two-bind load window with reuse.

    The window covers integer-typed carriers (`hτ`: the validator's
    width proof names the exact `.int lo hi`, so the reused value
    reads back through the canonical word in (6)).

    The rewrite fires on two adjacent loads from the same carrier
    (the DESIGN token-order premise by construction: no statement
    stands between the binds) with the same index value (`hIdx`, the
    validator's sameness proof) and an unchanged carrier (`hHalt`,
    discharged by ownership, held-lock cover or immutability -- the
    DESIGN stability premise), a pure index (`hOrte`, the DESIGN
    purity recomputation) and a width-exact value (`hW`). The
    validator admission (`hz`) is consumed by the conditional
    deliveries `hIdx`/`hHalt`, the DESIGN section 7.3 soundness shape;
    the generic Bool-to-Prop bridge (`optSound`) stays OPEN in CUTS.
    Conclusion, jointly:
    (1) the reused VALUE equals the reloaded one;
    (2) the handoff worlds agree on memory (slots and globs);
    (3) the handoff worlds agree on the held locks (reads never open
    or close a lock, so every continuation observes the same lock
    discipline -- contracts at their place, `SperrWechselG` order);
    (4) the EXACT trace difference: the optimized spur drops precisely
    the one eliminated read event -- no call event exists on either
    side, so call logs gain and lose nothing, and concurrent
    observers see one fewer read and no new write;
    (5) the orte equations: the eliminated load read at most `t`, the
    reuse reads nothing, neither writes nor calls;
    (6) the reused value reads back whole through the canonical word;
    (7)-(8) both windows unfold to the SAME continuation `rest` at
    the explicitly related handoff states -- so no fault is added or
    removed AT THE SITE (both evals are total), every downstream
    fault comes from `rest` applied to states related by (1)-(4), and
    the removed computation is one pure total read (no budget counter
    moves at a bind).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard. -/

/-- The integer value of an int-typed slot read, through the checked
    type proof (cf. `Adressraum.weltByte`: `Wert D (.int lo hi)` IS
    `Zahl lo hi`, so the cast only moves the field's type proof). -/
def cseSlotN (D : Deklaration) (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hτ : D.typ t f = .int lo hi)
    (σ₀ σ : World D) {Γ : Ctx} {Λ : List (Res D)}
    (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ)
    (ρ : Env D Γ) : Int :=
  (cast (congrArg (Wert D) hτ) (eval σ₀ (Expr.slot t f i hL) σ ρ)).n

theorem OptCseLoad_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    {t : D.Tab} {f : D.Feld t}
    {i₁ : Expr D Γ Λ (.index (D.count t))}
    {i₂ : Expr D (D.typ t f :: Γ) Λ (.index (D.count t))}
    (hL₁ : darf D t Λ) (hL₂ : darf D t Λ)
    (eV : Expr D (D.typ t f :: Γ) Λ (D.typ t f))
    (heV : eV = Expr.var Var.hier)
    (lo hi : Int) (hτ : D.typ t f = .int lo hi)
    (cert : CseLoadCert)
    (hz : cseLoadZulassen cert = true)
    (σ : World D) (ρ : Env D Γ)
    (σ₁ : World D) (hσ₁ : σ₁ = σ.lese Λ (Expr.slot t f i₁ hL₁).orte)
    (ρ₁ : Env D (D.typ t f :: Γ))
    (hρ₁ : ρ₁ = Env.cons (eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ) ρ)
    (σ₂ : World D) (hσ₂ : σ₂ = σ₁.lese Λ (Expr.slot t f i₂ hL₂).orte)
    (σ₂' : World D) (hσ₂' : σ₂' = σ₁.lese Λ eV.orte)
    (ρ₂ : Env D (D.typ t f :: (D.typ t f :: Γ)))
    (hρ₂ : ρ₂ = Env.cons (eval σ₂ (Expr.slot t f i₂ hL₂) σ₂ ρ₁) ρ₁)
    (ρ₂' : Env D (D.typ t f :: (D.typ t f :: Γ)))
    (hρ₂' : ρ₂' = Env.cons (eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ) ρ₁)
    (hIdx : cseLoadZulassen cert = true →
      (eval σ₂ i₂ σ₂ ρ₁).n = (eval σ₁ i₁ σ₁ ρ).n)
    (hHalt : cseLoadZulassen cert = true →
      σ₂.slots t (eval σ₁ i₁ σ₁ ρ).n f
        = σ₁.slots t (eval σ₁ i₁ σ₁ ρ).n f)
    (hOrte : i₁.orte = [] ∧ i₂.orte = [])
    (hW : 0 ≤ cseSlotN D t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ ∧
      cseSlotN D t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ < 2 ^ 64)
    (rest : Endblock D V l (D.typ t f :: (D.typ t f :: Γ)) Λ) :
    (eval σ₂ (Expr.slot t f i₂ hL₂) σ₂ ρ₁
      = eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ)
    ∧ σ₂.slots = σ₁.slots ∧ σ₂.globs = σ₁.globs
    ∧ σ₂.haelt = σ₂'.haelt
    ∧ σ₂.spur = Ereignis.zugriff t false Λ σ₁.haelt :: σ₂'.spur
    ∧ (Expr.slot t f i₂ hL₂).orte = [.inl t] ∧ eV.orte = []
    ∧ ((BitVec.ofNat 64 (cseSlotN D t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ).toNat : Wort)).toNat
        = (cseSlotN D t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ).toNat
    ∧ execEnd O passes R
        (Endblock.bind (Expr.slot t f i₁ hL₁)
          (Endblock.bind (Expr.slot t f i₂ hL₂) rest)) σ ρ
        = (execEnd O passes R rest σ₂ ρ₂).schrumpf.schrumpf
    ∧ execEnd O passes R
        (Endblock.bind (Expr.slot t f i₁ hL₁)
          (Endblock.bind eV rest)) σ ρ
        = (execEnd O passes R rest σ₂' ρ₂').schrumpf.schrumpf := by
  have o₂ : (Expr.slot t f i₂ hL₂).orte = [.inl t] := by
    simp [Expr.orte, hOrte.2]
  have oV : eV.orte = [] := by
    rw [heV]
    rfl
  have eS₂ : eval σ₂ (Expr.slot t f i₂ hL₂) σ₂ ρ₁
      = σ₂.slots t (eval σ₂ i₂ σ₂ ρ₁).n f := rfl
  have eS₁ : eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ
      = σ₁.slots t (eval σ₁ i₁ σ₁ ρ).n f := rfl
  have hWert : eval σ₂ (Expr.slot t f i₂ hL₂) σ₂ ρ₁
      = eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ := by
    rw [eS₂, eS₁, hIdx hz]
    exact hHalt hz
  refine ⟨hWert, ?_, ?_, ?_, ?_, o₂, oV, ?_, ?_, ?_⟩
  · rw [hσ₂]; rfl
  · rw [hσ₂]; rfl
  · rw [hσ₂, hσ₂', o₂, oV]; rfl
  · rw [hσ₂, hσ₂', o₂, oV]; rfl
  · exact cseLoadWort _ hW
  · subst hσ₁; subst hρ₁; subst hσ₂; subst hρ₂; rfl
  · subst heV; subst hσ₁; subst hρ₁; subst hσ₂'; subst hρ₂'; rfl

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptCseLoad_verbindung` instantiated JOINTLY: two
    adjacent loads of `konto[0]` (closed index `0`, well-typed since
    `konto` has 2 slots) under a double `bind` with a `leave`
    continuation, in the NON-DEGENERATE reference program `refD`
    (whose `einzahlen` writes its table, `refEin_schreibt`), beside
    the reached F-machine run `MB` that changes memory
    (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`). The start
    slot reads `0`, so the width premise holds by computation. -/

/-- Closed index `0` into `konto` (2 slots): elaborates at any
    context, so both loads of the witness window share one shape. -/
def zwIdx {Γ : Ctx} {Λ : List (Res refD)} :
    Expr refD Γ Λ (.index (refD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- Probe: the closed index reads no carrier. -/
theorem probe_zwIdx_orte : (zwIdx (Γ := []) (Λ := [])).orte = [] := by
  rfl

/-- Witness index at the outer context. -/
def zwIdx0 : Expr refD [] [Res.held (D := refD) ()]
    (.index (refD.count ())) :=
  zwIdx

/-- Witness index at the extended context (same closed shape). -/
def zwIdx1 : Expr refD (refD.typ () () :: []) [Res.held (D := refD) ()]
    (.index (refD.count ())) :=
  zwIdx

/-- Witness first load `konto[0]`. -/
def zwLoad0 : Expr refD [] [Res.held (D := refD) ()] (refD.typ () ()) :=
  Expr.slot () () zwIdx0 refDarf

/-- Witness second load `konto[0]` (same shape, extended context). -/
def zwLoad1 : Expr refD (refD.typ () () :: []) [Res.held (D := refD) ()]
    (refD.typ () ()) :=
  Expr.slot () () zwIdx1 refDarf

/-- Witness reuse: the variable bound by the first load. -/
def zwVar : Expr refD (refD.typ () () :: []) [Res.held (D := refD) ()]
    (refD.typ () ()) :=
  Expr.var Var.hier

/-- Witness world after the first bind's framing. -/
def zwS1 : World refD :=
  (refSp0.welt []).lese [Res.held (D := refD) ()] zwLoad0.orte

/-- Witness env after the first bind. -/
def zwR1 : Env refD (refD.typ () () :: []) :=
  Env.cons (eval zwS1 zwLoad0 zwS1 Env.nil) Env.nil

/-- Witness world after the second load's framing. -/
def zwS2 : World refD :=
  zwS1.lese [Res.held (D := refD) ()] zwLoad1.orte

/-- Witness world after the reuse's (empty) framing. -/
def zwS2' : World refD :=
  zwS1.lese [Res.held (D := refD) ()] zwVar.orte

/-- Witness env after the second load. -/
def zwR2 : Env refD (refD.typ () () :: (refD.typ () () :: [])) :=
  Env.cons (eval zwS2 zwLoad1 zwS2 zwR1) zwR1

/-- Witness env after the reuse. -/
def zwR2' : Env refD (refD.typ () () :: (refD.typ () () :: [])) :=
  Env.cons (eval zwS1 zwLoad0 zwS1 Env.nil) zwR1

/-- JOINT WITNESS for `OptCseLoad_verbindung`: two adjacent `konto[0]`
    loads with reuse on `refD`, beside the memory-changing reached run.
    ALL premises are instantiated JOINTLY, including the conditional
    deliveries (`hIdx`, `hHalt` close by computation: the index is
    closed, the adjacent binds frame without storing) and the width
    fact (the start slot reads `0`). -/
theorem OptCseLoad_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (t : refD.Tab) (f : refD.Feld t)
      (i₁ : Expr refD Γ Λ (.index (refD.count t)))
      (i₂ : Expr refD (refD.typ t f :: Γ) Λ (.index (refD.count t)))
      (hL₁ : darf refD t Λ) (hL₂ : darf refD t Λ)
      (eV : Expr refD (refD.typ t f :: Γ) Λ (refD.typ t f))
      (_heV : eV = Expr.var Var.hier)
      (lo hi : Int) (hτ : refD.typ t f = .int lo hi)
      (cert : CseLoadCert) (_hz : cseLoadZulassen cert = true)
      (σ : World refD) (ρ : Env refD Γ)
      (σ₁ : World refD)
      (_hσ₁ : σ₁ = σ.lese Λ (Expr.slot t f i₁ hL₁).orte)
      (ρ₁ : Env refD (refD.typ t f :: Γ))
      (_hρ₁ : ρ₁ = Env.cons (eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ) ρ)
      (σ₂ : World refD)
      (_hσ₂ : σ₂ = σ₁.lese Λ (Expr.slot t f i₂ hL₂).orte)
      (σ₂' : World refD) (_hσ₂' : σ₂' = σ₁.lese Λ eV.orte)
      (ρ₂ : Env refD (refD.typ t f :: (refD.typ t f :: Γ)))
      (_hρ₂ : ρ₂ = Env.cons (eval σ₂ (Expr.slot t f i₂ hL₂) σ₂ ρ₁) ρ₁)
      (ρ₂' : Env refD (refD.typ t f :: (refD.typ t f :: Γ)))
      (_hρ₂' : ρ₂' = Env.cons (eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ) ρ₁)
      (_hIdx : cseLoadZulassen cert = true →
        (eval σ₂ i₂ σ₂ ρ₁).n = (eval σ₁ i₁ σ₁ ρ).n)
      (_hHalt : cseLoadZulassen cert = true →
        σ₂.slots t (eval σ₁ i₁ σ₁ ρ).n f
          = σ₁.slots t (eval σ₁ i₁ σ₁ ρ).n f)
      (_hOrte : i₁.orte = [] ∧ i₂.orte = [])
      (_hW : 0 ≤ cseSlotN refD t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ ∧
        cseSlotN refD t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ < 2 ^ 64)
      (rest : Endblock refD V l
        (refD.typ t f :: (refD.typ t f :: Γ)) Λ),
      (eval σ₂ (Expr.slot t f i₂ hL₂) σ₂ ρ₁
        = eval σ₁ (Expr.slot t f i₁ hL₁) σ₁ ρ)
      ∧ σ₂.slots = σ₁.slots ∧ σ₂.globs = σ₁.globs
      ∧ σ₂.haelt = σ₂'.haelt
      ∧ σ₂.spur = Ereignis.zugriff t false Λ σ₁.haelt :: σ₂'.spur
      ∧ (Expr.slot t f i₂ hL₂).orte = [.inl t] ∧ eV.orte = []
      ∧ ((BitVec.ofNat 64
            (cseSlotN refD t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ).toNat : Wort)).toNat
          = (cseSlotN refD t f lo hi hτ σ₁ σ₁ i₁ hL₁ ρ).toNat
      ∧ execEnd O passes R
          (Endblock.bind (Expr.slot t f i₁ hL₁)
            (Endblock.bind (Expr.slot t f i₂ hL₂) rest)) σ ρ
          = (execEnd O passes R rest σ₂ ρ₂).schrumpf.schrumpf
      ∧ execEnd O passes R
          (Endblock.bind (Expr.slot t f i₁ hL₁)
            (Endblock.bind eV rest)) σ ρ
          = (execEnd O passes R rest σ₂' ρ₂').schrumpf.schrumpf
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptCseLoad_verbindung (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf)
    (hL₁ := refDarf) (hL₂ := refDarf)
    (eV := zwVar) (heV := rfl)
    (lo := 0) (hi := 100) (hτ := rfl)
    (cert := ⟨true, true, true, true, true, true, true⟩)
    (hz := by decide)
    (σ := refSp0.welt []) (ρ := Env.nil)
    (σ₁ := zwS1) (hσ₁ := rfl)
    (ρ₁ := zwR1) (hρ₁ := rfl)
    (σ₂ := zwS2) (hσ₂ := rfl)
    (σ₂' := zwS2') (hσ₂' := rfl)
    (ρ₂ := zwR2) (hρ₂ := rfl)
    (ρ₂' := zwR2') (hρ₂' := rfl)
    (hIdx := fun _ => rfl) (hHalt := fun _ => rfl)
    (hOrte := ⟨rfl, rfl⟩) (hW := by decide)
    (rest := Endblock.leave rfl)
  obtain ⟨c1, c2a, c2b, c3, c4, c5a, c5b, c6, c7, c8⟩ := hV
  exact ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [Res.held (D := refD) ()],
    true, (), (), zwIdx0, zwIdx1, refDarf, refDarf, zwVar, rfl,
    0, 100, rfl, ⟨true, true, true, true, true, true, true⟩, by decide,
    refSp0.welt [], Env.nil, zwS1, rfl, zwR1, rfl, zwS2, rfl, zwS2', rfl,
    zwR2, rfl, zwR2', rfl, (fun _ => rfl), (fun _ => rfl), ⟨rfl, rfl⟩,
    by decide, Endblock.leave rfl,
    c1, c2a, c2b, c3, c4, c5a, c5b, c6, c7, c8,
    refEin_schreibt (), refB_erreicht, refB_schreibt⟩

/- CUTS:
    - No generic `optSound` (DESIGN section 7.3): the Bool-to-Prop
      bridge -- from `cseLoadZulassen cert = true` to the semantic
      sameness/stability facts -- is ASSUMED per instance through the
      conditional deliveries `hIdx`/`hHalt`, never proved from the
      `Bool`. The validator's recomputation (region/range proof
      recheck, no-store scan, purity recomputation) and its one
      generic soundness lemma belong to the validator lane.
    - No downstream rest-induction: (7)-(8) unfold both windows to the
      SAME continuation at explicitly related handoff states; that an
      ARBITRARY continuation observes equal contracts, call logs and
      budget stops on those states is not derived here (it needs
      induction over `Endblock`, owned by the lowering/IR lane). What
      IS proved: both continuations receive equal values, equal
      slots/globs, equal held locks and equal env heads, with the
      exact one-read-event spur difference.
    - No non-adjacent window: token order is by construction (adjacent
      binds); a reuse across an intervening statement needs the full
      avail/dominator proof (DESIGN section 7.2 GVN row), OPEN.
    - No float-typed load window: `cseLoadGleit_behält` proves the
      admitted float reuse preserves value and `gleitPasst` outcome at
      the value level; the `Endblock` connection is stated for
      integer-typed carriers (the word image (6) needs `hτ`).
    - No totalCost/budget inequality: both windows are the same block
      spine with one pure total read removed, so step-budget
      accounting is unchanged; the formal level-(c) machine-work bound
      is OPEN per IR-VALIDIERUNG.
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader
      claim: correspondence stops at canonical words and `gleitPasst`
      values. The per-access target-to-W/GX simulation is OPEN.
-/

#print axioms cseLoadZulassen
#print axioms cseLoadVerweigert_publish
#print axioms cseLoadVerweigert_token
#print axioms cseLoadVerweigert_stabil
#print axioms cseLoadVerweigert_objekt
#print axioms cseLoadVerweigert_weite
#print axioms cseLoadVerweigert_idx
#print axioms cseLoadWort
#print axioms probe_cseLoadWort
#print axioms cseLoadGleit_behält
#print axioms probe_cseLoadGleit
#print axioms cseLoadRewritePrueft
#print axioms cseLoadRewrite_prueft
#print axioms cseSlotN
#print axioms OptCseLoad_verbindung
#print axioms OptCseLoad_verbindung_zeuge

end Gabbro.Grammatik.X86
