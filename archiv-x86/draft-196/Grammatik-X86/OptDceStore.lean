/-
  File:      Grammatik/X86/OptDceStore.lean
  Subject:   Dead-store rule lemma (lane 866).

  DESIGN section 7 row: local premise "pure (no token/atomic/call/check/stop/
  trap-capable FP) + dead confirmed", certificate "A+B", failure case
  "remove `0.0/0.0` (hides `logik bereich`); remove spin load", phase M,
  cost O(sites).

  Proved here, over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `Satz`, `Budget`): the back-to-back overwrite window
  `x = v1; x = v2` (same cell, validator-confirmed stability) reaches the
  same data memory, lock state and environment as `x = v2` alone; the only
  trace delta is the dead write event. Shared/volatile/atomic carriers,
  live cells and trap-capable FP producers are refused by `dceStoreZulassen`.
  No `ensures` is derived, no refusal becomes a warning, no faulting form is
  speculated above its guard.
-/
import Grammatik.Semantik
import Grammatik.Satz
import Grammatik.Budget
import Grammatik.ReferenzB
import Grammatik.Maschine

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one dead-store site
    (DESIGN section 7 row): same cell, removed store pure, carrier private
    (not shared/volatile/atomic), dead confirmed by recomputed liveness
    (layer B), and no trap-capable FP removed. -/
structure DceStoreCert where
  gleicheZelle : Bool
  reinEntfernt : Bool
  privatTraeger : Bool
  totBestaetigt : Bool
  keinFalleFP : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def dceStoreZulassen (c : DceStoreCert) : Bool :=
  c.gleicheZelle && c.reinEntfernt && c.privatTraeger && c.totBestaetigt && c.keinFalleFP

/-! ## 1. Refusal: every DESIGN failure case must NOT fire.

    A store to a shared/volatile/atomic carrier is refused (`privatTraeger
    = false` forces `false`): removing a spin load or a publishing write
    would hide a concurrent observation. A live cell is refused
    (`totBestaetigt = false`): the validator's recomputed liveness found a
    reader. A trap-capable FP producer is refused (`keinFalleFP = false`):
    removing `0.0/0.0` ("unused" NaN) would hide `logik bereich`. An impure
    removed store (token/atomic/call/check/stop in its footprint) and a
    cell mismatch are refused the same way. All are proved of the decided
    Bool, so the validator cannot silently skip them. -/

/-- A shared/volatile/atomic carrier refuses: spin loads and publishing
    writes stay. -/
theorem dceVerweigert_geteilt (c : DceStoreCert)
    (h : c.privatTraeger = false) :
    dceStoreZulassen c = false := by
  simp [dceStoreZulassen, h]

/-- A live cell refuses: a reader stands between the stores. -/
theorem dceVerweigert_lebendig (c : DceStoreCert)
    (h : c.totBestaetigt = false) :
    dceStoreZulassen c = false := by
  simp [dceStoreZulassen, h]

/-- A trap-capable FP producer refuses: `0.0/0.0` keeps its `logik bereich`. -/
theorem dceVerweigert_fpFalle (c : DceStoreCert)
    (h : c.keinFalleFP = false) :
    dceStoreZulassen c = false := by
  simp [dceStoreZulassen, h]

/-- An impure removed store refuses: token/atomic/call/check/stop stay. -/
theorem dceVerweigert_unrein (c : DceStoreCert)
    (h : c.reinEntfernt = false) :
    dceStoreZulassen c = false := by
  simp [dceStoreZulassen, h]

/-- A cell mismatch refuses: different cells are no overwrite. -/
theorem dceVerweigert_fremdzelle (c : DceStoreCert)
    (h : c.gleicheZelle = false) :
    dceStoreZulassen c = false := by
  simp [dceStoreZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_dceStoreZulassen_ok :
    dceStoreZulassen ⟨true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a shared-carrier certificate is refused. -/
theorem probe_dceStoreZulassen_geteilt :
    dceStoreZulassen ⟨true, true, false, true, true⟩ = false := by
  decide

/-- Probe: an FP-trap certificate is refused. -/
theorem probe_dceStoreZulassen_fpFalle :
    dceStoreZulassen ⟨true, true, true, true, false⟩ = false := by
  decide

/-! ## 2. Memory core: overwrite absorbs, locks survive the write.

    Writing the same cell twice is writing it once (over ARBITRARY values
    `v1 v2`: the dead value never matters); lock state only reads `nimmt`
    / `gibt` events, so the removed write event changes no held lock. Both
    are over the reused `World` operations, no new model. -/

/-- Overwrite absorbs: two writes to the same cell hold the second value
    everywhere and touch no global. -/
theorem storeSlot_absorbiert {D : Deklaration} (σ : World D) (t : D.Tab)
    (k : Int) (f : D.Feld t) (v1 v2 : Wert D (D.typ t f)) :
    ((σ.storeSlot t k f v1).storeSlot t k f v2).slots
      = (σ.storeSlot t k f v2).slots
    ∧ ((σ.storeSlot t k f v1).storeSlot t k f v2).globs
      = (σ.storeSlot t k f v2).globs := by
  constructor
  · funext t' k' f'
    by_cases ht : t' = t
    · subst ht
      by_cases hk : k' = k
      · subst hk
        by_cases hf : f' = f
        · subst hf
          simp [World.storeSlot]
        · simp [World.storeSlot, hf]
      · simp [World.storeSlot, hk]
    · simp [World.storeSlot, ht]
  · rfl

/-- A slot write keeps the held locks: `offen` ignores the write event. -/
theorem schreibSlot_haelt {D : Deklaration} (σ : World D) (t : D.Tab)
    (Λ : List (Res D)) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    (σ.schreibSlot t Λ k f v).haelt = σ.haelt := by
  rfl

/-- Probe: `40` overwritten by `100` reads as one write on `refD`. -/
theorem probe_storeSlot_absorbiert :
    (((refSp0.welt []).storeSlot () 0 ()
      (⟨40, by decide, by decide⟩ : Wert refD (refD.typ () ()))).storeSlot () 0 ()
      (⟨100, by decide, by decide⟩ : Wert refD (refD.typ () ()))).slots
    = ((refSp0.welt []).storeSlot () 0 ()
      (⟨100, by decide, by decide⟩ : Wert refD (refD.typ () ()))).slots :=
  (storeSlot_absorbiert _ _ _ _ _ _).1

/-- Probe: the write keeps the held locks on `refD`. -/
theorem probe_schreibSlot_haelt :
    ((refSp0.welt []).schreibSlot () [Res.held (D := refD) ()] 0 ()
      (⟨100, by decide, by decide⟩ : Wert refD (refD.typ () ()))).haelt
    = (refSp0.welt []).haelt :=
  schreibSlot_haelt _ _ _ _ _ _

/-! ## 3. Connection: the dead store disappears, nothing else moves.

    Both windows are `assignSlot` pairs/singletons: no step can fault (the
    arm has no `logik`/`hardware` outcome), call, lock, check, narrow,
    publish, await, exchange, touch an atomic, a register, or a device,
    and no step decides a `gleitPasst` -- the window performs no float
    computation at all, so no `logik bereich` (IEEE) can hide in the
    removed store. The validator fires the rule only under admission
    (`hz`); its recomputed stability (`hStabil`: the dead cell is the kept
    cell, and the kept index/value evaluate the same with and without the
    dead store) aligns the two writes. Conclusion, jointly:
    (1) all three steps are `.ok` with unchanged environments -- no fault
    added or removed, so contracts at their place read the same values
    downstream;
    (2) data memories agree (`slots`, `globs`): every downstream
    observation agrees;
    (3) held locks agree: lock discipline and concurrent lock observations
    are unchanged;
    (4) the exact trace delta, three equations: the original trace carries
    precisely the dead write event plus its pure reads on top of the
    optimised trace -- no call, lock, or shared-access event is added or
    removed, so call logs gain no event and the shared footprint is
    unchanged (the removed write targets the validator-certified private
    cell);
    (5) the cell holds the kept value in both worlds.
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard. -/

/-- CONNECTION: `x = v1; x = v2` reaches the same data, locks and
    environment as `x = v2`; the trace delta is exactly the dead write. -/
theorem OptDceStore_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e1 e2 : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (cert : DceStoreCert)
    (hz : dceStoreZulassen cert = true)
    (σ : World D) (ρ : Env D Γ)
    (σ₁ σa σb : World D)
    (hσ₁ : σ₁ = (σ.lese Λ (i.orte ++ e1.orte)).schreibSlot t Λ
      (eval (σ.lese Λ (i.orte ++ e1.orte)) i (σ.lese Λ (i.orte ++ e1.orte)) ρ).n f
      (eval (σ.lese Λ (i.orte ++ e1.orte)) e1 (σ.lese Λ (i.orte ++ e1.orte)) ρ))
    (hσa : σa = (σ₁.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
      (eval (σ₁.lese Λ (i.orte ++ e2.orte)) i (σ₁.lese Λ (i.orte ++ e2.orte)) ρ).n f
      (eval (σ₁.lese Λ (i.orte ++ e2.orte)) e2 (σ₁.lese Λ (i.orte ++ e2.orte)) ρ))
    (hσb : σb = (σ.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
      (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
      (eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ))
    (hStabil : dceStoreZulassen cert = true →
      (((eval (σ.lese Λ (i.orte ++ e1.orte)) i (σ.lese Λ (i.orte ++ e1.orte)) ρ).n
        = (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n)
      ∧ ((eval (σ₁.lese Λ (i.orte ++ e2.orte)) i (σ₁.lese Λ (i.orte ++ e2.orte)) ρ).n
        = (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n)
      ∧ (eval (σ₁.lese Λ (i.orte ++ e2.orte)) e2 (σ₁.lese Λ (i.orte ++ e2.orte)) ρ
        = eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ))) :
    execStmt O passes R
        (Stmt.assignSlot t f i e1 hw hL : Stmt D V l Γ Λ Λ) σ ρ
        = Ausgang.ok σ₁ ρ
    ∧ execStmt O passes R
        (Stmt.assignSlot t f i e2 hw hL : Stmt D V l Γ Λ Λ) σ₁ ρ
        = Ausgang.ok σa ρ
    ∧ execStmt O passes R
        (Stmt.assignSlot t f i e2 hw hL : Stmt D V l Γ Λ Λ) σ ρ
        = Ausgang.ok σb ρ
    ∧ σa.slots = σb.slots
    ∧ σa.globs = σb.globs
    ∧ σa.haelt = σb.haelt
    ∧ σ₁.spur = [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e1.orte)).haelt]
        ++ ((i.orte ++ e1.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur
    ∧ σa.spur = [Ereignis.zugriff t true Λ (σ₁.lese Λ (i.orte ++ e2.orte)).haelt]
        ++ ((i.orte ++ e2.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ₁.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ₁.haelt) ++ σ₁.spur
    ∧ σb.spur = [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e2.orte)).haelt]
        ++ ((i.orte ++ e2.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur
    ∧ σb.slots t
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
      = eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ := by
  obtain ⟨hK1, hK2, hV⟩ := hStabil hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ₁]; rfl
  · rw [hσa]; rfl
  · rw [hσb]; rfl
  · rw [hσa, hσb]
    have ca : ((σ₁.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) i (σ₁.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) e2 (σ₁.lese Λ (i.orte ++ e2.orte)) ρ)).slots
      = ((σ.storeSlot t
        (eval (σ.lese Λ (i.orte ++ e1.orte)) i (σ.lese Λ (i.orte ++ e1.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e1.orte)) e1 (σ.lese Λ (i.orte ++ e1.orte)) ρ)).storeSlot t
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) i (σ₁.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) e2 (σ₁.lese Λ (i.orte ++ e2.orte)) ρ)).slots := by
      rw [hσ₁]; rfl
    have cb : ((σ.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ)).slots
      = (σ.storeSlot t
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ)).slots :=
      rfl
    rw [ca, cb, hK1, hK2, hV]
    exact (storeSlot_absorbiert _ _ _ _ _ _).1
  · rw [hσa, hσb]
    have ga : ((σ₁.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) i (σ₁.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) e2 (σ₁.lese Λ (i.orte ++ e2.orte)) ρ)).globs
      = σ.globs := by
      rw [hσ₁]; rfl
    have gb : ((σ.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ)).globs
      = σ.globs :=
      rfl
    rw [ga, gb]
  · rw [hσa, hσb, hσ₁]
    simp only [schreibSlot_haelt, lese_haelt]
  · rw [hσ₁]; rfl
  · rw [hσa]; rfl
  · rw [hσb]; rfl
  · rw [hσb]
    have hb : (((σ.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ)).slots t
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f)
      = ((σ.storeSlot t
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ)).slots t
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f) :=
      rfl
    rw [hb]
    exact storeSlot_hit _ _ _ _ _

/-! ## 4. Budget: the dead store's pass disappears, no pass gains cost.

    Over the REUSED `Budget.lean` sequence layer (`seqPassesAux`: one pass
    per element under its own fresh budget): dropping the dead store drops
    exactly its pass, and every surviving pass keeps its declared op list.
    Pass names shift by the drop (the validator re-checks exhaustion
    timing on the optimised list -- re-summing declared costs is
    bookkeeping, exhaustion timing stays validator-side, as in `Budget.lean`
    itself, whose sequence layer carries no verified `execStmt` link). -/

/-- BUDGET: removing the dead element drops exactly one pass; every
    surviving pass keeps its op list. -/
theorem dceBudget_passAbzug {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} (assign : SeqElem D V l Γ → List Op) (i : Nat)
    (e1 e2 : SeqElem D V l Γ) (es : List (SeqElem D V l Γ)) :
    (seqPassesAux assign (i + 1) (e2 :: es)).length + 1
      = (seqPassesAux assign i (e1 :: e2 :: es)).length
    ∧ ∀ p ∈ seqPassesAux assign (i + 1) (e2 :: es),
      ∃ q ∈ seqPassesAux assign i (e1 :: e2 :: es), p.2 = q.2 := by
  constructor
  · simp only [seqPassesAux_cons, List.length_cons]
  · intro p hm
    rw [seqPassesAux_cons]
    exact ⟨p, List.mem_cons.mpr (Or.inr hm), rfl⟩

/-- JOINT WITNESS for `dceBudget_passAbzug` on `refD`: the dropped pass is
    the dead `konto[0] := 100` store, beside the memory-changing run. -/
theorem dceBudget_passAbzug_zeuge :
    ∃ (assign : SeqElem refD (vertragVon refD refEin) false [.int 0 10] → List Op)
      (i : Nat) (e1 e2 : SeqElem refD (vertragVon refD refEin) false [.int 0 10])
      (es : List (SeqElem refD (vertragVon refD refEin) false [.int 0 10])),
      (seqPassesAux assign (i + 1) (e2 :: es)).length + 1
        = (seqPassesAux assign i (e1 :: e2 :: es)).length
      ∧ (∀ p ∈ seqPassesAux assign (i + 1) (e2 :: es),
        ∃ q ∈ seqPassesAux assign i (e1 :: e2 :: es), p.2 = q.2)
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  refine ⟨fun _ => [⟨3⟩], 0, SeqElem.ofStmt refWriteStAt,
    SeqElem.ofStmt refWriteStAt, [], ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptDceStore_verbindung` instantiated JOINTLY:
    `konto[0] := 40` overwritten by `konto[0] := 100` (the dead `40`
    never matters) in the NON-DEGENERATE reference program `refD`
    (whose `einzahlen` writes its table, `refEin_schreibt`), beside the
    reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). All ten conclusion conjuncts are
    used. -/

/-- The dead value `40` in range on `refD`. -/
def dceZeugeVierzig
    : Expr refD [.int 0 10] [Res.held (D := refD) ()] (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 40)

/-- The witness environment: argument `7` of `einzahlen`. -/
def dceZeugeRho : Env refD [.int 0 10] :=
  .cons ⟨7, by decide, by decide⟩ .nil

/-- Witness world after the dead store. -/
def dceZeugeW1 : World refD :=
  ((refSp0.welt []).lese [Res.held (D := refD) ()]
    (refIdxEin.orte ++ dceZeugeVierzig.orte)).schreibSlot ()
    [Res.held (D := refD) ()]
    (eval ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ dceZeugeVierzig.orte)) refIdxEin
      ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ dceZeugeVierzig.orte)) dceZeugeRho).n ()
    (eval ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ dceZeugeVierzig.orte)) dceZeugeVierzig
      ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ dceZeugeVierzig.orte)) dceZeugeRho)

/-- Witness world after dead plus kept store. -/
def dceZeugeWa : World refD :=
  (dceZeugeW1.lese [Res.held (D := refD) ()]
    (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
    [Res.held (D := refD) ()]
    (eval (dceZeugeW1.lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) refIdxEin
      (dceZeugeW1.lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) dceZeugeRho).n ()
    (eval (dceZeugeW1.lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) refHundert
      (dceZeugeW1.lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) dceZeugeRho)

/-- Witness world after the kept store alone. -/
def dceZeugeWb : World refD :=
  (((refSp0.welt []).lese [Res.held (D := refD) ()]
    (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
    [Res.held (D := refD) ()]
    (eval ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) refIdxEin
      ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) dceZeugeRho).n ()
    (eval ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) refHundert
      ((refSp0.welt []).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) dceZeugeRho))

/-- JOINT WITNESS for `OptDceStore_verbindung`: `konto[0] := 40`
    overwritten by `konto[0] := 100` on `refD`, beside the
    memory-changing reached run. -/
theorem OptDceStore_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (t : refD.Tab) (f : refD.Feld t)
      (i : Expr refD Γ Λ (.index (refD.count t)))
      (e1 e2 : Expr refD Γ Λ (refD.typ t f))
      (hw : V.schreibt t = true) (hL : darf refD t Λ)
      (cert : DceStoreCert) (_hz : dceStoreZulassen cert = true)
      (σ : World refD) (ρ : Env refD Γ)
      (σ₁ σa σb : World refD)
      (_hσ₁ : σ₁ = (σ.lese Λ (i.orte ++ e1.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e1.orte)) i (σ.lese Λ (i.orte ++ e1.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e1.orte)) e1 (σ.lese Λ (i.orte ++ e1.orte)) ρ))
      (_hσa : σa = (σ₁.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) i (σ₁.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ₁.lese Λ (i.orte ++ e2.orte)) e2 (σ₁.lese Λ (i.orte ++ e2.orte)) ρ))
      (_hσb : σb = (σ.lese Λ (i.orte ++ e2.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ))
      (_hStabil : dceStoreZulassen cert = true →
        (((eval (σ.lese Λ (i.orte ++ e1.orte)) i (σ.lese Λ (i.orte ++ e1.orte)) ρ).n
          = (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n)
        ∧ ((eval (σ₁.lese Λ (i.orte ++ e2.orte)) i (σ₁.lese Λ (i.orte ++ e2.orte)) ρ).n
          = (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n)
        ∧ (eval (σ₁.lese Λ (i.orte ++ e2.orte)) e2 (σ₁.lese Λ (i.orte ++ e2.orte)) ρ
          = eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ))),
      execStmt O passes R
          (Stmt.assignSlot t f i e1 hw hL : Stmt refD V l Γ Λ Λ) σ ρ
          = Ausgang.ok σ₁ ρ
      ∧ execStmt O passes R
          (Stmt.assignSlot t f i e2 hw hL : Stmt refD V l Γ Λ Λ) σ₁ ρ
          = Ausgang.ok σa ρ
      ∧ execStmt O passes R
          (Stmt.assignSlot t f i e2 hw hL : Stmt refD V l Γ Λ Λ) σ ρ
          = Ausgang.ok σb ρ
      ∧ σa.slots = σb.slots
      ∧ σa.globs = σb.globs
      ∧ σa.haelt = σb.haelt
      ∧ σ₁.spur = [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e1.orte)).haelt]
          ++ ((i.orte ++ e1.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur
      ∧ σa.spur = [Ereignis.zugriff t true Λ (σ₁.lese Λ (i.orte ++ e2.orte)).haelt]
          ++ ((i.orte ++ e2.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ₁.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ₁.haelt) ++ σ₁.spur
      ∧ σb.spur = [Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e2.orte)).haelt]
          ++ ((i.orte ++ e2.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur
      ∧ σb.slots t
          (eval (σ.lese Λ (i.orte ++ e2.orte)) i (σ.lese Λ (i.orte ++ e2.orte)) ρ).n f
        = eval (σ.lese Λ (i.orte ++ e2.orte)) e2 (σ.lese Λ (i.orte ++ e2.orte)) ρ
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptDceStore_verbindung (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (l := false)
    (t := ()) (f := ()) (i := refIdxEin)
    (e1 := dceZeugeVierzig) (e2 := refHundert)
    (hw := refEin_schreibt ()) (hL := refDarfEin)
    (cert := ⟨true, true, true, true, true⟩) (hz := by decide)
    (σ := refSp0.welt []) (ρ := dceZeugeRho)
    (σ₁ := dceZeugeW1) (σa := dceZeugeWa) (σb := dceZeugeWb)
    (hσ₁ := rfl) (hσa := rfl) (hσb := rfl)
    (hStabil := fun _ => ⟨rfl, rfl, rfl⟩)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [.int 0 10],
    [Res.held (D := refD) ()], false, (), (), refIdxEin, dceZeugeVierzig,
    refHundert, refEin_schreibt (), refDarfEin,
    ⟨true, true, true, true, true⟩, by decide,
    refSp0.welt [], dceZeugeRho, dceZeugeW1, dceZeugeWa, dceZeugeWb,
    rfl, rfl, rfl, (fun _ => ⟨rfl, rfl, rfl⟩),
    hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1,
    hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.2.1,
    hV.2.2.2.2.2.2.2.2.2,
    refEin_schreibt (), refB_erreicht, refB_schreibt⟩

/- CUTS:
    - Complete: refusals, memory core, connection, budget, joint witness.
    - No block-window float rewrite: the admitted float fold is out of
      scope here (no `gleit` form occurs in an `assignSlot` window); the
      trap-capable-FP refusal is proved at the certificate level
      (`dceVerweigert_fpFalle`).
    - No full rest-induction: the connection characterises the two
      rest-entry worlds (data, locks, env, exact trace delta) for an
      arbitrary downstream; the lock-step simulation over an arbitrary
      `rest` with calls stays with the lowering lane (calls invoke the
      universally quantified handler `R`).
    - No totalCost inequality: removing one element drops exactly its
      `seqPassesAux` pass with all op lists kept (`dceBudget_passAbzug`);
      the formal level-(c) machine-work bound is OPEN per IR-VALIDIERUNG.
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at source worlds and `Zahl` values.
-/

#print axioms DceStoreCert
#print axioms dceStoreZulassen
#print axioms dceVerweigert_geteilt
#print axioms dceVerweigert_lebendig
#print axioms dceVerweigert_fpFalle
#print axioms dceVerweigert_unrein
#print axioms dceVerweigert_fremdzelle
#print axioms storeSlot_absorbiert
#print axioms schreibSlot_haelt
#print axioms OptDceStore_verbindung
#print axioms dceBudget_passAbzug
#print axioms dceBudget_passAbzug_zeuge
#print axioms dceZeugeVierzig
#print axioms OptDceStore_verbindung_zeuge

end Gabbro.Grammatik.X86
