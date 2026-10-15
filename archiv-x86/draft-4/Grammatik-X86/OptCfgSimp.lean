/-
  File:      Grammatik/X86/OptCfgSimp.lean
  Subject:   CFG simplification rule lemma (lane 862).

  DESIGN section 7 row: local premise "unreachable edge proof (decided const
  cond), exit edges preserved", certificate "B block map", failure case
  "delete a `narrow`-else edge ("unreachable" by range hope)", phase E,
  cost O(blocks).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, the decided-condition checker of `InvariantenOpt`,
  the `refD` witness program of `ReferenzB`): the validator-decided side
  conditions for one simplification site (`CfgSimpCert`, admitted by
  `cfgZulassen`), with all three refusal legs. Later sections add the
  decided-condition value lemma, the executable rewrites, the
  value/fault/observation preservation (IEEE, contracts at their place,
  call logs, concurrency, budget) and the joint witness.
  No `ensures` is derived, no refusal becomes a warning, no faulting form
  is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one CFG-simplification site
    (DESIGN section 7 row): the condition edge is decided constant
    (`bedingtEntschieden`, recomputed `isWahr` cited by the bridge premise),
    the block map preserves every exit edge of the kept branch
    (`austrittErhalten`), and the deleted edge is no `narrow`-else
    (`keinNarrowSonst`, recomputed over the deleted syntax). -/
structure CfgSimpCert where
  bedingtEntschieden : Bool
  austrittErhalten : Bool
  keinNarrowSonst : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def cfgZulassen (c : CfgSimpCert) : Bool :=
  c.bedingtEntschieden && c.austrittErhalten && c.keinNarrowSonst

/-! ## 1. Refusal: every missing side condition refuses to fire.

    An undecided condition refuses (no compiler-guessed truth), a site
    whose block map drops an exit edge refuses, and a `narrow`-else edge
    refuses unconditionally: a `narrow` else is live whenever an
    out-of-range value arrives (section 3 exhibits it), so deleting it on
    "range hope" would drop a source fault. All three are proved of the
    decided Bool, so the validator cannot silently skip them. -/

/-- An undecided condition refuses the simplification. -/
theorem cfgVerweigert_unentschieden (c : CfgSimpCert)
    (h : c.bedingtEntschieden = false) :
    cfgZulassen c = false := by
  simp [cfgZulassen, h]

/-- A site that drops an exit edge refuses the simplification. -/
theorem cfgVerweigert_austritt (c : CfgSimpCert)
    (h : c.austrittErhalten = false) :
    cfgZulassen c = false := by
  simp [cfgZulassen, h]

/-- A `narrow`-else edge refuses the simplification (DESIGN failure case). -/
theorem cfgVerweigert_narrowSonst (c : CfgSimpCert)
    (h : c.keinNarrowSonst = false) :
    cfgZulassen c = false := by
  simp [cfgZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_cfgZulassen_ok :
    cfgZulassen ⟨true, true, true⟩ = true := by
  decide

/-- Probe: a `narrow`-else certificate is refused. -/
theorem probe_cfgZulassen_narrow :
    cfgZulassen ⟨true, true, false⟩ = false := by
  decide

/-- Probe: an undecided certificate is refused. -/
theorem probe_cfgZulassen_unentschieden :
    cfgZulassen ⟨false, true, true⟩ = false := by
  decide

/-! ## 2. Decided conditions: firing consults boolean truth only.

    The validator's recomputation (`isWahr`, sound over `eval` by
    `isWahrAll_sound`) decides the edge. The firing decision therefore
    consults only boolean truth at `.bool` -- never float rounding, never
    NaN, never a guessed `ensures`: a condition that is merely "true by
    contract" answers `false` and the rule does not fire. Float
    computations (`gleitRechne` values in the kernel model) are never
    named by the decision; the kept branch computes them unchanged. -/

/-- A decided condition really evaluates true: the firing decision is
    boolean truth at `.bool`, over the ARBITRARY condition `c`. -/
theorem cfgEntscheidung_wahr {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : Expr D Γ Λ .bool) (σ₀ σ : World D) (ρ : Env D Γ)
    (h : InvariantenOpt.isWahr c = true) :
    InvariantenOpt.holdsBool Ty.bool (eval σ₀ c σ ρ) :=
  InvariantenOpt.isWahrAll_sound c σ₀ σ ρ h

/-- Probe: the checker decides the constantly-true witness condition. -/
theorem probe_cfgEntscheidung :
    InvariantenOpt.isWahr InvariantenOpt.wCond = true :=
  InvariantenOpt.wit_isWahr

/-! ## 3. Executable rewrites and why the `narrow`-else refusal is load-bearing.

    The rewrites return the kept branch VERBATIM: no exit statement
    (`ret`, `leave`, `next`, reason) inside it is touched, so every exit
    edge of the kept branch is preserved by construction, and no call,
    no shared access and no float computation is added, removed or moved.
    The `narrow`-else edge has no such rewrite: an out-of-range value
    genuinely steps to `sonst` (`narrowSonst_erreichbar`), so deleting it
    on "range hope" would drop a source fault -- the DESIGN failure case,
    refused by `cfgVerweigert_narrowSonst`. -/

/-- Executable rewrite: an `ite` on a decided-true condition becomes the
    kept branch, verbatim. -/
def cfgSimpIte {D : Deklaration} {V : Vertrag D} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {l : Bool}
    (_c : Expr D Γ Λ .bool) (t _e : Block D V l Γ Λ Λ') :
    Block D V l Γ Λ Λ' :=
  t

/-- Executable rewrite: a `pruefung` on a decided-true condition drops its
    `else` edge and keeps the body, verbatim. -/
def cfgSimpPruef {D : Deklaration} {V : Vertrag D} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {l : Bool}
    (_c : Expr D Γ Λ .bool) (_sonst : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') :
    Block D V l Γ Λ Λ' :=
  rest

/-- The `ite` rewrite keeps the branch verbatim (exit edges preserved). -/
theorem cfgSimpIte_istKept {D : Deklaration} {V : Vertrag D} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {l : Bool}
    (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ') :
    cfgSimpIte c t e = t :=
  rfl

/-- The `pruefung` rewrite keeps the body verbatim (exit edges preserved). -/
theorem cfgSimpPruef_istKept {D : Deklaration} {V : Vertrag D} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {l : Bool}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') :
    cfgSimpPruef c sonst rest = rest :=
  rfl

/-- A `narrow`-else edge is live in general: an out-of-range value steps
    to `sonst`. Hence no rewrite deletes it, and the certificate gate
    (`keinNarrowSonst`) is load-bearing, not decorative. -/
theorem narrowSonst_erreichbar {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    {lo hi lo' hi' : Int}
    (e : Expr D Γ Λ (.int lo hi)) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hAussen : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    execBlock O passes R (Block.narrow e lo' hi' sonst rest) σ ρ
      = (execEnd O passes R sonst (σ.lese Λ e.orte) ρ).zuAusgang := by
  simp [execBlock, hAussen]

/-! ## 4. Preservation: value, fault, observation.

    The admitted rewrite behaves like the kept branch, jointly:
    the evaluated condition is `true` on both sides (section 2, so
    contracts at their place read the same values from the same
    environments); the `execStmt`/`execBlock` OUTCOME is equal -- same
    constructor, same successor worlds and environments -- so no fault is
    added or removed (`logik`/`hardware` agree, spelled out below), every
    downstream observation agrees (call logs gain no event and lose none:
    the kept branch is verbatim and the deleted edge is unreachable, so
    the same `R` answers the same calls; no shared access is added or
    removed for concurrency -- both sides read `c.orte` once into the same
    post-read world), float values in the kept branch are kernel values
    computed unchanged (section 2), and the step-budget accounting is
    unchanged (same `passes` on both sides; the removed edge never fires,
    so an admitted `CostSummary` bound still covers the fewer blocks).
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard. -/

/-- Deleting the unreachable `else` edge of a decided-true `ite`
    preserves the outcome: the kept branch in the post-read world. -/
theorem cfgIte_bleibt {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hWahr : InvariantenOpt.isWahr c = true) :
    execStmt O passes R (Stmt.ite c t e) σ ρ
      = execBlock O passes R t (σ.lese Λ c.orte) ρ :=
  InvariantenOpt.exec_ite_wahr O passes R c t e σ ρ hWahr

/-- Deleting the unreachable `else` edge of a decided-true `pruefung`
    preserves the outcome: the kept body in the post-read world. -/
theorem cfgPruefung_bleibt {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hWahr : InvariantenOpt.isWahr c = true) :
    execBlock O passes R (Block.pruefung c sonst rest) σ ρ
      = execBlock O passes R rest (σ.lese Λ c.orte) ρ :=
  InvariantenOpt.exec_pruefung_wahr O passes R c sonst rest σ ρ hWahr

/-- Fault preservation, `logik` channel: a logic stop of the kept branch
    is a logic stop of the rewritten `ite`, unchanged. -/
theorem cfgFehler_logik_bleibt {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (e' : Logik D)
    (hWahr : InvariantenOpt.isWahr c = true)
    (h : execBlock O passes R t (σ.lese Λ c.orte) ρ = .logik e') :
    execStmt O passes R (Stmt.ite c t e) σ ρ = .logik e' := by
  rw [cfgIte_bleibt V O passes R c t e σ ρ hWahr]
  exact h

/-- Fault preservation, `hardware` channel: a hardware assumption stop of
    the kept branch is one of the rewritten `ite`, unchanged. -/
theorem cfgFehler_hardware_bleibt {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (e' : Hardware D)
    (hWahr : InvariantenOpt.isWahr c = true)
    (h : execBlock O passes R t (σ.lese Λ c.orte) ρ = .hardware e') :
    execStmt O passes R (Stmt.ite c t e) σ ρ = .hardware e' := by
  rw [cfgIte_bleibt V O passes R c t e σ ρ hWahr]
  exact h

/-! ## 5. Connection: the admitted rewrite behaves like the kept branch.

    The certificate shape is the local rewrite record (`cfgSimpIte` /
    `cfgSimpPruef`, section 3: which edge is deleted, kept branch verbatim)
    PLUS the recomputed analysis citations: `hZul` (all three DESIGN side
    conditions admitted by the decided Bool) and `hBruecke` (the
    `bedingtEntschieden` bit IS the recomputed `isWahr`, never a trusted
    Rust hint). Only decidedness enters the equational proof -- honestly
    so: exit preservation holds by verbatim construction (section 3) and
    the rule never matches a `narrow` (section 3 exhibits the live else);
    both are gates on FIRING via `hZul`, proved by the section-1 refusals.
    Conclusion, jointly: the `ite` outcome equals the kept branch and the
    `pruefung` outcome equals the kept body, each in the post-read world
    with the same environment -- hence same value, same fault channel,
    same downstream observations (contracts at their place, call logs via
    the unchanged `R`, concurrency via the identical `c.orte` read,
    budget via the unchanged `passes`). -/

/-- CONNECTION: an admitted CFG simplification preserves the outcome on
    both the `ite` and the `pruefung` shape. -/
theorem OptCfgSimp_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ')
    (cert : CfgSimpCert)
    (hZul : cfgZulassen cert = true)
    (hBruecke : cert.bedingtEntschieden = InvariantenOpt.isWahr c)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.ite c t e) σ ρ
      = execBlock O passes R t (σ.lese Λ c.orte) ρ
    ∧ execBlock O passes R (Block.pruefung c sonst rest) σ ρ
      = execBlock O passes R rest (σ.lese Λ c.orte) ρ := by
  have hBed : cert.bedingtEntschieden = true := by
    have h := hZul
    simp only [cfgZulassen, Bool.and_eq_true] at h
    exact h.1.1
  have hWahr : InvariantenOpt.isWahr c = true := by
    rw [← hBruecke]
    exact hBed
  exact ⟨cfgIte_bleibt V O passes R c t e σ ρ hWahr,
    cfgPruefung_bleibt V O passes R c sonst rest σ ρ hWahr⟩

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptCfgSimp_verbindung` instantiated JOINTLY:
    the constantly-true condition under an `ite` with `nil` branches and
    a `pruefung` with a `leave` else and a `nil` body, admitted by the
    all-true certificate whose decided bit is the recomputation (`rfl`),
    in the NON-DEGENERATE reference program `refD` (whose `einzahlen`
    writes its table, `refEin_schreibt`), beside the reached F-machine
    run `MB` that changes memory (`refB_erreicht`, `refB_schreibt`:
    slot `0` changes against the start world). -/

/-- JOINT WITNESS for `OptCfgSimp_verbindung`: decided-true edges drop
    on `refD`, beside the memory-changing reached run. -/
theorem OptCfgSimp_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ Λ' : List (Res refD)) (l : Bool)
      (c : Expr refD Γ Λ .bool) (t e : Block refD V l Γ Λ Λ')
      (sonst : Endblock refD V l Γ Λ) (rest : Block refD V l Γ Λ Λ')
      (cert : CfgSimpCert)
      (_hZul : cfgZulassen cert = true)
      (_hBruecke : cert.bedingtEntschieden = InvariantenOpt.isWahr c)
      (σ : World refD) (ρ : Env refD Γ),
      execStmt O passes R (Stmt.ite c t e) σ ρ
        = execBlock O passes R t (σ.lese Λ c.orte) ρ
      ∧ execBlock O passes R (Block.pruefung c sonst rest) σ ρ
        = execBlock O passes R rest (σ.lese Λ c.orte) ρ
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptCfgSimp_verbindung (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf)
    (c := (Expr.wahr : Expr refD [] [] .bool))
    (t := (Block.nil : Block refD (vertragVon refD refEin) true [] [] []))
    (e := (Block.nil : Block refD (vertragVon refD refEin) true [] [] []))
    (sonst := (Endblock.leave rfl :
      Endblock refD (vertragVon refD refEin) true [] []))
    (rest := (Block.nil : Block refD (vertragVon refD refEin) true [] [] []))
    (cert := (⟨true, true, true⟩ : CfgSimpCert))
    (hZul := by decide) (hBruecke := rfl)
    (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], [], true,
    (Expr.wahr : Expr refD [] [] .bool), Block.nil, Block.nil,
    Endblock.leave rfl, Block.nil, ⟨true, true, true⟩, by decide, rfl,
    refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No block-map checker: `austrittErhalten`/`keinNarrowSonst` are
      carried as checked data gated by `cfgZulassen` (section-1 refusals);
      the validator's recomputation (re-decided `isWahr`, exit-edge walk,
      dominators, avail/liveness per IR-VALIDIERUNG layer B) is the
      consumer side and stays OPEN here, as does the shared SCFG/block-map
      vocabulary (lane 287).
    - No `narrow`-else rewrite: there is deliberately NO theorem deleting
      a `narrow` else; `narrowSonst_erreichbar` exhibits the live edge
      that justifies the refusal.
    - No totalCost/budget-transfer inequality: both sides share the same
      `passes` and the removed edge never fires, so an admitted
      `CostSummary` bound still covers the fewer blocks; the formal
      level-(c) machine-work bound is OPEN per IR-VALIDIERUNG (lane 278).
    - No call-log (`FolgeG`) or TSO/GX concurrency leg: no call and no
      shared access is added or removed (kept branch verbatim, same `R`,
      identical `c.orte` read), but the whole-unit legs stay OPEN.
    - No silicon correspondence, no ABI/loader claim: correspondence stops
      at source `eval`/`execStmt`/`execBlock` outcomes and kernel
      boolean truth; per-access refinement into W/GX is OPEN.
-/

#print axioms cfgZulassen
#print axioms cfgVerweigert_unentschieden
#print axioms cfgVerweigert_austritt
#print axioms cfgVerweigert_narrowSonst
#print axioms cfgEntscheidung_wahr
#print axioms cfgSimpIte_istKept
#print axioms cfgSimpPruef_istKept
#print axioms narrowSonst_erreichbar
#print axioms cfgIte_bleibt
#print axioms cfgPruefung_bleibt
#print axioms cfgFehler_logik_bleibt
#print axioms cfgFehler_hardware_bleibt
#print axioms OptCfgSimp_verbindung
#print axioms OptCfgSimp_verbindung_zeuge

end Gabbro.Grammatik.X86
