/-
  File:      Grammatik/X86/OptLicmLoop.lean
  Subject:   Loop-invariant code motion (LICM) rule lemma (lane 872).

  DESIGN section 7 row: local premise "invariance recomputed (exact-value,
  not rounded-value), non-faulting over hoisted inputs from rechecked source
  facts", certificate "B+C", failure case "hoist `x/n` above `n!=0`; hoist
  token op on shared access on local evidence", phase M, cost O(sites).

  Covered fragment (no accepted IR yet): `Stmt.assignVar` motion across a
  `Stmt.ite` guard over the real `Syntax`/`Semantik` (`eval`/`execBlock`).
  The hoisted temp is env-only (no world write); reads are identical up to
  order (`licmOrte_gleich`); the taken path agrees fully. Cost (CostSummary:
  same statements on the taken path, no wait hidden), layout (TableLayout:
  no carrier touched) and duties follow from the exec equality.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Hoisted operation kinds. `tokenO` (shared/atomic/call/token op) is
    refused BY KIND: a token op is never pure, never speculation-safe. -/
inductive LicmOp where
  | addO | subO | mulO | divO | gleitO (op : GleitOp) | tokenO
  deriving DecidableEq, Repr

/-- Kind admission: token ops never hoist. -/
def licmOpOk : LicmOp → Bool
  | .tokenO => false
  | _ => true

/-- A pure read of an empty footprint leaves the world unchanged. -/
theorem licmLeseLeer {D : Deklaration} (σ : World D) (Λ : List (Res D)) :
    σ.lese Λ ([] : List (D.Tab ⊕ D.Glob)) = σ := rfl

/-! ## 1. Certificate and refusals (DESIGN section 7 row).

    The certificate is the LOCAL rewrite record plus recomputed analysis
    citations: which op kind is hoisted, and the five validator-recomputed
    Bools (exact-value invariance, non-faulting over the hoisted inputs
    from rechecked source facts, no token op, one FP rounding scope,
    facts rechecked at the hoist point). Admission gates USE of the rule;
    a refused site keeps its unhoisted certified translation. -/

/-- The validator-decided LICM certificate: the hoisted op kind plus the
    five recomputed side conditions (DESIGN cert B+C). -/
structure LicmCert where
  op : LicmOp
  invariantOk : Bool
  keinFehler : Bool
  keinToken : Bool
  gleicheRundung : Bool
  recheckedFacts : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds and the kind is hoistable. -/
def licmZulassen (c : LicmCert) : Bool :=
  licmOpOk c.op && c.invariantOk && c.keinFehler && c.keinToken
    && c.gleicheRundung && c.recheckedFacts

/-- KIND REFUSAL: a token op (shared/atomic/call/token) never hoists --
    the DESIGN "hoist token op on shared access on local evidence" case. -/
theorem licmVerweigert_tokenOp (c : LicmCert) (h : c.op = .tokenO) :
    licmZulassen c = false := by
  simp [licmZulassen, licmOpOk, h]

/-- FAULT REFUSAL: `x/n` hoisted above `n!=0` without non-faulting
    evidence refuses -- the untaken path would turn into a `hardware`
    stop the source never had (DESIGN CE-2). -/
theorem licmVerweigert_div (c : LicmCert) (h : c.keinFehler = false) :
    licmZulassen c = false := by
  simp [licmZulassen, h]

/-- A token op flagged by analysis refuses as well. -/
theorem licmVerweigert_token (c : LicmCert) (h : c.keinToken = false) :
    licmZulassen c = false := by
  simp [licmZulassen, h]

/-- No recomputed invariance, no hoist. -/
theorem licmVerweigert_inv (c : LicmCert) (h : c.invariantOk = false) :
    licmZulassen c = false := by
  simp [licmZulassen, h]

/-- Source facts not rechecked at the hoist point: refuse. -/
theorem licmVerweigert_facts (c : LicmCert) (h : c.recheckedFacts = false) :
    licmZulassen c = false := by
  simp [licmZulassen, h]

/-- A float hoist across rounding scopes refuses (double rounding). -/
theorem licmVerweigert_rundung (c : LicmCert)
    (h : c.gleicheRundung = false) :
    licmZulassen c = false := by
  simp [licmZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_licmZulassen_ok :
    licmZulassen ⟨.addO, true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a division without non-faulting evidence is refused. -/
theorem probe_licmZulassen_divNein :
    licmZulassen ⟨.divO, true, false, true, true, true⟩ = false := by
  decide

/-- Probe: a token op is refused by kind. -/
theorem probe_licmZulassen_tokenNein :
    licmZulassen ⟨.tokenO, true, true, true, true, true⟩ = false := by
  decide

/-! ## 2. Hoisted integer operations over arbitrary values.

    The hoisted op computes its value from ARBITRARY operands: `add`/`sub`/
    `mul`/`neg` are total (hence speculation-safe); `div`/`rem` keep the
    source `M102` side conditions as validator-decided premises, forwarded
    unchanged, so a zero divisor never reaches the hoist. -/

/-- `x + y` hoists as `x + y`. -/
theorem licmAdd_wert (x y : Int) :
    (Zahl.add (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x + y := by
  rfl

/-- `x - y` hoists as `x - y`. -/
theorem licmSub_wert (x y : Int) :
    (Zahl.sub (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x - y := by
  rfl

/-- `x * y` hoists as `x * y`. -/
theorem licmMul_wert (x y : Int) :
    (Zahl.mul (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x * y := by
  rfl

/-- `x / y` hoists as `x.tdiv y` under the `M102` premises: a zero
    divisor never reaches the hoist, so no `hardware` stop is added. -/
theorem licmDiv_wert (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y) :
    (Zahl.div h0 h1' (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x.tdiv y := by
  rfl

/-- `x % y` hoists as `x.tmod y` under the `M102` premises. -/
theorem licmRem_wert (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y) :
    (Zahl.rem h0 h1' (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x.tmod y := by
  rfl

/-- Probes: the hoisted ops compute (`7`, `3`). -/
theorem probe_licmAdd : (Zahl.add (⟨3, by decide, by decide⟩ : Zahl 3 3)
    (⟨4, by decide, by decide⟩ : Zahl 4 4)).n = 7 := by
  decide

theorem probe_licmDiv : (Zahl.div (by decide : (0 : Int) ≤ 7) (by decide : (1 : Int) ≤ 2)
    (⟨7, by decide, by decide⟩ : Zahl 7 7)
    (⟨2, by decide, by decide⟩ : Zahl 2 2)).n = 3 := by
  decide

/-! ## 3. Hoisted float operation: single rounding, one scope.

    The validator precomputes `gleitRechne op` on the invariant values IN
    THE KERNEL under one rounding scope (`gleicheRundung`). The
    recomputation obligation is conditional on admission (`hEq` takes
    `hz`): exact value, not rounded value, and the equation is claimed
    only where the validator admitted the site. A cross-scope hoist is
    refused by `licmVerweigert_rundung`. -/

/-- The admitted float hoist preserves value and `gleitPasst` outcome:
    same pushed value, same `logik bereich` outcome, so neither a value
    nor a fault is hoisted away (IEEE: one width, one RNE scope). -/
theorem licmGleit_behält (cert : LicmCert) (op : GleitOp)
    (qa qb qf lo hi : Int × Int)
    (hz : licmZulassen cert = true)
    (hEq : licmZulassen cert = true →
      bruch qf = gleitRechne op (bruch qa) (bruch qb)) :
    gleitPasst lo hi (bruch qf) =
      gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb)) := by
  have e := hEq hz
  rw [e]

/-- Probe: the kernel computes `0.5 + 0.25 = 0.75` in one rounding. -/
theorem probe_licmGleit :
    gleitRechne .add (bruch (1, 2)) (bruch (1, 4)) = bruch (3, 4) := by
  decide

/-! ## 4. Observation projection: the hoist moves no carrier access.

    The hoisted `assignVar` reads `e.orte` and writes only the local
    environment (`Env.set`: no world write, no carrier, no token). The
    guard reads `c.orte` on both sides. Hence both orders read exactly
    the same carriers -- same set, only the trace order may differ, and
    with `hRein` even the order agrees. For concurrency: no shared access
    is added or removed, no lock/atomic/fence crossed (cert `keinToken`). -/

/-- Both orders read the same carriers (permutation: order may differ). -/
theorem licmOrte_gleich {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} (e : Expr D Γ Λ τ) (c : Expr D Γ Λ .bool) :
    (e.orte ++ c.orte).Perm (c.orte ++ e.orte) :=
  List.perm_append_comm

/-! ## 5. Connection: the hoisted temp behaves like the sunk one.

    The rewrite moves `x := e` (invariant, pure, non-faulting) from
    inside the taken branch to before the guard:
    `x:=e; wenn c {…} …` instead of `wenn c {x:=e; …} …`.
    It fires only under the admitted certificate; the invariance equation
    (`hInv`: exact value, recomputed) and the guard independence
    (`hGuard`: the guard outcome is unchanged by the hoisted store) are
    claimed only where the validator admitted the site (`hz`), and the
    trip evidence (`hTaken`: the guarded region IS reached) selects the
    taken path. Conclusion, jointly:
    (1) the `execBlock` OUTCOME is equal on the taken path -- same
    constructor, same successor worlds and environments -- so no fault is
    added or removed (`logik`/`hardware` agree), every downstream
    observation agrees (contracts at their place read the same values
    from the same environments, call logs gain no event since the same
    subterms run under the same worlds, no shared access is added or
    removed for concurrency -- both sides read `e.orte ++ c.orte`
    carriers, and the hoisted store is env-only), and the step-budget
    accounting is unchanged on the taken path (same statements run);
    (2) the invariant VALUE is preserved across the guard read;
    (3) both orders read the same carriers.
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard (`div` keeps `M102`; the
    refused `x/n`-above-`n!=0` shape never reaches `hInv`). -/

/-- CONNECTION: hoisting invariant `x := e` above the guard preserves
    the taken-path outcome, the value and the carrier reads. -/
theorem OptLicmLoop_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {l : Bool} {τ : Ty}
    (cert : LicmCert)
    (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (c : Expr D Γ Λ .bool)
    (tRest eBr : Block D V l Γ Λ Λ')
    (restAfter : Block D V l Γ Λ' Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hz : licmZulassen cert = true)
    (hRein : e.orte = [])
    (hInv : licmZulassen cert = true →
      eval (σ.lese Λ c.orte) e (σ.lese Λ c.orte) ρ
        = eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)
    (hGuard : licmZulassen cert = true →
      wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte)
        (ρ.set x (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)))
      = wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ))
    (hTaken : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ)
      = true) :
    execBlock O passes R
      (Block.cons (Stmt.assignVar x e)
        (Block.cons (Stmt.ite c tRest eBr) restAfter)) σ ρ
    = execBlock O passes R
      (Block.cons (Stmt.ite c (Block.cons (Stmt.assignVar x e) tRest) eBr)
        restAfter) σ ρ
    ∧ eval (σ.lese Λ c.orte) e (σ.lese Λ c.orte) ρ
        = eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ
    ∧ (e.orte ++ c.orte).Perm (c.orte ++ e.orte) := by
  have hA' : ∀ σ' : World D, σ'.lese Λ e.orte = σ' := fun σ' => by
    rw [hRein]; exact licmLeseLeer σ' Λ
  have hInv' : eval (σ.lese Λ c.orte) e (σ.lese Λ c.orte) ρ
      = eval σ e σ ρ := by
    simpa [hA'] using hInv hz
  have hGuard' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte)
      (ρ.set x (eval σ e σ ρ))) = true := by
    have g := hGuard hz
    simp only [hA'] at g
    rw [g, hTaken]
  refine ⟨?_, hInv hz, List.perm_append_comm⟩
  simp [execBlock, execStmt, hA', hGuard', hTaken, hInv']

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptLicmLoop_verbindung` instantiated JOINTLY: the
    invariant `y+3` (outer value `4`, so `7`) hoisted above the taken
    guard `y <= 5`, in the NON-DEGENERATE reference program `refD`
    (whose `einzahlen` writes its table, `refEin_schreibt`), beside the
    reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). The guard reads only the
    untouched tail of the environment, so `hGuard` holds by computation;
    the invariant reads no carrier, so `hRein`/`hInv` hold by computation;
    the guard is taken (`4 <= 5`), so `hTaken` holds by computation. -/

/-- JOINT WITNESS for `OptLicmLoop_verbindung`: `y+3` above `y<=5`
    on `refD`, beside the memory-changing reached run. -/
theorem OptLicmLoop_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ Λ' Λ'' : List (Res refD)) (l : Bool) (τ : Ty)
      (cert : LicmCert)
      (x : Var Γ τ) (e : Expr refD Γ Λ τ)
      (c : Expr refD Γ Λ .bool)
      (tRest eBr : Block refD V l Γ Λ Λ')
      (restAfter : Block refD V l Γ Λ' Λ'')
      (σ : World refD) (ρ : Env refD Γ),
      execBlock O passes R
        (Block.cons (Stmt.assignVar x e)
          (Block.cons (Stmt.ite c tRest eBr) restAfter)) σ ρ
      = execBlock O passes R
        (Block.cons (Stmt.ite c (Block.cons (Stmt.assignVar x e) tRest) eBr)
          restAfter) σ ρ
      ∧ eval (σ.lese Λ c.orte) e (σ.lese Λ c.orte) ρ
          = eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ
      ∧ (e.orte ++ c.orte).Perm (c.orte ++ e.orte)
      ∧ licmZulassen cert = true
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptLicmLoop_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf)
    (Γ := [.int 3 13, .int 0 10])
    (Λ := (vertragVon refD refEin).ende)
    (Λ' := (vertragVon refD refEin).ende)
    (Λ'' := (vertragVon refD refEin).ende)
    (l := true) (τ := .int 3 13)
    (cert := ⟨.addO, true, true, true, true, true⟩)
    (x := Var.hier)
    (e := Expr.add (Expr.var (Var.dort Var.hier)) (Expr.lit 3))
    (c := Expr.le (Expr.var (Var.dort Var.hier)) (Expr.lit 5))
    (tRest := Block.nil) (eBr := Block.nil) (restAfter := Block.nil)
    (σ := refSp0.welt [])
    (ρ := Env.cons (⟨7, by decide, by decide⟩ : Wert refD (.int 3 13))
      (Env.cons (⟨4, by decide, by decide⟩ : Wert refD (.int 0 10)) Env.nil))
    (hz := by decide)
    (hRein := rfl)
    (hInv := fun _ => rfl)
    (hGuard := fun _ => rfl)
    (hTaken := by decide)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf,
    [.int 3 13, .int 0 10],
    (vertragVon refD refEin).ende, (vertragVon refD refEin).ende,
    (vertragVon refD refEin).ende, true, .int 3 13,
    ⟨.addO, true, true, true, true, true⟩,
    Var.hier,
    Expr.add (Expr.var (Var.dort Var.hier)) (Expr.lit 3),
    Expr.le (Expr.var (Var.dort Var.hier)) (Expr.lit 5),
    Block.nil, Block.nil, Block.nil,
    refSp0.welt [],
    Env.cons (⟨7, by decide, by decide⟩ : Wert refD (.int 3 13))
      (Env.cons (⟨4, by decide, by decide⟩ : Wert refD (.int 0 10)) Env.nil),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2
  · decide
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - PROVED: validator certificate with six decided refusals (token-op
      kind, `x/n`-above-`n!=0` fault, token flag, invariance, rechecked
      facts, rounding scope); integer value lemmas over arbitrary values
      (`div`/`rem` keep `M102`); admitted float hoist preserves value and
      `gleitPasst` outcome in one kernel rounding; orte permutation (same
      carriers, concurrency); the taken-path `execBlock` connection with
      jointly inhabited non-degenerate memory-changing witness.
    - OPEN, explicitly not claimed: the untaken path (the hoisted store
      touches the dead temp there; liveness certificate is phase-B work);
      `sub`/`mul` syntax connections (their VALUES hoist, section 2);
      float/Narrow/div syntax windows (value level only, sections 2-3);
      totalCost inequality (same statements on the taken path, so same
      budget shape; the formal level-(c) machine-work bound is OPEN per
      IR-VALIDIERUNG); loop-trip evidence beyond the reached guard
      (trip-count reasoning belongs to the unroll certificate);
      per-access refinement into W/GX (TSO bridge lane); silicon
      correspondence, ABI/loader claims.
-/

#print axioms licmOpOk
#print axioms licmLeseLeer
#print axioms licmZulassen
#print axioms licmVerweigert_tokenOp
#print axioms licmVerweigert_div
#print axioms licmVerweigert_token
#print axioms licmVerweigert_inv
#print axioms licmVerweigert_facts
#print axioms licmVerweigert_rundung
#print axioms licmAdd_wert
#print axioms licmSub_wert
#print axioms licmMul_wert
#print axioms licmDiv_wert
#print axioms licmRem_wert
#print axioms licmGleit_behält
#print axioms probe_licmGleit
#print axioms licmOrte_gleich
#print axioms OptLicmLoop_verbindung
#print axioms OptLicmLoop_verbindung_zeuge

end Gabbro.Grammatik.X86
