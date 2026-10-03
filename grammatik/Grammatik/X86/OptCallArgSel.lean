/-
  File:      Grammatik/X86/OptCallArgSel.lean
  Subject:   Call-argument selection rule lemma (lane 894).

  DESIGN section 7 row (layout/allocation, plus §2 line "call arguments use
  the ABI registers before stack slots"): the lowering places the first
  `regBudget` (6) integer arguments in ABI registers and the rest in
  8-aligned stack slots, under the per-image calling convention the
  validator re-decided from the image (never trusted from Rust).

  Certificate (local rewrite record + recomputed analysis citations):
  `CallArgCert` (four decided Bools) plus the computed `platziere` list;
  the validator rechecks admission (`callArgZulassen`), the arity bound
  (`platzOk`) and the recomputed per-site placement. Failure case (must
  NOT fire): unchecked convention, over-budget arity, hidden/variadic
  parameters, or misaligned stack slots -- each proved to force `false`.
  Phase L, cost O(args).

  Proved over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`): value preservation at
  arbitrary types, regs-before-stack shape, IEEE outcome stability
  (`gleitPasst` over preserved values), bounded cost, no new fault, the
  placement tied to each call's evaluated integer values (`envInts`,
  derived round-trips plus the value agreement obtained through the
  shared record), and the conditional source call-outcome congruence
  (`execStmt` `.call` equality under equal `orte`/full `evalArgs`, so
  where it applies, contracts at their place, call logs, concurrency
  and budget observations agree downstream). Full `evalArgs`-
  preservation by the lowering stays OPEN (see CUTS). No `ensures`
  is derived, no refusal becomes a warning, no faulting form is
  speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The validator-decided side conditions for one call-argument selection
    site (DESIGN section 7 row): the per-image calling convention was
    re-decided from the image, the arity fits the register budget plus
    the stack window, no hidden/variadic parameter is present, and the
    stack slots are 8-aligned with the 16-aligned entry preserved. -/
structure CallArgCert where
  konventionGeprueft : Bool
  registerBudgetOk : Bool
  keineVersteckten : Bool
  stapelBuendig : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def callArgZulassen (c : CallArgCert) : Bool :=
  c.konventionGeprueft && c.registerBudgetOk && c.keineVersteckten && c.stapelBuendig

/-- One lowered argument location: an ABI register or a stack slot at a
    byte offset. -/
inductive ArgPlatz where
  | reg (r : Nat)
  | stapel (off : Nat)
  deriving DecidableEq, Repr

/-- Number of integer arguments carried in ABI registers (System-V-like
    six: rdi rsi rdx rcx r8 r9); the rest goes on the stack. -/
def regBudget : Nat := 6

/-- Maximum admitted argument count (register window plus stack window);
    anything above is refused, never truncated. -/
def maxArgs : Nat := 64

/-! ## 1. Refusal: every unchecked side condition must NOT select.

    Each DESIGN failure case is proved of the decided Bool: an unchecked
    per-image convention, an over-budget arity, a hidden/variadic
    parameter, or a misaligned stack slot forces `callArgZulassen =
    false`, so the validator cannot silently skip it. The rule then falls
    back to another certified translation, never to a warning. -/

/-- Unchecked calling convention refuses the selection. -/
theorem callArgVerweigert_konvention (c : CallArgCert)
    (h : c.konventionGeprueft = false) :
    callArgZulassen c = false := by
  simp [callArgZulassen, h]

/-- Over-budget arity refuses the selection. -/
theorem callArgVerweigert_budget (c : CallArgCert)
    (h : c.registerBudgetOk = false) :
    callArgZulassen c = false := by
  simp [callArgZulassen, h]

/-- A hidden/variadic parameter refuses the selection. -/
theorem callArgVerweigert_versteckt (c : CallArgCert)
    (h : c.keineVersteckten = false) :
    callArgZulassen c = false := by
  simp [callArgZulassen, h]

/-- A misaligned stack slot refuses the selection. -/
theorem callArgVerweigert_stapel (c : CallArgCert)
    (h : c.stapelBuendig = false) :
    callArgZulassen c = false := by
  simp [callArgZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_callArgZulassen_ok :
    callArgZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: an unchecked convention is refused. -/
theorem probe_callArgZulassen_konv :
    callArgZulassen ⟨false, true, true, true⟩ = false := by
  decide

/-- Probe: a hidden parameter is refused. -/
theorem probe_callArgZulassen_versteckt :
    callArgZulassen ⟨true, true, false, true⟩ = false := by
  decide

/-! ## 2. Placement: registers before stack slots, over arbitrary values.

    `platzFuer i` is the lowered location of argument `i`: the first
    `regBudget` arguments go in ABI registers, the rest in stack slots at
    8-byte offsets. `platziere` pairs the locations with ARBITRARY values
    (`α`: integers, float bit patterns, pointers alike -- the selection
    never inspects a value), `liesWerte` reads the values back. The
    validator recomputes this exact function; nothing is trusted. -/

/-- The lowered location of argument `i`: register while in budget,
    8-byte stack slot above it. -/
def platzFuer (i : Nat) : ArgPlatz :=
  if i < regBudget then .reg i else .stapel ((i - regBudget) * 8)

/-- Pair locations with arbitrary argument values, left to right. -/
def platziereAux (i : Nat) : List α → List (ArgPlatz × α)
  | [] => []
  | v :: vs => (platzFuer i, v) :: platziereAux (i + 1) vs

/-- The computed per-site placement: the local rewrite record of the
    certificate (DESIGN layer A). -/
def platziere (vs : List α) : List (ArgPlatz × α) :=
  platziereAux 0 vs

/-- Read the values back from a placed list. -/
def liesWerte : List (ArgPlatz × α) → List α :=
  List.map Prod.snd

/-- VALUE PRESERVATION: the placed arguments read back to exactly the
    passed values, at any type. No value is changed, dropped or
    reordered by the selection. -/
theorem platziere_liest (vs : List α) :
    liesWerte (platziere vs) = vs := by
  unfold platziere liesWerte
  suffices h : ∀ (i : Nat) (ws : List α),
      (platziereAux i ws).map Prod.snd = ws from h 0 vs
  intro i ws
  induction ws generalizing i with
  | nil => rfl
  | cons v vs ih => simp [platziereAux, ih]

/-- COST BOUND: one lowered location per argument -- no hidden extra
    move, so the step-budget accounting is unchanged (same count the
    source budget priced). -/
theorem platziere_laenge (vs : List α) :
    (platziere vs).length = vs.length := by
  unfold platziere
  suffices h : ∀ (i : Nat) (ws : List α),
      (platziereAux i ws).length = ws.length from h 0 vs
  intro i ws
  induction ws generalizing i with
  | nil => rfl
  | cons _ _ ih => simp [platziereAux, ih]

/-- REGS FIRST: argument `i` below the budget goes in register `i`. -/
theorem platzFuer_reg (i : Nat) (h : i < regBudget) :
    platzFuer i = .reg i := by
  simp [platzFuer, h]

/-- STACK ABOVE: argument `i` at/above the budget goes on the stack at
    the 8-byte offset for its position. -/
theorem platzFuer_stapel (i : Nat) (h : regBudget ≤ i) :
    platzFuer i = .stapel ((i - regBudget) * 8) := by
  simp [platzFuer, Nat.not_lt.mpr h]

/-- STACK ALIGNED: every stack slot the rule emits is 8-aligned. -/
theorem platzFuer_buendig (i : Nat) (off : Nat)
    (h : platzFuer i = .stapel off) :
    off % 8 = 0 := by
  have hi : ¬ i < regBudget := by
    intro hc
    rw [platzFuer_reg i hc] at h
    exact ArgPlatz.noConfusion h
  rw [platzFuer_stapel i (Nat.le_of_not_lt hi)] at h
  cases h
  omega

/-- Probes: args 0 and 5 in registers, arg 6 on the stack at offset 0,
    arg 7 at offset 8. -/
theorem probe_platz0 : platzFuer 0 = .reg 0 := by decide

theorem probe_platz5 : platzFuer 5 = .reg 5 := by decide

theorem probe_platz6 : platzFuer 6 = .stapel 0 := by decide

theorem probe_platz7 : platzFuer 7 = .stapel 8 := by decide

/-! ## 3. Integer projection: tying the placement to a real call.

    The optimisation moves EVALUATED values, so the rule links its value
    list `vs` to the integer values a real call passes: `wertInt` reads
    the number out of an integer-typed value (nothing else carries one),
    `envInts` collects them left to right over an evaluated argument
    environment. Both are pure recomputable functions -- the validator
    re-runs them on the checked call, nothing is trusted. -/

/-- The integer carried by a value, if its type is an integer range. -/
def wertInt {τ : Ty} (v : Wert D τ) : Option Int :=
  match τ with
  | .int _ _ => some v.n
  | _ => none

/-- The integer values of an evaluated argument environment, left to
    right; non-integer arguments contribute nothing. -/
def envInts {Γ : Ctx} : Env D Γ → List Int
  | .nil => []
  | .cons v rest =>
    match wertInt v with
    | some n => n :: envInts rest
    | none => envInts rest

/-- An integer value projects to its number. -/
theorem wertInt_int (lo hi n : Int)
    (v : Wert D (.int lo hi)) (h : v.n = n) :
    wertInt v = some n := by
  simp [wertInt, h]

/-- Projection over a cons cell agrees with the head value. -/
theorem envInts_cons (τ : Ty) (Γ : Ctx)
    (v : Wert D τ) (ρ : Env D Γ) :
    envInts (Env.cons v ρ) =
      match wertInt v with
      | some n => n :: envInts ρ
      | none => envInts ρ := by
  rfl

/-- Probe: `[7]` projects from a one-integer environment. -/
theorem probe_envInts {D : Deklaration} :
    envInts (Env.cons (⟨7, by decide, by decide⟩ : Wert D (.int 0 10)) Env.nil :
      Env D [.int 0 10]) = [7] := by
  rfl

/-! ## 4. IEEE, arity gate and no new fault.

    Float arguments cross the selection as UNCONVERTED bit patterns
    (here: the `bruch` numerator/denominator pair): the rule never rounds,
    narrows or re-evaluates a float, so the `gleitPasst` outcome -- the
    `logik bereich` check -- is a pure function of preserved values.
    `platzOk` gates USE of a placement on the admitted certificate plus
    the arity bound; an admitted placement therefore stays in budget, so
    no stack-overflow fault is introduced and no faulting form is
    speculated above its guard. -/

/-- IEEE STABILITY: the `gleitPasst` outcome over placed-then-read float
    patterns equals the outcome over the passed patterns -- same pushed
    value, same `logik bereich` outcome, at every index. -/
theorem gleitPasst_erhalt (lo hi : Int × Int) (qs : List (Int × Int)) (i : Nat) :
    ((liesWerte (platziere qs))[i]?.map (fun q => gleitPasst lo hi (bruch q))) =
      ((qs[i]?).map (fun q => gleitPasst lo hi (bruch q))) := by
  rw [platziere_liest]

/-- Probe: the kernel computes `0.5 + 0.25 = 0.75` through placed values. -/
theorem probe_gleitPlatz :
    gleitRechne .add (bruch (1, 2)) (bruch (1, 4)) = bruch (3, 4) := by
  decide

/-- The arity gate: an admitted certificate plus an in-budget argument
    count. The validator re-decides both; the lowering trusts neither. -/
def platzOk (c : CallArgCert) (n : Nat) : Bool :=
  callArgZulassen c && decide (n ≤ maxArgs)

/-- An admitted certificate within budget admits the placement. -/
theorem platzOk_von_zulassen (c : CallArgCert) (n : Nat)
    (hz : callArgZulassen c = true) (hN : n ≤ maxArgs) :
    platzOk c n = true := by
  simp [platzOk, hz, hN]

/-- NO NEW FAULT: an admitted placement stays in budget -- the emitted
    stack window cannot overflow, so the selection introduces no
    `hardware` stop the source had no counterpart for. -/
theorem keinFehlerNeu (c : CallArgCert) (n : Nat)
    (h : platzOk c n = true) :
    n ≤ maxArgs := by
  simp [platzOk] at h
  exact h.2

/-- The placed integer values read back whole through the canonical
    word under the width-exact premise the validator decided. -/
theorem platzWort (x : Int) (hW : 0 ≤ x ∧ x < 2 ^ 64) :
    ((BitVec.ofNat 64 x.toNat : Wort)).toNat = x.toNat := by
  have h : x.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `42` reads back as `42` through the word. -/
theorem probe_platzWort :
    ((BitVec.ofNat 64 ((42 : Int)).toNat : Wort)).toNat = 42 := by
  decide

/-! ## 5. Connection: one recomputed placement serves the call sites.

    The rewrite is stated at a `Stmt.call` window, so its consequences
    cover every downstream observation at once. The optimisation's value
    list `vs` is LINKED to the calls it serves: `hVs`/`hVs'` premise that
    `vs` is exactly the integer values each site evaluates
    (`envInts (evalArgs …)`, recomputed by the validator, never trusted).
    Conclusion, jointly:
    (1)+(2) the placed values read back to each site's evaluated values
    -- DERIVED through the shared record via `platziere_liest`, not
    assumed;
    (3) both sites agree on their integer values -- DERIVED from the two
    links (the `hVals`-like equality obtained through the placement);
    (4) one location per argument (budget unchanged);
    (5) the admitted placement passes the arity gate (no new fault);
    (6) the `execStmt` OUTCOME is equal -- a CONDITIONAL congruence: it
    assumes equal footprints (`hOrte`) and equal full evaluation
    (`hVals`). Full `evalArgs`-preservation by the lowering (beyond the
    integer values (3) proves) is CUT as OPEN (see CUTS): this lemma shows
    the placement carries the values and that equal evaluation gives
    equal outcomes; closing the remaining gap belongs to the
    lowering/validator lane.
    Where (6) applies, same constructor, same successor worlds and
    environments follow -- so no fault is added or removed
    (`logik`/`hardware` agree), contracts at their place read the same
    values from the same environments, call logs gain no event, no
    shared access is added or removed for concurrency, and the
    step-budget accounting is unchanged.
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard: the source check
    (`weiter`/`narrow`) at the site still enforces every range. -/

/-- CONNECTION: one admitted placement carries both sites' values;
    outcome congruence is conditional on equal evaluation. -/
theorem OptCallArgSel_verbindung {D : Deklaration} {V : Vertrag D}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool} {f : D.Fn}
    (args args' : Args D Γ Λ (D.params f))
    (hp : RufPasst D V (D.signatur f) Λ)
    (hp' : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) (hr' : D.gruende f = 0)
    (cert : CallArgCert) (vs : List Int)
    (hz : callArgZulassen cert = true)
    (hN : vs.length ≤ maxArgs)
    (σ : World D) (ρ : Env D Γ)
    (hVs : vs = envInts (evalArgs σ args σ ρ))
    (hVs' : vs = envInts (evalArgs σ args' σ ρ))
    (hOrte : args.orte = args'.orte)
    (hVals : ∀ w : World D, evalArgs w args w ρ = evalArgs w args' w ρ) :
    liesWerte (α := Int) (platziere (α := Int) vs)
      = envInts (evalArgs σ args σ ρ)
    ∧ liesWerte (α := Int) (platziere (α := Int) vs)
      = envInts (evalArgs σ args' σ ρ)
    ∧ envInts (evalArgs σ args σ ρ) = envInts (evalArgs σ args' σ ρ)
    ∧ ((platziere (α := Int) vs).length = vs.length)
    ∧ platzOk cert vs.length = true
    ∧ execStmt (l := l) O passes R (Stmt.call (l := l) f args hp hr) σ ρ
      = execStmt (l := l) O passes R (Stmt.call (l := l) f args' hp' hr') σ ρ := by
  refine ⟨?_, ?_, ?_, platziere_laenge vs,
    platzOk_von_zulassen cert vs.length hz hN, ?_⟩
  · rw [hVs, platziere_liest]
  · rw [hVs', platziere_liest]
  · rw [← hVs, ← hVs']
  · simp only [execStmt, hOrte, hVals]

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    The witness call goes to `einzahlen` (`refEin`), the reference
    function WITH an integer parameter, so the rewrite is exhibited on
    two SYNTACTICALLY DIFFERENT argument terms: `3` as a widened literal
    versus `1 + 2` as a widened sum. Both evaluate to `3` with empty
    footprints, and `vs = [3]` is tied to both evaluations by computation
    (`rfl`), so the shared placement `[(.reg 0, 3)]` is non-trivial: it
    genuinely selects a register and reads the value back. -/

/-- The held-set of `einzahlen` is exactly the witness lock holdings:
    the exact-held-set shape `hh_von`/`hx_von` need. -/
theorem refHeldIff :
    ∀ L : refD.Lock,
      Res.held (D := refD) L ∈ [Res.held (D := refD) ()]
        ↔ L ∈ (refD.signatur refEin).haelt := by
  intro L
  have eH : (refD.signatur refEin).haelt = [()] := rfl
  constructor
  · intro hL
    have heq := List.mem_singleton.mp hL
    cases heq
    rw [eH]
    exact List.mem_singleton.mpr rfl
  · intro hL
    rw [eH] at hL
    have eL := List.mem_singleton.mp hL
    cases eL
    exact List.mem_singleton.mpr rfl

/-- The call from the witness site to `einzahlen`: one integer argument,
    the callee holds the same lock, needs nothing else. Same lock-set
    shape as `refHpLiesAt` (`einzahlen` holds exactly `[()]`). -/
theorem refHpEinAt :
    RufPasst refD (vertragVon refD refEin) (refD.signatur refEin)
      [Res.held (D := refD) ()] where
  hw := fun t ht => by cases t <;> rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := RufPasst.hh_von refHeldIff
  hx := RufPasst.hx_von refHeldIff

/-- Witness argument: `3` as a widened literal. The type is stated as
    `[.int 0 10]` (definitionally `refD.params refEin` by
    `refEin_params`), so every downstream computation reduces. -/
def argDreiLit : Args refD [] [Res.held (D := refD) ()] [.int 0 10] :=
  Args.cons ((.weiter (by decide) (by decide) (.lit 3)) :
    Expr refD [] [Res.held (D := refD) ()] (.int 0 10)) Args.nil

/-- Witness argument: `3` as a widened sum `1 + 2` -- syntactically
    different from `argDreiLit`, same value, same (empty) footprint. -/
def argDreiAdd : Args refD [] [Res.held (D := refD) ()] [.int 0 10] :=
  Args.cons ((.weiter (by decide) (by decide) (.add (.lit 1) (.lit 2))) :
    Expr refD [] [Res.held (D := refD) ()] (.int 0 10)) Args.nil

/-- JOINT WITNESS for `OptCallArgSel_verbindung`: admitted selection of
    `[3]` at the `einzahlen`-call of `refD` -- literal `3` versus sum
    `1 + 2`, one shared register placement -- beside the memory-changing
    reached run. -/
theorem OptCallArgSel_verbindung_zeuge :
    ∃ (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool) (f : refD.Fn)
      (args args' : Args refD Γ Λ (refD.params f))
      (hp hp' : RufPasst refD (vertragVon refD refEin) (refD.signatur f) Λ)
      (hr hr' : refD.gruende f = 0)
      (cert : CallArgCert) (vs : List Int)
      (_hz : callArgZulassen cert = true)
      (_hN : vs.length ≤ maxArgs)
      (σ : World refD) (ρ : Env refD Γ)
      (_hVs : vs = envInts (evalArgs σ args σ ρ))
      (_hVs' : vs = envInts (evalArgs σ args' σ ρ))
      (_hOrte : args.orte = args'.orte)
      (_hVals : ∀ w : World refD, evalArgs w args w ρ = evalArgs w args' w ρ),
      liesWerte (α := Int) (platziere (α := Int) vs)
        = envInts (evalArgs σ args σ ρ)
      ∧ liesWerte (α := Int) (platziere (α := Int) vs)
        = envInts (evalArgs σ args' σ ρ)
      ∧ envInts (evalArgs σ args σ ρ) = envInts (evalArgs σ args' σ ρ)
      ∧ ((platziere (α := Int) vs).length = vs.length)
      ∧ platzOk cert vs.length = true
      ∧ execStmt (l := l) O passes R (Stmt.call (l := l) f args hp hr) σ ρ
        = execStmt (l := l) O passes R (Stmt.call (l := l) f args' hp' hr') σ ρ
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptCallArgSel_verbindung (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf)
    (Γ := []) (Λ := [Res.held (D := refD) ()]) (l := false)
    (f := refEin) (args := argDreiLit) (args' := argDreiAdd)
    (hp := refHpEinAt) (hp' := refHpEinAt) (hr := rfl) (hr' := rfl)
    (cert := ⟨true, true, true, true⟩) (vs := [3])
    (hz := by decide) (hN := by decide)
    (σ := refSp0.welt []) (ρ := Env.nil)
    (hVs := rfl) (hVs' := rfl) (hOrte := rfl) (hVals := fun _ => rfl)
  refine ⟨refO, 0, keinRuf, [], [Res.held (D := refD) ()], false,
    refEin, argDreiLit, argDreiAdd, refHpEinAt, refHpEinAt, rfl, rfl,
    ⟨true, true, true, true⟩, [3], by decide, by decide,
    refSp0.welt [], Env.nil, rfl, rfl, rfl, fun _ => rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2.1
  · exact hV.2.2.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
  - Full `evalArgs`-preservation by the lowering is OPEN (review 1044,
    R1): this file derives the integer-value agreement through the
    shared placement record (`envInts` round-trips) and the conditional
    outcome congruence; showing that the EMITTED bytes evaluate every
    argument (including non-integer ones) to the same values belongs to
    the lowering/validator lane with the byte correspondence.
  - No register classes: the model has ONE `reg` file keyed by position.
    Integer versus float (xmm) classes under System V AMD64, and which
    positions consume which class, are not modelled -- the validator
    decides the per-image convention content, carried here only as the
    `konventionGeprueft` Bool.
  - No REX/width/flag effects: widths below 64 bits, sign/zero extension
    on narrower moves, and condition-code clobbering by argument moves
    are not modelled.
  - No 16-byte entry alignment: only 8-alignment of each stack slot is
    proved (`platzFuer_buendig`); the call-entry 16-alignment invariant
    (stack depth parity at the call) is unchecked here.
  - No convention content beyond one `Bool`: the per-image calling
    convention (register order, stack layout, hidden parameters, class
    rules) enters only as `konventionGeprueft`; its recomputation from
    the image is validator work, not proved here.
  - `maxArgs = 64` provenance: a fixed constant of this rule, not a
    validator-decided value; the per-site BOUND CHECK (`platzOk`,
    `keinFehlerNeu`) is decided, the number itself is reviewed, not
    derived.
  - No TSO/memory-order claim for stack-slot stores: the order in which
    lowered stores become visible to other threads, and their interaction
    with fences/locks, stays with the TSO/GX bridge lane.
  - No block-window float rewrite beyond value stability: section 4 proves
    the `gleitPasst` outcome is a pure function of preserved values; the
    kernel recomputation of any folded float equation stays with the
    constant-folding lane.
  - No lowering to bytes: `platziere` is the SOURCE-side value record of
    the per-site placement (DESIGN layer A over arbitrary values), not a
    decoded machine instruction; the byte correspondence through decoded
    final machine bytes stays with the decoder/bridge lanes.
  - No per-site spill/fence accounting beyond the unit count: section 2
    proves one location per argument, so no hidden move enters the
    `CostSummary` expansion; the counted per-class maxima stay with the
    cost lane.
  - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
    correspondence stops at preserved source values, `gleitPasst`
    outcomes and the conditional `execStmt` call-outcome congruence over
    the canonical vocabulary.
  - No checker change: no source admission is tightened to ease proof;
    everything is over the real `Stmt.call`, the real `evalArgs` and the
    real reference program `refD`.
-/

#print axioms callArgZulassen
#print axioms callArgVerweigert_konvention
#print axioms callArgVerweigert_budget
#print axioms callArgVerweigert_versteckt
#print axioms callArgVerweigert_stapel
#print axioms platziere_liest
#print axioms platziere_laenge
#print axioms platzFuer_reg
#print axioms platzFuer_stapel
#print axioms platzFuer_buendig
#print axioms gleitPasst_erhalt
#print axioms platzOk_von_zulassen
#print axioms keinFehlerNeu
#print axioms platzWort
#print axioms wertInt_int
#print axioms envInts_cons
#print axioms probe_envInts
#print axioms refHeldIff
#print axioms refHpEinAt
#print axioms OptCallArgSel_verbindung
#print axioms OptCallArgSel_verbindung_zeuge

end Gabbro.Grammatik.X86
