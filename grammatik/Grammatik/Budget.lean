/-
  File:       Grammatik/Budget.lean
  Subject:    Ops-budget accounting is sound: a declared per-pass bound is
              respected by execution.

  Claim (in one sentence):
    Steps whose total cost fits the declared per-pass bound execute and report
    the leftover; steps whose total cost exceeds the bound stop with an
    EXPLICIT budget outcome that names the pass -- never with a silent
    overrun.

  Mapping to the declared surface (`SYNTAX.md` §18, fourth version):
    `costs`          -- `Op.cost`: the declared cost of one primitive step.
                       A number the declaration trusts, not one measured here
                       (premise P1).
    `per_pass N ops` -- `Budget.perPass = N`: a FRESH bound of `N` ops for EACH
                       pass. `ops` is `totalCost`, the summed step costs on the
                       Gabbro side.
    stuck-with-name  -- `BudgetOut.budget name needed bound`: the explicit
                       outcome. For one pass the name is the syntactic form
                       `"per_pass.ops"`; over several passes it is the failing
                       pass's own name.

  Deliberately OUTSIDE (decision, not omission):
    Wall-clock time, cycles, and deadlines never enter this file. Per
    `Ziel.lean` the budget counts Gabbro-side steps only; a deadline is the
    hardware assumption `fortschritt` with its probe (`fristAlsAnnahme`),
    measured by the probe and never proved here. There is no `Time` type
    below, and that absence is the statement.

  Proven below (`#print axioms` at the end shows each rests on no axioms):
    `runOps_within`        -- within bound: execution reports the exact leftover.
    `runOps_exceeds`       -- over bound: execution reports the named budget outcome.
    `runOps_no_silent`     -- no silent overrun: `ok` implies within bound.
    `runOps_exhaustive`    -- no third outcome: every run is `ok` or `budget`.
    `runPass_within`       -- the same three through one fresh per-pass budget.
    `runPass_exceeds`
    `runPass_no_silent`
    `runPasses_all_within` -- `ok` over passes implies EVERY pass was within bound.
    `runPasses_complete`   -- every pass within bound implies `ok`.
    `runPasses_exceeds`    -- one pass over bound implies the named budget outcome.
    `per_pass_respected`   -- the umbrella: either all passes ran within bound,
                              or the run names the pass that did not.
    `held_respected_gilt`    -- the `held <= K` umbrella, through `per_pass_respected`.
    `bounded_respected_gilt` -- the `bounded N` umbrella, through `per_pass_respected`.
    `seqPasses_complete`   -- every sequence element within bound implies `ok`.
    `seqPasses_exceeds`    -- one element over bound implies the named outcome.
    `senkKosten_modell`      -- a modeled lowering head costs exactly one C-side op.
    `senkKosten_unter_schranke` -- that one op fits under the measured maximum.
    `modell_erhaltung`       -- preservation for the modeled ops: a valid print
                               elaborates (meaning, reused) AND fits the max
                               (count, new).
    `modell_lauf_erhalten`   -- over modeled runs the lowered count IS the source
                               count: one op in, one op out.

  Premises (trusted, not proved):
    P1  Declared costs are faithful: `Op.cost` is the cost the declaration
        attributes to the primitive. No measurement against the emitter.
    P2  Fresh budget per pass: each pass starts at the full `perPass` bound;
        leftover does not carry across passes, overrun does not accumulate.
    P3  Addition on `Nat` counts steps: `totalCost` sums the declared costs.

  Cuts (booked, not hidden):
    C1  The interpreter is abstract: `runOps`/`runPasses` range over op lists,
        not over an instrumentation of `Semantik.exec`. There is NO verified
        link from a `Stmt`/`Block` to its op list; threading a budget through
        `execStmt`/`execBlock` is cut, not faked.
    C2  `held <=` and `bounded` are budget forms, exhaustion outcomes, and
        run/umbrella shapes beside `per_pass` (defs reusing
        `runPass`/`runPasses_*`); the umbrellas are proved
        (`held_respected_gilt`, `bounded_respected_gilt` through
        `per_pass_respected`). No link to `Semantik.exec`.
    C3  No preservation claim across lowering: nothing about C forms,
        quantitative CompCert, or the probe. Same boundary as `Ziel.lean`.
        NARROWED 2026-09-11 for the seven modeled heads (CUT-1/2): the
        appendix `Lowering preservation for the modeled ops` below proves
        the count leg beside the reused `zeugnis_sound` meaning leg, over
        the measured maximum; the remainder named there stays cut.
    C4  Not wired into `Grammatik.lean`: lane scope forbids the index edit;
        check this file directly with `lake env lean Grammatik/Budget.lean`.
    C5  Statement threading is shapes only (`SeqElem`/`seqPasses` below): the
        op list of an element is a DECLARED assignment (P1 lifted to
        statements), resource threading (`Λ` into `Λ'`) between elements is
        not tracked, and there is NO link to `Semantik.execStmt`/`execBlock`.
        Closing that link needs `Semantik` changes and stays booked here, not
        faked.

  No `mathlib`, no `sorry`, no `axiom`.
-/

import Grammatik.Syntax
import Grammatik.Ziel
import Grammatik.Zeugnis

namespace Gabbro.Grammatik

/-- One budgeted primitive step. `cost` is its DECLARED cost (premise P1). -/
structure Op where
  cost : Nat
  deriving DecidableEq, Repr

/-- `ops`: the cost of a pass on the Gabbro side, summed (premise P3). -/
def totalCost : List Op → Nat
  | [] => 0
  | op :: rest => op.cost + totalCost rest

/-- The declared bound: `per_pass N ops` is `Budget.mk N` (premise P2). -/
structure Budget where
  perPass : Nat
  deriving DecidableEq, Repr

/-- The outcome of a budgeted run. Two constructors, like the two errors of
    `Ausgang` in `Semantik.lean`: `ok` is the quiet case, and the breach is
    `budget` -- named, with the numbers attached. There is no third. -/
inductive BudgetOut where
  | ok (left : Nat) : BudgetOut
  | budget (name : String) (needed bound : Nat) : BudgetOut
  deriving DecidableEq, Repr

/-- The budgeted interpreter: check BEFORE each step. The first step that does
    not fit stops the run with the named budget outcome. -/
def runOps (bound left : Nat) : List Op → BudgetOut
  | [] => .ok left
  | op :: rest =>
    if op.cost ≤ left then runOps bound (left - op.cost) rest
    else .budget "per_pass.ops" (bound - left + op.cost + totalCost rest) bound

theorem totalCost_nil : totalCost [] = 0 := rfl

theorem totalCost_cons (op : Op) (rest : List Op) :
    totalCost (op :: rest) = op.cost + totalCost rest := rfl

theorem runOps_nil (bound left : Nat) : runOps bound left [] = .ok left := rfl

theorem runOps_cons (bound left : Nat) (op : Op) (rest : List Op) :
    runOps bound left (op :: rest) =
      (if op.cost ≤ left then runOps bound (left - op.cost) rest
       else .budget "per_pass.ops" (bound - left + op.cost + totalCost rest) bound) := rfl

/-- Steps within bound execute, and the leftover is exact. -/
theorem runOps_within (bound left : Nat) (ops : List Op)
    (h : totalCost ops ≤ left) :
    runOps bound left ops = .ok (left - totalCost ops) := by
  revert left h
  induction ops with
  | nil =>
    intro left _
    rw [runOps_nil, totalCost_nil]
    simp
  | cons op rest ih =>
    intro left h
    rw [totalCost_cons] at h
    rw [runOps_cons, totalCost_cons]
    have hhead : op.cost ≤ left := by omega
    rw [if_pos hhead]
    have hrest : totalCost rest ≤ left - op.cost := by omega
    rw [ih (left - op.cost) hrest]
    congr 1
    omega

/-- Steps over bound stop with the EXPLICIT, named budget outcome. -/
theorem runOps_exceeds (bound left : Nat) (ops : List Op)
    (h : left < totalCost ops) :
    ∃ needed, runOps bound left ops = .budget "per_pass.ops" needed bound := by
  revert left h
  induction ops with
  | nil =>
    intro left h
    rw [totalCost_nil] at h
    exact absurd h (by omega)
  | cons op rest ih =>
    intro left h
    rw [totalCost_cons] at h
    rw [runOps_cons]
    by_cases hhead : op.cost ≤ left
    · rw [if_pos hhead]
      have hrest : left - op.cost < totalCost rest := by omega
      exact ih (left - op.cost) hrest
    · rw [if_neg hhead]
      exact ⟨_, rfl⟩

/-- Never a silent overrun: `ok` implies the cost fit the bound. -/
theorem runOps_no_silent (bound left left' : Nat) (ops : List Op)
    (h : runOps bound left ops = .ok left') :
    totalCost ops ≤ left := by
  by_cases hc : totalCost ops ≤ left
  · exact hc
  · have hlt : left < totalCost ops := by omega
    obtain ⟨_, hb⟩ := runOps_exceeds bound left ops hlt
    rw [hb] at h
    exact BudgetOut.noConfusion h

/-- No third outcome: every run is `ok` or the named `budget`. -/
theorem runOps_exhaustive (bound left : Nat) (ops : List Op) :
    (∃ left', runOps bound left ops = .ok left') ∨
    (∃ needed, runOps bound left ops = .budget "per_pass.ops" needed bound) := by
  by_cases hc : totalCost ops ≤ left
  · exact Or.inl ⟨_, runOps_within bound left ops hc⟩
  · have hlt : left < totalCost ops := by omega
    obtain ⟨_, hb⟩ := runOps_exceeds bound left ops hlt
    exact Or.inr ⟨_, hb⟩

/-! ## One pass: the same three through a fresh per-pass budget -/

/-- One pass runs against a FRESH full bound (premise P2). -/
def runPass (b : Budget) (ops : List Op) : BudgetOut :=
  runOps b.perPass b.perPass ops

theorem runPass_within (b : Budget) (ops : List Op)
    (h : totalCost ops ≤ b.perPass) :
    ∃ left, runPass b ops = .ok left :=
  ⟨_, runOps_within b.perPass b.perPass ops h⟩

theorem runPass_exceeds (b : Budget) (ops : List Op)
    (h : b.perPass < totalCost ops) :
    ∃ needed, runPass b ops = .budget "per_pass.ops" needed b.perPass :=
  runOps_exceeds b.perPass b.perPass ops h

theorem runPass_no_silent (b : Budget) (ops : List Op) (left : Nat)
    (h : runPass b ops = .ok left) :
    totalCost ops ≤ b.perPass :=
  runOps_no_silent b.perPass b.perPass left ops h

/-! ## Passes: the bound resets at each pass, the name sticks to the failure -/

/-- A named pass: the name is what a breach reports (stuck-with-name). -/
abbrev Pass := String × List Op

/-- The budgeted multi-pass run: each pass starts fresh; the first breach
    stops the whole run under the failing pass's name. -/
def runPasses (b : Budget) : List Pass → BudgetOut
  | [] => .ok b.perPass
  | p :: rest =>
    match runOps b.perPass b.perPass p.2 with
    | .ok _ => runPasses b rest
    | .budget _ _ _ => .budget p.1 (totalCost p.2) b.perPass

theorem runPasses_nil (b : Budget) : runPasses b [] = .ok b.perPass := rfl

theorem runPasses_cons (b : Budget) (p : Pass) (rest : List Pass) :
    runPasses b (p :: rest) =
      match runOps b.perPass b.perPass p.2 with
      | .ok _ => runPasses b rest
      | .budget _ _ _ => .budget p.1 (totalCost p.2) b.perPass := rfl

/-- Head fits: the run continues with the tail. -/
theorem runPasses_cons_ok (b : Budget) (p : Pass) (rest : List Pass) (v : Nat)
    (hOps : runOps b.perPass b.perPass p.2 = .ok v) :
    runPasses b (p :: rest) = runPasses b rest := by
  rw [runPasses_cons, hOps]

/-- Head breaches: the run stops under the head's name. -/
theorem runPasses_cons_budget (b : Budget) (p : Pass) (rest : List Pass)
    (name : String) (needed bd : Nat)
    (hOps : runOps b.perPass b.perPass p.2 = .budget name needed bd) :
    runPasses b (p :: rest) = .budget p.1 (totalCost p.2) b.perPass := by
  rw [runPasses_cons, hOps]

/-- `ok` over passes implies EVERY pass was within bound: no pass overran
    silently behind a later `ok`. -/
theorem runPasses_all_within (b : Budget) (passes : List Pass)
    (left : Nat) (h : runPasses b passes = .ok left) :
    ∀ p ∈ passes, totalCost p.2 ≤ b.perPass := by
  revert left h
  induction passes with
  | nil =>
    intro left _ p hm
    exact (List.not_mem_nil hm).elim
  | cons hd tl ih =>
    intro left h p hm
    cases hOps : runOps b.perPass b.perPass hd.2 with
    | ok left' =>
      rw [runPasses_cons_ok b hd tl left' hOps] at h
      cases List.mem_cons.mp hm with
      | inl heq =>
        rw [heq]
        exact runOps_no_silent b.perPass b.perPass left' hd.2 hOps
      | inr hmem =>
        exact ih _ h _ hmem
    | budget _ _ _ =>
      rw [runPasses_cons_budget b hd tl _ _ _ hOps] at h
      exact BudgetOut.noConfusion h

/-- Every pass within bound implies `ok`: nothing else can stop the run. -/
theorem runPasses_complete (b : Budget) (passes : List Pass)
    (h : ∀ p ∈ passes, totalCost p.2 ≤ b.perPass) :
    ∃ left, runPasses b passes = .ok left := by
  revert h
  induction passes with
  | nil =>
    intro _
    exact ⟨_, runPasses_nil b⟩
  | cons hd tl ih =>
    intro h
    have hhead : totalCost hd.2 ≤ b.perPass :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have hOps : runOps b.perPass b.perPass hd.2
        = .ok (b.perPass - totalCost hd.2) :=
      runOps_within b.perPass b.perPass hd.2 hhead
    have htail : ∀ p ∈ tl, totalCost p.2 ≤ b.perPass := by
      intro p hm
      exact h p (List.mem_cons.mpr (Or.inr hm))
    obtain ⟨left, hleft⟩ := ih htail
    refine ⟨left, ?_⟩
    rw [runPasses_cons_ok b hd tl _ hOps, hleft]

/-- One pass over bound implies the run stops under THAT pass's name. -/
theorem runPasses_exceeds (b : Budget) (passes : List Pass)
    (h : ∃ p ∈ passes, b.perPass < totalCost p.2) :
    ∃ name needed, runPasses b passes = .budget name needed b.perPass := by
  revert h
  induction passes with
  | nil =>
    intro h
    obtain ⟨p, hm, _⟩ := h
    exact (List.not_mem_nil hm).elim
  | cons hd tl ih =>
    intro h
    by_cases hhead : totalCost hd.2 ≤ b.perPass
    · have hOps : runOps b.perPass b.perPass hd.2
          = .ok (b.perPass - totalCost hd.2) :=
        runOps_within b.perPass b.perPass hd.2 hhead
      rw [runPasses_cons_ok b hd tl _ hOps]
      apply ih
      obtain ⟨p, hm, hlt⟩ := h
      cases List.mem_cons.mp hm with
      | inl heq =>
        subst heq
        exact absurd hlt (by omega)
      | inr hmem =>
        exact ⟨p, hmem, hlt⟩
    · -- `h` is unused below, and `omega` must not see it: an `∃`-hypothesis
      -- with bound atoms makes `omega` fall back to `Decidable.byContradiction`
      -- (classical). Measured 2026-09-10; `clear` keeps the proof axiom-free.
      clear h
      have hlt : b.perPass < totalCost hd.2 := by omega
      obtain ⟨_, hb⟩ := runOps_exceeds b.perPass b.perPass hd.2 hlt
      rw [runPasses_cons_budget b hd tl _ _ _ hb]
      exact ⟨hd.1, _, rfl⟩

/-- The umbrella: either all passes ran within the declared bound, or the run
    names the pass that did not. A silent overrun is neither. -/
theorem per_pass_respected (b : Budget) (passes : List Pass) :
    (∃ left, runPasses b passes = .ok left ∧
      ∀ p ∈ passes, totalCost p.2 ≤ b.perPass) ∨
    (∃ name needed, runPasses b passes = .budget name needed b.perPass) := by
  by_cases h : ∃ p ∈ passes, b.perPass < totalCost p.2
  · obtain ⟨name, needed, hb⟩ := runPasses_exceeds b passes h
    exact Or.inr ⟨name, needed, hb⟩
  · have hall : ∀ p ∈ passes, totalCost p.2 ≤ b.perPass := by
      intro p hm
      by_cases hlt : b.perPass < totalCost p.2
      · exact absurd ⟨p, hm, hlt⟩ h
      · omega
    obtain ⟨left, hleft⟩ := runPasses_complete b passes hall
    exact Or.inl ⟨left, hleft, hall⟩

#print axioms Gabbro.Grammatik.runOps_within
#print axioms Gabbro.Grammatik.runOps_exceeds
#print axioms Gabbro.Grammatik.runOps_no_silent
#print axioms Gabbro.Grammatik.runOps_exhaustive
#print axioms Gabbro.Grammatik.runPass_within
#print axioms Gabbro.Grammatik.runPass_exceeds
#print axioms Gabbro.Grammatik.runPass_no_silent
#print axioms Gabbro.Grammatik.runPasses_all_within
#print axioms Gabbro.Grammatik.runPasses_cons_ok
#print axioms Gabbro.Grammatik.runPasses_cons_budget
#print axioms Gabbro.Grammatik.runPasses_complete
#print axioms Gabbro.Grammatik.runPasses_exceeds
#print axioms Gabbro.Grammatik.per_pass_respected

/-! ## Gehaltene Sperre: `held <= K ops` als Gestalt neben `per_pass`

    Jede Sperre meldet `held <= K ops`: wer sie haelt, bleibt je Durchgang unter `K`.
    Die Gestalt unten legt nur die Budgetform, den Erschoepfungsausgang und die
    Anbindung an `runPass`/`runPasses` fest; sie rechnet nichts neu und bindet
    nichts an `Semantik.exec` an (Schnitt C2). Nur Definitionen, keine Saetze.
-/

/-- `held <= K ops` als Budgetgestalt: dieselbe Schranke wie `Budget`, unter dem Haltenamen gelesen. -/
def heldBudget (K : Nat) : Budget := ⟨K⟩

/-- Der Erschoepfungsausgang zur gehaltenen Sperre: benannt, mit Zahlen, wie `BudgetOut.budget`. -/
def heldErschoepft (sperrName : String) (gebraucht schranke : Nat) : BudgetOut :=
  .budget sperrName gebraucht schranke

/-- Ein Durchgang unter gehaltener Sperre: frisches `K` je Durchgang (Anbindung an `runPass`). -/
def runHeldPass (K : Nat) (ops : List Op) : BudgetOut :=
  runPass ⟨K⟩ ops

/-- Alle Durchgaenge unter gehaltener Sperre: jeder beginnt frisch, der erste Bruch
    meldet seinen Namen (Anbindung an `runPasses`). -/
def runHeldPasses (K : Nat) (paesse : List Pass) : BudgetOut :=
  runPasses ⟨K⟩ paesse

/-- Die Schirmgestalt zur gehaltenen Sperre: dieselbe Form wie `per_pass_respected`,
    mit `K` als Schranke. Entweder lief alles im Budget, oder der Lauf nennt die
    Stelle, die es nicht tat. -/
def held_respected (K : Nat) (paesse : List Pass) : Prop :=
  (∃ rest, runHeldPasses K paesse = .ok rest ∧
    ∀ p ∈ paesse, totalCost p.2 ≤ K) ∨
  (∃ name gebraucht, runHeldPasses K paesse = .budget name gebraucht K)

/-- The held lock respects its budget: the umbrella shape over `held <= K`
    is the `per_pass` umbrella under the lock name. Either every pass ran
    within `K`, or the run names the pass that did not -- through `runPass`
    and `runPasses`, proved by `per_pass_respected`. -/
theorem held_respected_gilt (K : Nat) (paesse : List Pass) :
    held_respected K paesse :=
  per_pass_respected ⟨K⟩ paesse

#print axioms Gabbro.Grammatik.held_respected_gilt

/-! ## Begrenzte Schleife: `bounded N ops` als Gestalt neben `per_pass`

    `retry` traegt `bounded N ops`, `forever` traegt `per_pass bounded N ops`: je
    Durchgang bleibt unter `N`. Die Gestalt unten legt nur die Budgetform, den
    Erschoepfungsausgang und die Anbindung an `runPass`/`runPasses` fest; sie
    rechnet nichts neu und bindet nichts an `Semantik.exec` an (Schnitt C2).
    Nur Definitionen, keine Saetze.
-/

/-- `bounded N ops` als Budgetgestalt: dieselbe Schranke wie `Budget`, unter dem Schleifennamen gelesen. -/
def boundedBudget (N : Nat) : Budget := ⟨N⟩

/-- Der Erschoepfungsausgang zur begrenzten Schleife: benannt, mit Zahlen, wie `BudgetOut.budget`. -/
def boundedErschoepft (schleifenName : String) (gebraucht schranke : Nat) : BudgetOut :=
  .budget schleifenName gebraucht schranke

/-- Ein Durchgang der begrenzten Schleife: frisches `N` je Durchgang (Anbindung an `runPass`). -/
def runBoundedPass (N : Nat) (ops : List Op) : BudgetOut :=
  runPass ⟨N⟩ ops

/-- Alle Durchgaenge der begrenzten Schleife: jeder beginnt frisch, der erste Bruch
    meldet seinen Namen (Anbindung an `runPasses`). -/
def runBoundedPasses (N : Nat) (paesse : List Pass) : BudgetOut :=
  runPasses ⟨N⟩ paesse

/-- Die Schirmgestalt zur begrenzten Schleife: dieselbe Form wie `per_pass_respected`,
    mit `N` als Schranke. Entweder lief alles im Budget, oder der Lauf nennt die
    Stelle, die es nicht tat. -/
def bounded_respected (N : Nat) (paesse : List Pass) : Prop :=
  (∃ rest, runBoundedPasses N paesse = .ok rest ∧
    ∀ p ∈ paesse, totalCost p.2 ≤ N) ∨
  (∃ name gebraucht, runBoundedPasses N paesse = .budget name gebraucht N)

/-- The bounded loop respects its budget: the umbrella shape over
    `bounded N` is the `per_pass` umbrella under the loop name. Either
    every pass ran within `N`, or the run names the pass that did not --
    through `runPass` and `runPasses`, proved by `per_pass_respected`. -/
theorem bounded_respected_gilt (N : Nat) (paesse : List Pass) :
    bounded_respected N paesse :=
  per_pass_respected ⟨N⟩ paesse

#print axioms Gabbro.Grammatik.bounded_respected_gilt

end Gabbro.Grammatik

/-! ## Statement threading: `runPasses` over `Stmt`/`Block` sequences

    A sequence is a list of index-erased elements sharing one `l` and one `Γ`:
    each element keeps its own `Λ`/`Λ'`. The op list of an element comes from a
    DECLARED assignment `assign` (premise P1 lifted to statements: a number the
    declaration trusts, not one measured here). Resource threading (`Λ` into
    `Λ'`) between elements is NOT tracked below, and there is NO verified link
    from an element to `Semantik.execStmt`/`execBlock`: the full execution
    linkage stays booked (cut C5), not faked.

    Proven below (`#print axioms` shows `[propext, Classical.choice, Quot.sound]`:
    the same footprint as `Stmt`/`Block` themselves and as the `Satz.lean`
    theorems about them -- measured 2026-09-11, inherited by mentioning
    statements, no new axiom):
      `seqPasses_complete` -- every element within bound implies `ok`.
      `seqPasses_exceeds`  -- one element over bound implies the named outcome.
-/

namespace Gabbro.Grammatik

/-- One element of a budgeted sequence: a statement or a whole block, with its
    resource indices erased so elements with different `Λ` share one list. -/
inductive SeqElem (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx) : Type where
  | ofStmt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : SeqElem D V l Γ
  | ofBlock {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : SeqElem D V l Γ

/-- The sequence as named passes: element `i` runs under its own fresh budget
    and reports `"seq.i"` on breach (stuck-with-name, as in `runPasses`). -/
def seqPassesAux {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) : Nat → List (SeqElem D V l Γ) → List Pass
  | _, [] => []
  | i, e :: es => ("seq." ++ toString i, assign e) :: seqPassesAux assign (i + 1) es

/-- The budgeted sequence run: each element starts fresh; the first breach
    stops the whole run under the failing element's name. -/
def seqPasses {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (es : List (SeqElem D V l Γ)) : List Pass :=
  seqPassesAux assign 0 es

theorem seqPassesAux_nil {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (i : Nat) :
    seqPassesAux assign i [] = [] := rfl

theorem seqPassesAux_cons {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (i : Nat)
    (e : SeqElem D V l Γ) (es : List (SeqElem D V l Γ)) :
    seqPassesAux assign i (e :: es)
      = (("seq." ++ toString i, assign e) :: seqPassesAux assign (i + 1) es) := rfl

/-- Every pass of the translated sequence is one element's declared ops. -/
theorem seqPassesAux_all_within {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (b : Budget)
    (es : List (SeqElem D V l Γ)) (i : Nat)
    (h : ∀ e ∈ es, totalCost (assign e) ≤ b.perPass) :
    ∀ p ∈ seqPassesAux assign i es, totalCost p.2 ≤ b.perPass := by
  induction es generalizing i with
  | nil =>
    intro p hm
    rw [seqPassesAux_nil] at hm
    exact (List.not_mem_nil hm).elim
  | cons hd tl ih =>
    intro p hm
    rw [seqPassesAux_cons] at hm
    cases List.mem_cons.mp hm with
    | inl heq =>
      rw [heq]
      exact h hd (List.mem_cons.mpr (Or.inl rfl))
    | inr hmem =>
      exact ih (i + 1) (fun e he => h e (List.mem_cons.mpr (Or.inr he))) _ hmem

/-- An over-budget element survives translation as an over-budget pass. -/
theorem seqPassesAux_has_over {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (assign : SeqElem D V l Γ → List Op) (b : Budget)
    (es : List (SeqElem D V l Γ)) (i : Nat)
    (h : ∃ e ∈ es, b.perPass < totalCost (assign e)) :
    ∃ p ∈ seqPassesAux assign i es, b.perPass < totalCost p.2 := by
  induction es generalizing i with
  | nil =>
    obtain ⟨e, hm, _⟩ := h
    exact (List.not_mem_nil hm).elim
  | cons hd tl ih =>
    by_cases hhead : b.perPass < totalCost (assign hd)
    · refine ⟨("seq." ++ toString i, assign hd), ?_, hhead⟩
      rw [seqPassesAux_cons]
      exact List.mem_cons.mpr (Or.inl rfl)
    · rw [seqPassesAux_cons]
      obtain ⟨e, hm, hlt⟩ := h
      cases List.mem_cons.mp hm with
      | inl heq =>
        subst heq
        exact absurd hlt (by omega)
      | inr hmem =>
        obtain ⟨p, hpm, hplt⟩ := ih (i + 1) ⟨e, hmem, hlt⟩
        exact ⟨p, List.mem_cons.mpr (Or.inr hpm), hplt⟩

/-- Per-pass bound respected through sequencing: every element within bound
    implies the whole sequence runs `ok`. -/
theorem seqPasses_complete {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (b : Budget) (assign : SeqElem D V l Γ → List Op) (es : List (SeqElem D V l Γ))
    (h : ∀ e ∈ es, totalCost (assign e) ≤ b.perPass) :
    ∃ left, runPasses b (seqPasses assign es) = .ok left := by
  apply runPasses_complete
  intro p hm
  exact seqPassesAux_all_within assign b es 0 h p hm

/-- Per-pass bound respected through sequencing: one element over bound
    implies the run stops under THAT element's sequence name. -/
theorem seqPasses_exceeds {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (b : Budget) (assign : SeqElem D V l Γ → List Op) (es : List (SeqElem D V l Γ))
    (h : ∃ e ∈ es, b.perPass < totalCost (assign e)) :
    ∃ name needed, runPasses b (seqPasses assign es) = .budget name needed b.perPass := by
  apply runPasses_exceeds
  obtain ⟨p, hm, hlt⟩ := seqPassesAux_has_over assign b es 0 h
  exact ⟨p, hm, hlt⟩

#print axioms Gabbro.Grammatik.seqPassesAux_all_within
#print axioms Gabbro.Grammatik.seqPassesAux_has_over
#print axioms Gabbro.Grammatik.seqPasses_complete
#print axioms Gabbro.Grammatik.seqPasses_exceeds

end Gabbro.Grammatik

/-! ## Lowering preservation for the modeled ops (hLowering leg b, 2026-09-11)

    What `hLowering` in `Ziel.lean` (`ziel_nutzer_last`) owes beyond the numeric
    fragment (`absenkung_wert`, `absenkung_haelt_schranke`: the witness `17`
    keeps the cap `18`) is the CompCert-style preservation leg: lowering keeps
    the `ops` count. This section states and proves it for the MODELED ops --
    the seven CUT-1/2 certificate heads (`sdiv`, `srem`, `band`, `bor`, `bxor`,
    `shl`, `shr`), whose meaning leg is already proved (`zeugnis_sound` in
    `Zeugnis.lean`: a valid print elaborates to the judged `Expr`). Nothing
    below re-proves meaning; the new claim is the COUNT leg beside it, over
    the measured maximum (`absenkung.proPrimitiv = 17`, counted statically in
    `messung/ABSENKUNG-MESSUNG.md`, confirmed over emitted products in
    `messung/ABSENKUNG-LEXERLAUF.md`, re-confirmed on `fisch` in
    `messung/ABSENKUNG-DURCHSETZUNG.md` section 5):

      `senkKosten_modell`         -- a modeled head lowers to exactly one C-side op.
      `senkKosten_unter_schranke` -- that one op fits under the measured maximum.
      `modell_erhaltung`          -- the preservation theorem: a valid modeled
                                    print elaborates (meaning, reused) AND fits
                                    the max (count, new).
      `modell_lauf_erhalten`      -- over a run of modeled heads the lowered
                                    count IS the source count: one op in, one
                                    op out, no silent loss or gain.

    Proven below (`#print axioms` at the end shows the footprint:
    `modell_erhaltung` inherits whatever `zeugnis_sound` rests on, nothing
    more).

    What is NOT modeled here (booked follow-up, not silent):

    - The eleven other `CertExpr` heads: `lit`, `add`, `sub`, `neg`, `mul`,
      `div`, `rem` (closed-fragment arithmetic: meaning proved, count leg not
      claimed), `wide` (the index widening), `var`, `glob`, `slot` (CUT-4
      reads: meaning proved, count leg not claimed). `modellKopf` says `false`
      for each of them, and every theorem below demands `modellKopf c = true`,
      so the `0` beside `senkKosten` is unreachable, never a claim.
    - The CUT-3 shapes (`CertCut3`: floats, options, sums, grounds,
      quantifiers, `reaches`) and the CUT-4/5 remainders (`durch`, `ptrOf`,
      `fnref`, calls WITH arguments): soundness proved in `Zeugnis.lean`
      (`cut3_sound`, `cut4_sound`, `block5_sound`, lane 106), preservation
      not stated.
    - The `StmtArt`-level expansions above one statement (the descendants
      walk at seventeen and every row beneath it): bounded by the lexer run
      (`17 <= 18`, enforced by `absenkung.rs` once the hook is applied), with
      no per-op preservation claim -- the bound is the enforcement, not the
      proof.
    - The C-to-Asm leg: `costKept` (CerCo, the implication shape in
      `Erhaltung.lean`) and `costMeasured` (production, witness pairs) are
      untouched here; this section speaks Gabbro-to-C only.

    No `mathlib`, no `sorry`, no `axiom`.
-/

namespace Gabbro.Grammatik

/-- The modeled op heads: the seven CUT-1/2 certificate shapes (signed
    division and remainder, bitwise and shifts). Everything else is `false`:
    the unmodeled remainder, named in the section header, not hidden. -/
def modellKopf {D : Deklaration} : CertExpr D → Bool
  | .sdiv _ _ => true
  | .srem _ _ => true
  | .band _ _ => true
  | .bor _ _ _ => true
  | .bxor _ _ _ => true
  | .shl _ _ _ => true
  | .shr _ _ _ => true
  | _ => false

/-- The lowered C-side cost of one head: a modeled op is exactly one C-side
    op site of cost 1 (one op in, one op out -- the CompCert-style count leg,
    declared P1-style). Unmodeled heads carry `0`, which no theorem below can
    observe: each demands `modellKopf c = true`. -/
def senkKosten {D : Deklaration} : CertExpr D → Nat
  | .sdiv _ _ => 1
  | .srem _ _ => 1
  | .band _ _ => 1
  | .bor _ _ _ => 1
  | .bxor _ _ _ => 1
  | .shl _ _ _ => 1
  | .shr _ _ _ => 1
  | _ => 0

/-- Count leg: a modeled head lowers to exactly one C-side op. -/
theorem senkKosten_modell {D : Deklaration} (c : CertExpr D)
    (h : modellKopf c = true) :
    senkKosten c = 1 := by
  cases c <;> simp_all [modellKopf, senkKosten]

/-- Bound leg: the one lowered op fits under the measured maximum. -/
theorem senkKosten_unter_schranke {D : Deklaration} (c : CertExpr D)
    (h : modellKopf c = true) :
    senkKosten c ≤ absenkung.proPrimitiv := by
  have h1 : senkKosten c = 1 := senkKosten_modell c h
  have h17 : absenkung.proPrimitiv = 17 := absenkung_wert
  omega

/-- Preservation for the modeled ops: a valid print of a modeled head
    elaborates to the judged expression (meaning, reused from
    `zeugnis_sound` -- not re-proved) AND lowers to one C-side op under the
    measured maximum (count, new). -/
theorem modell_erhaltung {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertExpr D) (lo hi : Int)
    (hmod : modellKopf c = true) (hval : GueltigAbleitung D Γ Λ c lo hi) :
    (∃ _ : Expr D Γ Λ (.int lo hi), True) ∧
      senkKosten c ≤ absenkung.proPrimitiv :=
  ⟨zeugnis_sound c lo hi hval, senkKosten_unter_schranke c hmod⟩

/-- Over a run of modeled heads the lowered C-side count IS the source count:
    one op in, one op out, no silent loss or gain. -/
theorem modell_lauf_erhalten {D : Deklaration} (cs : List (CertExpr D)) :
    (∀ c ∈ cs, modellKopf c = true) → (cs.map senkKosten).sum = cs.length := by
  induction cs with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    have hhd : modellKopf hd = true := h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ c ∈ tl, modellKopf c = true :=
      fun c hm => h c (List.mem_cons.mpr (Or.inr hm))
    simp only [List.map_cons, List.sum_cons, List.length_cons,
      senkKosten_modell hd hhd, ih htl, Nat.add_comm]

/-- Accept: `7 sdiv 2` is a modeled head. -/
example : modellKopf (D := TestD) (.sdiv (.lit 7) (.lit 2)) = true := by decide

/-- Reject: `add` is not modeled -- the remainder, not a shrug. -/
example : modellKopf (D := TestD) (.add (.lit 1) (.lit 2)) = false := by decide

/-- End to end: a valid modeled print elaborates AND fits under the maximum
    (the CUT-1 probe `7 sdiv 2`, through `modell_erhaltung`). -/
example : (∃ _ : Expr TestD [] [] (.int (-7) 7), True) ∧
    senkKosten (D := TestD) (.sdiv (.lit 7) (.lit 2)) ≤ absenkung.proPrimitiv :=
  modell_erhaltung _ _ _ rfl (by decide)

#print axioms Gabbro.Grammatik.modellKopf
#print axioms Gabbro.Grammatik.senkKosten
#print axioms Gabbro.Grammatik.senkKosten_modell
#print axioms Gabbro.Grammatik.senkKosten_unter_schranke
#print axioms Gabbro.Grammatik.modell_erhaltung
#print axioms Gabbro.Grammatik.modell_lauf_erhalten

end Gabbro.Grammatik
