module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm
public import Grammatik.Kern.Syntax.Ziel
public import Grammatik.Korpus.Zeugnis.Zeugnis

@[expose] public section



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

theorem totalCost_nil : totalCost [] = 0 := by rfl

theorem totalCost_cons (op : Op) (rest : List Op) :
    totalCost (op :: rest) = op.cost + totalCost rest := by rfl

theorem runOps_nil (bound left : Nat) : runOps bound left [] = .ok left := by rfl

theorem runOps_cons (bound left : Nat) (op : Op) (rest : List Op) :
    runOps bound left (op :: rest) =
      (if op.cost ≤ left then runOps bound (left - op.cost) rest
       else .budget "per_pass.ops" (bound - left + op.cost + totalCost rest) bound) := by rfl

/-- Steps within bound execute, and the leftover is exact. -/
theorem runOps_within (bound left : Nat) (ops : List Op)
    (h : totalCost ops ≤ left) :
    runOps bound left ops = .ok (left - totalCost ops) := by
  revert left h
  induction ops with
  | nil =>
    intro left _
    rw [runOps_nil, totalCost_nil]
    simp only [Nat.sub_zero]
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

theorem runPasses_nil (b : Budget) : runPasses b [] = .ok b.perPass := by rfl

theorem runPasses_cons (b : Budget) (p : Pass) (rest : List Pass) :
    runPasses b (p :: rest) =
      match runOps b.perPass b.perPass p.2 with
      | .ok _ => runPasses b rest
      | .budget _ _ _ => .budget p.1 (totalCost p.2) b.perPass := by rfl

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

/-! ## Foreign edges: declared costs, no zero slip

    A foreign edge -- a syscall, an `Ax`/`extern` call -- counts its DECLARED
    cost `decl` plus one dispatch step (`fremdOp`): the call rule `call counts
    DECLARED costs` lifted to edges the checker cannot see into. The `+ 1`
    is the no-zero-slip rule: even a foreign edge declared at `0` still costs
    one budgeted op, so no foreign call passes the budget silently.
    `budget_erhaltung_fremd` is the preservation lemma: a pass holding a
    foreign edge fits the bound exactly when the numbers say so, and an
    over-budget foreign edge stops with the named outcome -- through
    `runOps_within`/`runOps_exceeds`/`runPass_within`, nothing re-proved.
-/

/-- A foreign edge as a budgeted op: declared cost plus one dispatch step. -/
def fremdOp (decl : Nat) : Op := ⟨decl + 1⟩

/-- A foreign edge costs exactly its declared cost plus one. -/
theorem fremdOp_kosten (decl : Nat) : (fremdOp decl).cost = decl + 1 := by rfl

/-- No zero slip: a foreign edge costs at least one op, even declared at `0`. -/
theorem fremd_kein_null (decl : Nat) : 1 ≤ (fremdOp decl).cost := by
  simp only [fremdOp]; omega

/-- A lone foreign edge totals to its declared cost plus one. -/
theorem fremd_totalCost (decl : Nat) : totalCost [fremdOp decl] = decl + 1 := by rfl

/-- A foreign edge within bound executes and reports the exact leftover. -/
theorem runOps_fremd_within (bound left decl : Nat) (h : decl + 1 ≤ left) :
    runOps bound left [fremdOp decl] = .ok (left - (decl + 1)) := by
  apply runOps_within
  simp only [fremd_totalCost]
  exact h

/-- A foreign edge over bound stops with the named budget outcome. -/
theorem runOps_fremd_exceeds (bound left decl : Nat) (h : left < decl + 1) :
    ∃ needed, runOps bound left [fremdOp decl] = .budget "per_pass.ops" needed bound := by
  apply runOps_exceeds
  simp only [fremd_totalCost]
  exact h

/-- **Budget preservation over foreign calls**: a pass holding a foreign edge
    of declared cost `decl` runs `ok` whenever `decl + 1` fits the bound --
    through `runPass_within`, hence under `per_pass_respected`. -/
theorem budget_erhaltung_fremd (b : Budget) (decl : Nat) (h : decl + 1 ≤ b.perPass) :
    ∃ left, runPass b [fremdOp decl] = .ok left :=
  runPass_within b [fremdOp decl] (by simp only [fremd_totalCost]; exact h)

/-- Accept: a foreign edge declared at `0` still costs exactly one op. -/
example : (fremdOp 0).cost = 1 := by rfl

/-- Accept: a foreign edge declared at `3` totals to four ops. -/
example : totalCost [fremdOp 3] = 4 := by rfl

/-- Accept: that edge fits a bound of five with leftover one. -/
example : runPass ⟨5⟩ [fremdOp 3] = .ok 1 := by rfl

/-- Reject: it does not fit a bound of three -- the run names the breach. -/
example : ∃ needed, runOps 3 3 [fremdOp 3] = .budget "per_pass.ops" needed 3 :=
  runOps_fremd_exceeds 3 3 3 (by omega)

#print axioms Gabbro.Grammatik.fremdOp_kosten
#print axioms Gabbro.Grammatik.fremd_kein_null
#print axioms Gabbro.Grammatik.fremd_totalCost
#print axioms Gabbro.Grammatik.runOps_fremd_within
#print axioms Gabbro.Grammatik.runOps_fremd_exceeds
#print axioms Gabbro.Grammatik.budget_erhaltung_fremd

end Gabbro.Grammatik
