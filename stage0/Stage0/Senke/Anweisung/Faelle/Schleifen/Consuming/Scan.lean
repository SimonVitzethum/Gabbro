/- Induction over the concrete selector's remaining index suffix. Edges are
   ordinary runner executions; there is no additional execution semantics. -/
module
public import Stage0.Senke.Anweisung.SchleifeTeile
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR

variable [Kern] {D : Deklaration} {L : Lay D}
variable {fp : W} {lo K : Nat} {pr : List Nat}

/-- A path between two instruction addresses with the same frame contract as
    statement lowering. The postcondition retains the loop's concrete words,
    represented environment/world, code and surrounding function interface. -/
def ScanRun (L : Lay D) (fp : W) (lo K : Nat) (pr : List Nat)
    (start finish : W) (m : Mem) (post : Mem → Prop) : Prop :=
  ∃ m', Star ⟨start, fp⟩ m ⟨finish, fp⟩ m' ∧
    AgreeW L fp lo K m m' ∧ Keeps fp pr m m' ∧ post m'

/-- Prefix a suffix simulation with the instructions of one actual scan step. -/
theorem ScanRun.bind {start middle finish : W} {m : Mem}
    {mid post : Mem → Prop}
    (first : ScanRun L fp lo K pr start middle m mid)
    (rest : ∀ m', mid m' → ScanRun L fp lo K pr middle finish m' post) :
    ScanRun L fp lo K pr start finish m post := by
  obtain ⟨m1, s1, a1, k1, h1⟩ := first
  obtain ⟨m2, s2, a2, k2, h2⟩ := rest m1 h1
  exact ⟨m2, s1.trans s2, a1.trans a2, k1.trans k2, h2⟩

/-- Predecessor-loop simulation, in the same suffix/fuel form as trav_loop.
    The emitted bound test, rejecting branch and
    increment/backedge are explicit premises below. `ready j` includes the predecessor counter word j;
    `result` restores the candidate binder even after membership borrowing.
    Self edges are ignored, exactly as in the canonical keinVorgaenger. -/
theorem predecessor_scan (count : Int) (candidate : Zahl 0 (count - 1))
    (member : Zahl 0 (count - 1) → Bool)
    (edge : Zahl 0 (count - 1) → Zahl 0 (count - 1) → Bool)
    (header selected rejected : W)
    (ready : Nat → Mem → Prop) (result : Bool → Mem → Prop)
    (exhausted : ∀ m, ready count.toNat m →
      ScanRun L fp lo K pr header selected m (result true))
    (blocked : ∀ j (x : Zahl 0 (count - 1)), x.n = j →
      (member x && edge x candidate && !decide (x.n = candidate.n)) = true →
      ∀ m, ready j m → ScanRun L fp lo K pr header rejected m (result false))
    (advance : ∀ j (x : Zahl 0 (count - 1)), x.n = j →
      (member x && edge x candidate && !decide (x.n = candidate.n)) = false →
      ∀ m, ready j m → ScanRun L fp lo K pr header header m (ready (j + 1))) :
    ∀ remaining j, j + remaining = count.toNat → ∀ m, ready j m →
      let answer := keinVorgaenger (idxAb count j remaining) member edge
        (fun a b => decide (a.n = b.n)) candidate
      ScanRun L fp lo K pr header (if answer then selected else rejected) m (result answer) := by
  intro remaining
  induction remaining with
  | zero =>
    intro j endCount m hm
    have hj : j = count.toNat := by omega
    subst j
    simpa only [idxAb_zero, keinVorgaenger, ↓reduceIte] using exhausted m hm
  | succ remaining ih =>
    intro j bound m hm
    obtain ⟨x, hx, suffix⟩ := idxAb_succ count j remaining (by omega)
    rw [suffix]
    dsimp only [keinVorgaenger]
    by_cases hit : (member x && edge x candidate && !decide (x.n = candidate.n)) = true
    · simpa only [hit, Bool.not_true, Bool.false_and, ↓reduceIte] using
        blocked j x hx hit m hm
    · have miss : (member x && edge x candidate && !decide (x.n = candidate.n)) = false := by
        cases h : member x && edge x candidate && !decide (x.n = candidate.n)
        · rfl
        · exact False.elim (hit h)
      simp only [miss, Bool.not_false, Bool.true_and]
      exact (advance j x hx miss m hm).bind
        (fun m' h' => ih (j + 1) (by omega) m' h')

/-- Candidate-loop simulation. The positive edge contains predecessor_scan;
    a rejected candidate executes candidateNext and re-enters with j+1. The
    final live flag is computed over the whole scanned suffix, so no-minimal
    and all-absent domains remain distinguishable.

    `minimal` is the actual membership/predecessor branch, with the canonical
    orientation predecessor::candidate. Its proof is independent of the body. -/
theorem candidate_scan (count : Int)
    (member : Zahl 0 (count - 1) → Bool)
    (edge : Zahl 0 (count - 1) → Zahl 0 (count - 1) → Bool)
    (header selected exhausted : W)
    (ready : Nat → Bool → Mem → Prop)
    (result : Option (Zahl 0 (count - 1)) → Bool → Mem → Prop)
    (endScan : ∀ seen m, ready count.toNat seen m →
      ScanRun L fp lo K pr header exhausted m (result none seen))
    (minimal : ∀ j (x : Zahl 0 (count - 1)), x.n = j → ∀ seen m,
      ready j seen m →
      let test := istMinimalVerbrauch (alleIndizes count) member edge
        (fun a b => decide (a.n = b.n)) x
      if test then ScanRun L fp lo K pr header selected m (result (some x) true)
      else ScanRun L fp lo K pr header header m (ready (j + 1) (seen || member x))) :
    ∀ remaining j, j + remaining = count.toNat → ∀ seen m, ready j seen m →
      let suffix := idxAb count j remaining
      let choice := verbrauchWahlAux (alleIndizes count) suffix member edge
        (fun a b => decide (a.n = b.n))
      let live := seen || suffix.any member
      ScanRun L fp lo K pr header (if choice.isSome then selected else exhausted)
        m (result choice live) := by
  intro remaining
  induction remaining with
  | zero =>
    intro j bound seen m hm
    have hj : j = count.toNat := by omega
    subst j
    simpa only [idxAb_zero, verbrauchWahlAux, List.any_nil, Bool.or_false,
      Option.isSome_none, ↓reduceIte] using endScan seen m hm
  | succ remaining ih =>
    intro j bound seen m hm
    obtain ⟨x, hx, suffix⟩ := idxAb_succ count j remaining (by omega)
    dsimp only
    rw [suffix]
    simp only [verbrauchWahlAux, List.any_cons]
    have step := minimal j x hx seen m hm
    by_cases good : istMinimalVerbrauch (alleIndizes count) member edge
        (fun a b => decide (a.n = b.n)) x = true
    · have live : member x = true := (Bool.and_eq_true.mp good).1
      simp only [good, ↓reduceIte] at step ⊢
      simpa only [live, Bool.true_or, Bool.or_true, Option.isSome_some, ↓reduceIte]
        using step
    · simp only [good, ↓reduceIte] at step ⊢
      have rest := step.bind (fun m' h' => ih (j + 1) (by omega) (seen || member x) m' h')
      cases seen <;> cases hp : member x <;> simpa only [hp, Bool.false_or, Bool.true_or]
        using rest

end Gabbro.Stage0.Senke.Consuming
