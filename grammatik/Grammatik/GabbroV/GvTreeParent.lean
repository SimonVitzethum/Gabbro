/-
   File:      Grammatik/GabbroV/GvTreeParent.lean
   Subject:   Agent 04: does `tree { parent child sibling }` imply parent
              consistency? (TODO 0f; `beispiele/09`, `messung/caprock/kapraum`.)

   Question: `blatt_loeschen(opfer)` requires `benutzt(opfer)`; `einsammeln`
   calls it for every descendant of `s`. Does the `tree` declaration alone
   guarantee that every descendant is occupied (or that the links agree)?

   Skeleton: `TreeState` plus the bounded quantifiers. The decision
   (counter-states, local closing clause) lands in later steps.
-/
import Grammatik.Kern.Semantik.Semantik

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- A tree table state, projected from `World` onto one table: the slot
    count, the three edge fields of the `tree` declaration, and the
    occupancy field (`benutzt`). Indices are `Nat`; only `< s.n` count. -/
structure TreeState where
  n : Nat
  parent : Nat → Option Nat
  child : Nat → Option Nat
  sibling : Nat → Option Nat
  benutzt : Nat → Bool

/-- Bounded universal quantification over `off ..< off + m`, as `Bool`. -/
def alleAb (p : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | off, m + 1 => p off && alleAb p (off + 1) m

/-- Bounded universal quantification over `0 ..< n`, as `Bool`. -/
def alleUnter (p : Nat → Bool) (n : Nat) : Bool := alleAb p 0 n

/-- Boolean `<` on `Nat`, so edge-bound checks compute without `decide`. -/
def ltB : Nat → Nat → Bool
  | 0, 0 => false
  | 0, _ + 1 => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => ltB a b

/-- `ltB` means `<`. -/
theorem ltB_true (a b : Nat) (h : ltB a b = true) : a < b := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => simp [ltB] at h
      | succ b => omega
  | succ a ih =>
      cases b with
      | zero => simp [ltB] at h
      | succ b =>
          have h2 : ltB a b = true := by simpa [ltB] using h
          have := ih b h2
          omega

/-- Boolean equality on `Option Nat`, for the link-agreement clauses. -/
def optEq : Option Nat → Option Nat → Bool
  | none, none => true
  | some a, some b => a == b
  | _, _ => false

/-- One optional step: `false` at `none`, `f c` at `some c`. -/
def optSchritt (o : Option Nat) (f : Nat → Bool) : Bool :=
  match o with
  | none => false
  | some c => f c

/-- One optional guard: `true` at `none`, `f c` at `some c`. -/
def optWahr (o : Option Nat) (f : Nat → Bool) : Bool :=
  match o with
  | none => true
  | some c => f c

/-- A true step exists: the edge is bound, with the witness. -/
theorem optSchritt_existiert (o : Option Nat) (f : Nat → Bool)
    (h : optSchritt o f = true) : ∃ c, o = some c := by
  cases o with
  | none => simp [optSchritt] at h
  | some c => exact ⟨c, rfl⟩

/-- A true step through a known binding gives the step predicate. -/
theorem optSchritt_gilt (o : Option Nat) (f : Nat → Bool) (c : Nat)
    (hc : o = some c) (h : optSchritt o f = true) : f c = true := by
  subst hc
  simpa [optSchritt] using h

/-- A true guard at a known binding gives the guarded predicate. -/
theorem optWahr_gilt (o : Option Nat) (f : Nat → Bool) (c : Nat)
    (hc : o = some c) (h : optWahr o f = true) : f c = true := by
  subst hc
  simpa [optWahr] using h

/-- Conjunction elimination, both sides. -/
theorem und_beide (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | true =>
      cases b with
      | true => exact ⟨rfl, rfl⟩
      | false => simp at h
  | false => simp at h

/-- Disjunction elimination, one side. -/
theorem oder_eins (a b : Bool) (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false =>
      cases b with
      | true => exact Or.inr rfl
      | false => simp at h

/-- Boolean implication introduction. -/
theorem impl_true (c b : Bool) (h : c = true → b = true) : ((!c) || b) = true := by
  cases c with
  | true => exact h rfl
  | false => rfl

/-- Lookup in a true bounded quantification. -/
theorem alleAb_gilt (p : Nat → Bool) (off m k : Nat)
    (h : alleAb p off m = true) (hlo : off ≤ k) (hhi : k < off + m) :
    p k = true := by
  induction m generalizing off with
  | zero => omega
  | succ m ih =>
      have h' : (p off && alleAb p (off + 1) m) = true := h
      have h1 : p off = true := (und_beide _ _ h').1
      have h2 : alleAb p (off + 1) m = true := (und_beide _ _ h').2
      by_cases hkk : k = off
      · subst hkk
        exact h1
      · exact ih (off + 1) h2 (by omega) (by omega)

/-- A pointwise true predicate gives a true bounded quantification. -/
theorem alleAb_voll (p : Nat → Bool) (off m : Nat)
    (h : ∀ k, off ≤ k → k < off + m → p k = true) :
    alleAb p off m = true := by
  induction m generalizing off with
  | zero => rfl
  | succ m ih =>
      have h' : (p off && alleAb p (off + 1) m) = true := by
        have h1 : p off = true := h off (Nat.le_refl off) (by omega)
        have h2 : alleAb p (off + 1) m = true :=
          ih (off + 1) (fun k hlo hhi => h k (by omega) (by omega))
        simp [h1, h2]
      exact h'

/-- Declaration shape (the `D006`/`D007`/`D008` value shadow of
    `option index into Self`): every edge answer is `none` or a valid slot.
    This is ALL the declaration constrains. -/
def baumKanteOk (n : Nat) (e : Nat → Option Nat) : Bool :=
  alleAb (fun k => optWahr (e k) (fun m => ltB m n)) 0 n

/-- The declaration holds of the state: all three edges have the form. -/
def hatForm (s : TreeState) : Bool :=
  baumKanteOk s.n s.parent && baumKanteOk s.n s.child && baumKanteOk s.n s.sibling

/-- A bound edge target lies in range. -/
theorem baumKanteOk_ziel (n : Nat) (e : Nat → Option Nat) (k c : Nat)
    (h : baumKanteOk n e = true) (hkn : k < n) (hc : e k = some c) : c < n := by
  have hkk : alleAb (fun k => optWahr (e k) (fun m => ltB m n)) 0 n = true := h
  have hmem : optWahr (e k) (fun m => ltB m n) = true :=
    alleAb_gilt _ 0 n k hkk (Nat.zero_le k) (by omega)
  have hlt : (fun m => ltB m n) c = true := optWahr_gilt _ _ c hc hmem
  exact ltB_true c n hlt

/-- Reachability along child/sibling steps with fuel, mirroring
    `Semantik.kette` (one field there, two step kinds here: the
    first-child/next-sibling walk the traverse lowering runs). -/
def erreichbar (s : TreeState) : Nat → Nat → Nat → Bool
  | 0, k, ziel => if k = ziel then true else false
  | fuel + 1, k, ziel =>
      if k = ziel then true
      else
        optSchritt (s.child k) (fun c => erreichbar s fuel c ziel) ||
        optSchritt (s.sibling k) (fun m => erreichbar s fuel m ziel)

/-- Reachability with the slot count as fuel (more steps repeat a slot). -/
def erreicht (s : TreeState) (a b : Nat) : Bool := erreichbar s s.n a b

/-- Parent consistency at the link level: the form plus, per slot, the
    child/parent inverse (a child is reached downwards from its parent),
    the sibling/parent agreement, all with fuel `s.n`. -/
def elternKonsistent (s : TreeState) : Bool :=
  hatForm s &&
  alleUnter (fun k =>
    optWahr (s.child k) (fun c => optEq (s.parent c) (some k)) &&
    optWahr (s.parent k) (fun p => erreicht s p k) &&
    optWahr (s.sibling k) (fun m => optEq (s.parent m) (s.parent k))) s.n

/-- Occupancy closure: every descendant of an occupied slot is occupied.
    This is what `blatt_loeschen(opfer)` needs for every descendant. -/
def benutztAbgeschlossen (s : TreeState) : Bool :=
  alleUnter (fun k =>
    alleUnter (fun d => ((!erreicht s k d) || (!s.benutzt k)) || s.benutzt d)
      s.n) s.n

/-- Call safety at a root: every descendant the traverse reaches is
    occupied, so the callee's `requires benutzt(opfer)` holds. -/
def aufrufSicher (s : TreeState) (wurzel : Nat) : Bool :=
  alleUnter (fun d => (!erreicht s wurzel d) || s.benutzt d) s.n

/-- The smallest extra clause: the LOCAL one-edge occupancy invariant.
    An occupied slot has occupied children and siblings. -/
def lokalBenutzt (s : TreeState) : Bool :=
  alleUnter (fun k => ((!s.benutzt k) ||
    (optWahr (s.child k) (fun c => s.benutzt c) &&
     optWahr (s.sibling k) (fun m => s.benutzt m)))) s.n

/-- The local clause lifts along every reachable path: with the declaration
    form, an occupied source reaches only occupied targets. -/
theorem lokal_schliesst_fuel (s : TreeState) (fuel k d : Nat)
    (hform : hatForm s = true) (hlok : lokalBenutzt s = true)
    (hkn : k < s.n) (hben : s.benutzt k = true)
    (herr : erreichbar s fuel k d = true) : s.benutzt d = true := by
  revert hkn hben herr
  induction fuel generalizing k with
  | zero =>
      intro hkn hben herr
      by_cases hkd : k = d
      · subst hkd
        exact hben
      · simp only [erreichbar, if_neg hkd] at herr
        simp at herr
  | succ n ih =>
      intro hkn hben herr
      have hS : (if k = d then true
        else
          optSchritt (s.child k) (fun c => erreichbar s n c d) ||
          optSchritt (s.sibling k) (fun m => erreichbar s n m d)) = true :=
        herr
      by_cases hkd : k = d
      · subst hkd
        exact hben
      · rw [if_neg hkd] at hS
        have hfc : baumKanteOk s.n s.child = true :=
          (und_beide _ _ (und_beide _ _ hform).1).2
        have hfs : baumKanteOk s.n s.sibling = true := (und_beide _ _ hform).2
        have hlokAb : alleAb (fun k => ((!s.benutzt k) ||
            (optWahr (s.child k) (fun c => s.benutzt c) &&
             optWahr (s.sibling k) (fun m => s.benutzt m)))) 0 s.n = true :=
          hlok
        have hpk : ((!s.benutzt k) ||
            (optWahr (s.child k) (fun c => s.benutzt c) &&
             optWahr (s.sibling k) (fun m => s.benutzt m))) = true :=
          alleAb_gilt _ 0 s.n k hlokAb (Nat.zero_le k) (by omega)
        have hX : (optWahr (s.child k) (fun c => s.benutzt c) &&
            optWahr (s.sibling k) (fun m => s.benutzt m)) = true := by
          simpa [hben] using hpk
        have hor := oder_eins _ _ hS
        cases hor with
        | inl hA =>
            have hex := optSchritt_existiert _ _ hA
            cases hex with
            | intro c hc =>
                have hlt := baumKanteOk_ziel s.n s.child k c hfc hkn hc
                have hXc := (und_beide _ _ hX).1
                have hbc : s.benutzt c = true := optWahr_gilt _ _ c hc hXc
                have hstep : erreichbar s n c d = true :=
                  optSchritt_gilt _ _ c hc hA
                exact ih c hlt hbc hstep
        | inr hB =>
            have hex := optSchritt_existiert _ _ hB
            cases hex with
            | intro m hm =>
                have hlt := baumKanteOk_ziel s.n s.sibling k m hfs hkn hm
                have hXm := (und_beide _ _ hX).2
                have hbm : s.benutzt m = true := optWahr_gilt _ _ m hm hXm
                have hstep : erreichbar s n m d = true :=
                  optSchritt_gilt _ _ m hm hB
                exact ih m hlt hbm hstep

/-- The local clause gives call safety at an occupied root. -/
theorem lokal_gibt_rufSicher (s : TreeState) (wurzel : Nat)
    (hlok : lokalBenutzt s = true) (hform : hatForm s = true)
    (hwn : wurzel < s.n) (hben : s.benutzt wurzel = true) :
    aufrufSicher s wurzel = true := by
  have hvoll : alleAb (fun d => ((!erreicht s wurzel d) || s.benutzt d))
      0 s.n = true := by
    apply alleAb_voll
    intro d hlo hhi
    show ((!erreicht s wurzel d) || s.benutzt d) = true
    apply impl_true
    intro herr
    exact lokal_schliesst_fuel s s.n wurzel d hform hlok hwn hben herr
  exact hvoll

/-! ## Witnesses: the declaration does not imply consistency -/

/-- Counter-state 1 (the `beispiele/09` shape): links fully agree, the
    declaration holds, but the child slot is free -- a descendant the
    traverse reaches with `benutzt = false`. -/
def gegenbeispiel1 : TreeState where
  n := 2
  parent := fun k => match k with | 1 => some 0 | _ => none
  child := fun k => match k with | 0 => some 1 | _ => none
  sibling := fun _ => none
  benutzt := fun k => match k with | 0 => true | _ => false

theorem gegenbeispiel1_form : hatForm gegenbeispiel1 = true := by decide
theorem gegenbeispiel1_elternOk : elternKonsistent gegenbeispiel1 = true := by decide
theorem gegenbeispiel1_offen : benutztAbgeschlossen gegenbeispiel1 = false := by decide
theorem gegenbeispiel1_rufUnsicher : aufrufSicher gegenbeispiel1 0 = false := by decide
theorem gegenbeispiel1_lokalVerletzt : lokalBenutzt gegenbeispiel1 = false := by decide

/-- Counter-state 2: the declaration holds, but a parent pointer dangles
    (the child edge is absent), so parent consistency fails. -/
def gegenbeispiel2 : TreeState where
  n := 2
  parent := fun k => match k with | 1 => some 0 | _ => none
  child := fun _ => none
  sibling := fun _ => none
  benutzt := fun _ => true

theorem gegenbeispiel2_form : hatForm gegenbeispiel2 = true := by decide
theorem gegenbeispiel2_elternVerletzt : elternKonsistent gegenbeispiel2 = false := by
  decide

/-- Counter-state 3: the declaration holds, but a sibling carries a foreign
    parent (none instead of the sibling's parent). -/
def gegenbeispiel3 : TreeState where
  n := 3
  parent := fun k => match k with | 1 => some 0 | _ => none
  child := fun k => match k with | 0 => some 1 | _ => none
  sibling := fun k => match k with | 1 => some 2 | _ => none
  benutzt := fun _ => true

theorem gegenbeispiel3_form : hatForm gegenbeispiel3 = true := by decide
theorem gegenbeispiel3_elternVerletzt : elternKonsistent gegenbeispiel3 = false := by
  decide

/-- Consistent twin: declaration, link agreement, occupancy closure and
    call safety all hold. -/
def beispielKonsistent : TreeState where
  n := 2
  parent := fun k => match k with | 1 => some 0 | _ => none
  child := fun k => match k with | 0 => some 1 | _ => none
  sibling := fun _ => none
  benutzt := fun _ => true

theorem beispielKonsistent_eltern : elternKonsistent beispielKonsistent = true := by
  decide
theorem beispielKonsistent_abgeschlossen :
    benutztAbgeschlossen beispielKonsistent = true := by
  decide
theorem beispielKonsistent_rufSicher : aufrufSicher beispielKonsistent 0 = true := by
  decide
theorem beispielKonsistent_lokal : lokalBenutzt beispielKonsistent = true := by decide

/-! ## Decision: the declaration implies neither consistency -/

/-- The declaration does not imply occupancy closure (counter-state 1). -/
theorem deklaration_schliesst_benutzt_nicht :
    hatForm gegenbeispiel1 = true ∧ benutztAbgeschlossen gegenbeispiel1 = false :=
  ⟨gegenbeispiel1_form, gegenbeispiel1_offen⟩

/-- The declaration does not imply parent consistency (counter-state 2). -/
theorem deklaration_schliesst_eltern_nicht :
    hatForm gegenbeispiel2 = true ∧ elternKonsistent gegenbeispiel2 = false :=
  ⟨gegenbeispiel2_form, gegenbeispiel2_elternVerletzt⟩

/-
   CUTS: what is not proved.
   - Proved here: the declaration shape (`hatForm`, the `D006`/`D007`/`D008`
     value shadow) implies neither link agreement (`elternKonsistent`,
     counter-states 2 and 3) nor occupancy closure (`benutztAbgeschlossen`,
     counter-state 1, the `einsammeln`/`blatt_loeschen` gap); the local
     one-edge clause (`lokalBenutzt`) closes occupancy transitively
     (`lokal_schliesst_fuel`) and hence call safety (`lokal_gibt_rufSicher`).
   - Only stated (definitions, no theorems): `elternKonsistent` as the
     proposed link invariant and `aufrufSicher` as the traverse-callee
     safety; no theorem lifts `elternKonsistent` from a local link clause
     (the mirror of `lokal_schliesst_fuel` for links is open).
   - Not modelled: the projection `World -> TreeState` is documented, not
     formalised (no simulation theorem between `Semantik.kette`/`Expr.reaches`
     and `erreichbar`); the GabbroV duty side (`programmlogik/` `RunsLoop*`,
     `Body.lean`) is untouched by design, so no bridge theorem to premise
     (b) `NutzerPflicht` is claimed; `sibling` cycles and fuel completeness
     (paths longer than `s.n` repeat a slot) are not proved.
   - Witness coverage: three inconsistent and one consistent concrete state,
     each with `decide`d equations; no for-all-over-syntax premise occurs in
     this file, so rule 3 requires no `_zeuge` (the task's witnesses are the
     four concrete states above).
-/

#print axioms ltB_true
#print axioms lokal_schliesst_fuel
#print axioms lokal_gibt_rufSicher
#print axioms deklaration_schliesst_benutzt_nicht
#print axioms deklaration_schliesst_eltern_nicht
#print axioms gegenbeispiel1_offen
#print axioms beispielKonsistent_rufSicher

end Gabbro.Grammatik.X86
