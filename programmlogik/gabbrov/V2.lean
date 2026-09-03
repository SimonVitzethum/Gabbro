/-
  File:    gabbrov/V2.lean
  Subject: **V2's CHEAP half of `dokumente/GABBROV.md` §5 -- VACUITY, and only that.**

  §5 names two assumption checks and `messung/GABBROV-V1.md` §6 measured that they have
  opposite costs:

    contradiction -- "does the assumption set have a model?"  needs the eight assumptions as
                     FORMULAS, and every one of them is a German prose sentence. `G5` can
                     today neither fire nor be cleared. NOT BUILT, and not started.
    vacuity       -- "is a precondition unsatisfiable?"       needs no assumption
                     formalisation at all. The preconditions are obligation-side objects and
                     the fragment of `V1.lean` already holds them. THIS FILE.

  WHY VACUITY IS WORTH A FILE
    A `requires` that no state meets makes its postcondition hold trivially. The obligation
    then PASSES, and passing it proves nothing -- §5 puts that next to `W16` and the aborting
    measurement run, and the class is the same: a tool that looks plausible and measures
    nothing. **The sharpest form of it is §4 below**, where an obligation whose postcondition
    is literally `False` passes.

  THE THREE OUTCOMES, because §4 of `GABBROV.md` demands three and not two
    VACUOUS      -- the precondition is unsatisfiable, and `vacuous_sound` PROVES that no
                    world meets it. The obligation says nothing.
    NOT VACUOUS  -- a world meeting the precondition is EXHIBITED and `decide` checks it.
    UNDECIDED    -- the precondition is outside the atom fragment this checker decides. Named,
                    not approximated (§7: *"A specification outside the fragment is rejected,
                    not approximated"*).

  WHAT THIS FILE DOES NOT MEASURE, named rather than left out
    * **Satisfiability of a precondition CONJOINED with the program's declared invariants.**
      A `requires` can be satisfiable alone and unsatisfiable together with a `table …
      invariant`. This run asks the weaker question, which is the one §5 asks. *The stronger
      one needs the invariants as premises, and that is V3's shape, not this one's.*
    * **Whether a non-vacuous obligation is PROVABLE.** `V1.lean` says the same of itself:
      every row is a definition, not a theorem.
-/
import Gabbro.Body

set_option autoImplicit false

open Gabbro.Body

namespace GabbroV.V2

/-! ## 0. The checker

    A precondition in the shape the fragment actually produces: a conjunction of constraints
    on places. `requires s.used`, `requires q.phase == DRIVER`, `requires cap != 0` -- every
    `requires` conjunct among the 66 that is not itself a quantified invariant has this form.
-/

/-- One conjunct of a precondition. -/
inductive Atom where
  | eq (p : Place) (v : Value)
  | ne (p : Place) (v : Value)
  deriving DecidableEq

/-- A precondition: the conjunction of its atoms. -/
abbrev Pre := List Atom

/-- What it means for a world to meet one atom. -/
def Atom.sat (w : World) : Atom → Bool
  | .eq p v => w p == v
  | .ne p v => !(w p == v)

/-- What it means for a world to meet a precondition. -/
def holds (w : World) (pre : Pre) : Bool := pre.all (Atom.sat w)

/-- **Two atoms that cannot both hold.** Three shapes, and the fourth is expressly `false`:
    two disequations on one place are always jointly satisfiable, because `Value` has more
    than two inhabitants (`int n` for every `n`). *A checker that answered `true` here would
    be unsound in the direction that matters.* -/
def clash : Atom → Atom → Bool
  | .eq p v, .eq q u => p == q && !(v == u)
  | .eq p v, .ne q u => p == q && (v == u)
  | .ne p v, .eq q u => p == q && (v == u)
  | .ne _ _, .ne _ _ => false

/-- **THE CHECK.** A precondition is vacuous when two of its atoms clash. -/
def vacuous : Pre → Bool
  | []       => false
  | a :: rest => rest.any (clash a) || vacuous rest

/-! ## 1. Soundness -- the theorem that makes the verdict mean something

    `R11`: a guardian nobody has ever seen say no is an ornament, and a guardian that says no
    for no reason is worse. **If `vacuous` fires, no world meets the precondition** -- proved,
    not asserted, because a false VACUOUS verdict would condemn a real obligation.
-/

theorem clash_sound {a b : Atom} {w : World}
    (h : clash a b = true) (ha : a.sat w = true) (hb : b.sat w = true) : False := by
  cases a with
  | eq p v =>
    cases b with
    | eq q u =>
      simp [clash] at h
      simp [Atom.sat] at ha hb
      exact h.2 (by rw [← ha, ← hb, h.1])
    | ne q u =>
      simp [clash] at h
      simp [Atom.sat] at ha hb
      exact hb (by rw [← h.1, ha, h.2])
  | ne p v =>
    cases b with
    | eq q u =>
      simp [clash] at h
      simp [Atom.sat] at ha hb
      exact ha (by rw [h.1, hb, ← h.2])
    | ne q u => simp [clash] at h

/-- **No world meets a precondition the check condemns.** -/
theorem vacuous_no_model : ∀ (pre : Pre) (w : World),
    vacuous pre = true → holds w pre = true → False := by
  intro pre
  induction pre with
  | nil => intro _ h _; simp [vacuous] at h
  | cons a rest ih =>
    intro w h hh
    simp only [holds, List.all_cons, Bool.and_eq_true] at hh
    obtain ⟨ha, hrest⟩ := hh
    simp only [vacuous, Bool.or_eq_true, List.any_eq_true] at h
    cases h with
    | inl hany =>
      obtain ⟨b, hb, hcl⟩ := hany
      have hbsat : b.sat w = true := by
        simp only [List.all_eq_true] at hrest
        exact hrest b hb
      exact clash_sound hcl ha hbsat
    | inr hr => exact ih w hr hrest

/-- **If the check fires, the precondition is unsatisfiable.** -/
theorem vacuous_sound (pre : Pre) (h : vacuous pre = true) (w : World) : holds w pre = false := by
  cases hh : holds w pre with
  | false => rfl
  | true  => exact (vacuous_no_model pre w h hh).elim

/-! ## 2. The witness side -- and it is a CONSTRUCTION, not a search

    The other direction needs a world, and for this atom fragment the world can be BUILT from
    the precondition itself: bind every `eq`-place to its value and leave the rest `absent`.
    *A bounded search over a guessed space would answer "undecided" where the fragment can
    answer "no"; the canonical world answers it by construction.*
-/

/-- A world from a finite list of bindings; everything else is `absent`. -/
def mk (bs : List (Place × Value)) : World := fun q =>
  match bs.find? (fun b => b.1 == q) with
  | some b => b.2
  | none   => .absent

/-- **The canonical witness** for a precondition: every `eq` honoured, everything else
    `absent`. Whether it really meets the precondition is checked per row by `decide` below
    rather than proved in general -- *`ne p .absent` on a place no `eq` mentions is the one
    shape it fails on, and no row among the 66 has it.* -/
def canon (pre : Pre) : World :=
  mk (pre.filterMap fun a => match a with | .eq p v => some (p, v) | .ne _ _ => none)

/-- The verdict, with §4's three outcomes. -/
inductive Verdict where
  | vacuous
  | notVacuous
  | undecided
  deriving DecidableEq, Repr

/-- The check applied: `undecided` is never produced here, because a precondition that
    reaches this function is already in the atom fragment. The rows that are NOT are listed
    in §5 and carry their witness directly. -/
def verdict (pre : Pre) : Verdict :=
  if vacuous pre then .vacuous
  else if holds (canon pre) pre then .notVacuous
  else .undecided

/-! ## 3. The preconditions of the sayable obligations, one by one

    Which rows have a precondition at all is a question about the ROW, and it is answered by
    reading `V1.lean`: a row has one exactly when its `Prop` carries an antecedent that
    constrains a state. Rows that are unconditional invariants (`L15`, `L18`-`L22`, `L41`,
    `L64`, …) have none, and a check over them would be a check over nothing.

    Quantified parameters are instantiated at a concrete index -- satisfiability is an
    existential, so one witness settles it.
-/

-- F1 -- Cap space
def preL01 : Pre := [.eq (.slot "c" 1 "parent") .absent]
def preL02 : Pre := [.eq (.slot "c" 1 "next_sibling") (.present 2)]
def preL06 : Pre := [.eq (.slot "c" 1 "prev_sibling") (.present 0)]
def preL08 : Pre := [.eq (.slot "o" 1 "refcount") (.int 5)]
/-- L10 is a CASE SPLIT, and each arm has its own precondition. Both are checked. -/
def preL10a : Pre := [.eq (.slot "o" 1 "refcount") (.int 0)]
def preL10b : Pre := [.ne (.slot "o" 1 "refcount") (.int 0)]
def preL14 : Pre := [.eq (.slot "c" 1 "used") (.bool true)]

-- F3 -- IOMMU / endpoints
def preL28 : Pre := [.eq (.slot "e" 0 "quiescing") (.bool true)]
def preL31 : Pre := [.eq (.slot "e" 0 "senders_count") (.int 32)]
def preL33 : Pre := [.eq (.slot "t" 1 "frame") (.present 8)]
def preL35 : Pre := [.eq (.slot "t" 1 "core") (.int 0)]

-- F4 -- the virtio driver's status ladder. **Four preconditions, four rungs, and they are
-- pairwise incompatible -- which is a property of the LADDER and not a defect.**
def preL36 : Pre := [.eq (.global "DEVICE_STATUS") (.int 0)]
def preL37 : Pre := [.eq (.global "DEVICE_STATUS") (.int 1)]
def preL38 : Pre := [.eq (.global "DEVICE_STATUS") (.int 3)]
def preL39 : Pre := [.eq (.global "DEVICE_STATUS") (.int 11)]
def preL40 : Pre := [.eq (.global "DEVICE_STATUS") (.int 7)]

-- F5 -- the block service
def preL43 : Pre := [.eq (.global "notification") (.int 1)]
def preL44 : Pre := [.eq (.global "capacity") .absent]
def preL47 : Pre := [.eq (.global "EP_revoked") (.bool true)]
def preL49 : Pre := [.eq (.field "m" "start") (.int 16), .eq (.field "m" "len") (.int 32)]

-- F6..F9
def preL53 : Pre := [.eq (.global "frei_min") .absent]
def preL56 : Pre := [.eq (.slot "st" 0 "groesse") (.int 4096),
                     .eq (.slot "st" 0 "frei_min") (.int 1024),
                     .eq (.slot "st" 0 "irq_tiefe_max") (.int 256)]
def preL58 : Pre := [.eq (.global "phase") (.int 0)]
def preL59 : Pre := [.eq (.global "aufgeloest") (.present 2)]
def preL60a : Pre := [.eq (.global "aufgeloest") (.present 2)]
def preL60b : Pre := [.eq (.global "aufgeloest") .absent]
def preL61 : Pre := [.eq (.slot "pt" 0 "PS") (.int 0)]
def preL62 : Pre := [.eq (.slot "pt" 0 "PS") (.int 1)]
def preL63 : Pre := [.eq (.field "abbildung" "level") (.int 3)]

-- F10 -- and this row is an ASSUMPTION since 2026-09-03 (`messung/GABBROV-V2.md` §1), so it
-- is measured and then subtracted at the census rather than left in silently.
def preL66 : Pre := [.eq (.global "tokens_left") (.int 5)]

/-- Every precondition of §3, with its row name. -/
def register : List (String × Pre) :=
  [("L01", preL01), ("L02", preL02), ("L06", preL06), ("L08", preL08),
   ("L10a", preL10a), ("L10b", preL10b), ("L14", preL14),
   ("L28", preL28), ("L31", preL31), ("L33", preL33), ("L35", preL35),
   ("L36", preL36), ("L37", preL37), ("L38", preL38), ("L39", preL39), ("L40", preL40),
   ("L43", preL43), ("L44", preL44), ("L47", preL47), ("L49", preL49),
   ("L53", preL53), ("L56", preL56), ("L58", preL58), ("L59", preL59),
   ("L60a", preL60a), ("L60b", preL60b), ("L61", preL61), ("L62", preL62),
   ("L63", preL63), ("L66", preL66)]

/-- **The run.** Every entry of the register, checked. -/
def lauf : List (String × Verdict) := register.map (fun r => (r.1, verdict r.2))

/-- **NOT ONE of them is vacuous** -- and the count is computed, not written down. -/
def zahlVacuous  : Nat := (lauf.filter (fun r => r.2 == Verdict.vacuous)).length
def zahlNotVac   : Nat := (lauf.filter (fun r => r.2 == Verdict.notVacuous)).length
def zahlUndecided: Nat := (lauf.filter (fun r => r.2 == Verdict.undecided)).length

/-- The whole register comes back `notVacuous`, checked by the kernel and not by a reading. -/
example : zahlVacuous = 0 := by decide
example : zahlUndecided = 0 := by decide
example : zahlNotVac = 30 := by decide

/-! ## 4. The speech test -- and it FIRES

    `R11` again, and this time it is the whole point: **a vacuity check that has never said
    VACUOUS is an ornament**, and a clean result over thirty rows is worth exactly as much as
    the check's ability to have come out otherwise. So the check is driven against a
    precondition written to be unsatisfiable.
-/

/-- **A deliberately vacuous obligation.** `L41`'s own fragment declares
    `tagged type BufPhase = { Driver, Device }` and its obligation is that a buffer is in
    exactly one of the two. This `requires` demands BOTH -- the shape a `requires` takes when
    a conjunct is added to an existing one without reading it. -/
def preVac : Pre := [.eq (.slot "q" 3 "phase") (.int 0), .eq (.slot "q" 3 "phase") (.int 1)]

/-- **The check fires.** -/
example : verdict preVac = Verdict.vacuous := by decide

/-- And it fires for the RIGHT reason: `vacuous_sound` turns the verdict into a statement
    about every world there is, not about the one the checker looked at. -/
theorem preVac_unsat : ∀ w : World, holds w preVac = false :=
  vacuous_sound preVac (by decide)

/-- **The second shape**, and the checker must catch it too: an equation and a disequation on
    one place. *A checker that only compared two equations would pass this.* -/
def preVac2 : Pre := [.eq (.global "capacity") (.int 0), .ne (.global "capacity") (.int 0)]
example : verdict preVac2 = Verdict.vacuous := by decide

/-- **The half that makes the other half mean anything.** Two atoms that do NOT clash, on the
    same place and on different ones, must come back `notVacuous`. A checker that answered
    `vacuous` whenever a place occurred twice would pass every line above and be useless. -/
def preSat : Pre := [.eq (.slot "q" 3 "phase") (.int 0), .ne (.slot "q" 3 "phase") (.int 1)]
example : verdict preSat = Verdict.notVacuous := by decide

/-- Two disequations on ONE place are satisfiable -- `Value` has more than two inhabitants.
    *This is the line that would fall if `clash` returned `true` for `.ne`/`.ne`.* -/
def preTwoNe : Pre := [.ne (.global "x") (.int 0), .ne (.global "x") (.int 1)]
example : verdict preTwoNe = Verdict.notVacuous := by decide

/-! ### And WHY a vacuous precondition matters -- the sharpest form

    An obligation with an unsatisfiable precondition holds **whatever its postcondition
    says**, and the demonstration below takes the postcondition all the way to `False`.
-/

/-- An obligation in the shape of the 66: a precondition on the pre-state, a claim about the
    post-state. Here the claim is `False`. -/
def LVac (s _s' : State) : Prop := holds s.world preVac = true → False

/-- **It passes.** No program was consulted, no body was executed, and the obligation whose
    postcondition is `False` is a theorem. *That is what a vacuity check is for, and it is why
    a `passed` without one is worth nothing.* -/
theorem LVac_passes : ∀ s s' : State, LVac s s' := by
  intro s _ h
  rw [preVac_unsat s.world] at h
  exact Bool.noConfusion h

/-! ## 5. The four rows the atom fragment does NOT decide, and their witnesses

    `L05`, `L09`, `L16` and `L27` are preservation obligations whose precondition is a
    QUANTIFIED INVARIANT (`cdt_wohlgeformt`, `antwortpflicht_paarig`), not a conjunction of
    place constraints. §0's checker is honest about them -- they never reach it. **They are
    still answered**, by exhibiting a world, which is the same currency the checker deals in.
-/

/-- `reachesIn` and `sl`, as `V1.lean` defines them. Repeated rather than imported, because
    `V1.lean` is a measurement file and importing it would make this one's `#eval` depend on
    that one's census. -/
def reachesIn (w : World) (c : String) (f : String) : Nat → Int → Int → Bool
  | 0,     s, t => decide (s = t)
  | n + 1, s, t =>
      if s = t then true
      else match w (.slot c s f) with
           | .present k => reachesIn w c f n k t
           | _          => false

abbrev sl (w : World) (c : String) (s : Int) (f : String) : Value := w (.slot c s f)

/-- A cap space whose slots 1 and 2 both reach the root 0 through `parent`. -/
def wCdt : World := mk [(.slot "c" 2 "parent", .present 1), (.slot "c" 1 "parent", .present 0)]

/-- **`L05`, `L09`, `L16` -- `cdt_wohlgeformt` is satisfiable**, so none of the three is
    vacuous. Written out over the domain rather than through `allD`, which is not a
    `Decidable` shape. -/
example : reachesIn wCdt "c" "parent" 4 1 0 = true := by decide
example : reachesIn wCdt "c" "parent" 4 2 0 = true := by decide

/-- **`L27` -- `antwortpflicht_paarig` is satisfiable.** An endpoint with neither field set
    meets the biconditional; so does one with both. -/
def wPaar : World := mk [(.slot "e" 0 "caller", .present 7), (.slot "e" 0 "reply_owner", .present 7)]
example : (sl wPaar "e" 0 "caller" = .absent) ↔ (sl wPaar "e" 0 "reply_owner" = .absent) := by
  constructor <;> intro h <;> simp [sl, wPaar, mk] at h
example : (sl (mk []) "e" 0 "caller" = .absent) ↔ (sl (mk []) "e" 0 "reply_owner" = .absent) := by
  constructor <;> intro _ <;> rfl

/-! ## 6. A NEIGHBOURING pathology the run found, and it is not vacuity

    Vacuity is *"the precondition admits no state"*. Two rows have the opposite defect: the
    precondition admits states, and the postcondition then follows from the PRECONDITION
    ALONE, with no reference to the program. **The obligation is a tautology.**

    `L44` and `L53` both read *"never read yet is distinguishable from zero"* and both were
    written as `x = absent → x ≠ int 0`. In the shared `Value` that is a theorem about the
    datatype: `absent` and `int 0` are different constructors. *The obligation the fragment
    MEANT is a statement about the model's expressiveness; what stands is a statement about
    Lean's `Value`, and no program can fail it.*
-/

theorem L44_is_a_tautology (w : World) :
    w (.global "capacity") = .absent → w (.global "capacity") ≠ .int 0 := by
  intro h; rw [h]; decide

theorem L53_is_a_tautology (w : World) :
    w (.global "frei_min") = .absent → w (.global "frei_min") ≠ .int 0 := by
  intro h; rw [h]; decide

/-- **Both hold of the EMPTY world**, which contains no program at all -- the same
    demonstration as `LVac_passes`, one pathology over. -/
example : (mk []) (.global "capacity") = .absent → (mk []) (.global "capacity") ≠ .int 0 :=
  L44_is_a_tautology (mk [])

/-! ## 7. The count, read off THIS file

    A number in a comment drifts away from the file beneath it, so these are computed.
-/

def zahlMitVorbedingung : Nat := register.length
def zahlAtomfragment    : Nat := register.length
def zahlDirektBezeugt   : Nat := 4   -- L05, L09, L16, L27

#eval s!"register entries (L10 and L60 each contribute two arms): {zahlMitVorbedingung}"
#eval s!"  vacuous:      {zahlVacuous}"
#eval s!"  not vacuous:  {zahlNotVac}"
#eval s!"  undecided:    {zahlUndecided}"
#eval s!"outside the atom fragment, witnessed directly: {zahlDirektBezeugt}"

end GabbroV.V2
