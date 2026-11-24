module

public import Core.Ast.Semantik.ProgramRegistry
public import Core.Ast.Semantik.Auswertung

/-!
The program forms' control obligations belong with the instruction semantics.
Each instruction is an ideal and a concrete unit. Caller switches, tests and
back-edges are separate visible units, so none of them contributes stuttering.
The finite count of such units is stated independently of their stutter length.
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- Count semantic instructions, including a call, return or back-edge. -/
inductive Rahmen.LaufN (code : List Befehl) : Nat → Rahmen → Rahmen → Prop where
  | null : LaufN code 0 frame frame
  | step : before.stopp = none → before.rueckgabe = none →
      code[before.pc]? = some instruction →
      LaufN code n (instruction.auswerten before) after →
      LaufN code (n + 1) before after

def Rahmen.Aktiv (frame : Rahmen) : Prop := frame.stopp = none ∧ frame.rueckgabe = none

/-- Exiting a loop includes returning from its surrounding function or requesting its handler. -/
def SchleifenAusgang (first limit : Nat) (before after : Rahmen) : Prop :=
  after.stopp.isSome = true ∨ after.rueckgabe.isSome = true ∨
    after.fortsetzungen.length < before.fortsetzungen.length ∨
    (after.fortsetzungen.length = before.fortsetzungen.length ∧
      (after.pc < first ∨ limit ≤ after.pc))

def Binnen (code : List Befehl) (budget : Nat) (start : Rahmen) (goal : Rahmen → Prop) : Prop :=
  ∃ n out, n ≤ budget ∧ Rahmen.LaufN code n start out ∧ goal out

/-- A test that takes a pass consumes exactly one permit. The zero-budget
    branch requests its named handler only after the final test is true. -/
theorem pass_fortschritt (frame : Rahmen) (leaveAt : Nat) (handler : Option Identifier)
    (remaining : Nat) (count : frame.zaehler frame.pc = some remaining) :
    (frame.pass false leaveAt handler).pc = frame.pc + leaveAt ∧
    (frame.pass false leaveAt handler).zaehler frame.pc = none ∧
    (remaining = 0 →
      (frame.pass true leaveAt handler).stopp = some (.ueberlauf handler)) ∧
     (∀ n, remaining = n + 1 → (frame.pass true leaveAt handler).pc = frame.pc + 1 ∧
       (frame.pass true leaveAt handler).zaehler frame.pc = some n) := by
  constructor
  · rfl
  constructor
  · simpa [Rahmen.pass]
  constructor
  · intro hzero
    simpa [Rahmen.pass, count, hzero, Rahmen.halt]
  · intro n hn
    simpa [Rahmen.pass, count, hn]

/-- A target is entered with the checked positional arguments and a fresh local
    frame. Caller's locals, temporaries and loop state live in its continuation. -/
theorem directCall_fortschritt (frame : Rahmen) (site : Rufstelle) (target : Funktion)
    (lookup : Funktion.finde frame.funktionen site.name = some target)
    (typecheck : site.passt frame.funktionen = true)
    (args : List (Option Dynamisch))
    (bind : frame.rufArgumente 0 site.args target.parameter = some args)
    (recursive : target.misstAbstieg = true ∨ ∀ saved ∈ frame.fortsetzungen,
      saved.funktion.map Subtype.val ≠ some site.name.val)
    (notSelf : target.misstAbstieg = true ∨ frame.funktion.map Subtype.val ≠ some site.name.val) :
    let next := frame.ruf site.name site.args site.bind
    next.pc = target.adresse ∧ next.fortsetzungen.length = frame.fortsetzungen.length + 1 ∧
      next.funktion = some site.name ∧ next.mass = none ∧
      next.lokale = args.reverse ++ frame.globale.drop (frame.globale.length - target.konstanten) := by
  cases hb : site.bind with
  | none =>
    by_cases hm : target.misstAbstieg = true
    · simpa [Rahmen.ruf, lookup, bind, hb, hm]
    · have hrec := recursive.resolve_left hm
      have hself := notSelf.resolve_left hm
      have hno : ¬ ∃ x ∈ frame.fortsetzungen,
          Option.map Subtype.val x.funktion = some site.name.val := by
        rintro ⟨x, hx, hEq⟩
        exact hrec x hx hEq
      simpa [Rahmen.ruf, lookup, bind, hb, hm, hrec, hself, hno]
  | some written =>
    cases hr : target.result with
    | none =>
      have : False := by simpa [Rufstelle.passt, lookup, hb, hr] using typecheck
      exact this.elim
    | some declared =>
      have hfit : tyFits declared written = true := by
        have ht' : (site.args.length = target.parameter.length ∧
            ∀ (a b : Ty .value), (a, b) ∈ site.args.zip target.parameter → tyFits a b = true) ∧
            tyFits declared written = true := by
          simpa [Rufstelle.passt, lookup, hb, hr] using typecheck
        exact ht'.2
      by_cases hm : target.misstAbstieg = true
      · simpa [Rahmen.ruf, lookup, bind, hb, hr, hfit, hm]
      · have hrec := recursive.resolve_left hm
        have hself := notSelf.resolve_left hm
        have hno : ¬ ∃ x ∈ frame.fortsetzungen,
            Option.map Subtype.val x.funktion = some site.name.val := by
          rintro ⟨x, hx, hEq⟩
          exact hrec x hx hEq
        simpa [Rahmen.ruf, lookup, bind, hb, hr, hfit, hm, hrec, hself, hno]

theorem directCall_rueckkehr (callee : Rahmen) (saved : Fortsetzung)
    (stack : List Fortsetzung) (same : callee.fortsetzungen = saved :: stack)
    (value : Option Dynamisch) :
    let caller := callee.rueckkehr value
    caller.pc = saved.pc ∧ caller.temp = saved.temp ∧ caller.zaehler = saved.zaehler ∧
      caller.obergrenzen = saved.obergrenzen ∧ caller.funktion = saved.funktion ∧
      caller.mass = saved.mass ∧ caller.fortsetzungen = stack ∧
       caller.lokale = match saved.eingang with
         | none => saved.lokale
         | some written => value.bind (wertIn written) :: saved.lokale := by
  simp only [Rahmen.rueckkehr, same, true_and, and_true]
  rfl

/-- The nearest saved activation of the same function controls a recursive entry.
    A nonnegative entry measure is checked on every re-entry, with a strict decrease. -/
theorem function_decreases (frame : Rahmen) (name : Identifier) (slot : Nat) (value : Ganzzahl)
    (saved : Fortsetzung) (old : Nat) (current : frame.funktion = some name)
    (read : frame.zahl slot = some value)
    (prior : frame.fortsetzungen.find? (fun k => (k.funktion.map Subtype.val) == some name.val)
      = some saved) (oldMeasure : saved.mass = some old) :
    (0 ≤ value.zahl.wert ∧ value.zahl.wert.toNat < old →
      (frame.setzeMass slot).mass = some value.zahl.wert.toNat ∧
      (frame.setzeMass slot).pc = frame.pc + 1) ∧
    (¬ (0 ≤ value.zahl.wert ∧ value.zahl.wert.toNat < old) →
      (frame.setzeMass slot).stopp = some (.abstieg name)) := by
  constructor
  · intro h
    unfold Rahmen.setzeMass
    simp only [current, read, prior, oldMeasure]
    have hnonneg : 0 ≤ value.zahl.wert := h.1
    have hcast : (value.zahl.wert.toNat : Int) = value.zahl.wert := Int.toNat_of_nonneg hnonneg
    have hltInt' : (value.zahl.wert.toNat : Int) < (old : Int) := by exact_mod_cast h.2
    have hltInt : value.zahl.wert < (old : Int) := by simpa [hcast] using hltInt'
    have hnot : ¬ (old : Int) ≤ value.zahl.wert := not_le_of_gt hltInt
    have hnlt : ¬ value.zahl.wert < 0 := not_lt_of_ge hnonneg
    have hnle : ¬ old ≤ value.zahl.wert.toNat := not_le_of_gt h.2
    simpa [Rahmen.halt, hnlt, hnot, hnle]
  · intro hfail
    unfold Rahmen.setzeMass
    simp only [current, read, prior, oldMeasure]
    by_cases hv : value.zahl.wert < 0
    · simpa [Rahmen.halt, hv]
    · have hge : old ≤ value.zahl.wert.toNat := by omega
      simpa [Rahmen.halt, hv, hge]

theorem function_rekursionstiefe (mass : Nat → Nat) (depth : Nat)
    (decreases : ∀ i < depth, mass (i + 1) < mass i) :
    depth ≤ mass 0 := by
  have strong : ∀ d, (∀ i < d, mass (i + 1) < mass i) → d + mass d ≤ mass 0 := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.zero_add, le_refl]
    | succ d ih =>
      intro h
      have hd : ∀ i < d, mass (i + 1) < mass i := fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self d))
      have ih' := ih hd
      have step := h d (Nat.lt_succ_self d)
      omega
  have := strong depth decreases
  omega

inductive Rufpfad (table : List Funktion) : Identifier → Identifier → Prop where
  | direkt : Funktion.finde table source = some function → call ∈ function.ruft →
      Rufpfad table source call.name
  | weiter : Funktion.finde table source = some function → call ∈ function.ruft →
      Rufpfad table call.name target → Rufpfad table source target

theorem function_rekursiv_korrekt (table : List Funktion) (function : Funktion)
    (unique : (table.map (fun f => f.name.val)).Nodup)
    (member : function ∈ table) :
    Funktion.rekursiv table function = true ↔ Rufpfad table function.name function.name := by
  -- Mirror function_rekursionstiefe on simple paths after removing repeated intermediate vertices.
  sorry

/-- A program with any syntactic recursive cycle containing a function with a
    missing measure is refused at launch before it selects an entry frame. -/
theorem program_unbounded_refused (frame : Rahmen) (entry : Identifier) (bad : Funktion)
    (unique : (frame.funktionen.map (fun f => f.name.val)).Nodup)
    (firstBad : frame.funktionen.find? (fun f =>
      !f.misstAbstieg && Funktion.rekursiv frame.funktionen f) = some bad) :
    (Befehl.starte entry |>.auswerten frame).stopp = some (.unbeschraenkteRekursion bad.name) := by
  simpa [Befehl.auswerten, unique, firstBad, Rahmen.halt]

/-- One successful loop body segment either exits or reaches its back-edge on the
    same stack. Its budget includes all calls and nested loop instructions. -/
def SchleifenKoerper (code : List Befehl) (origin : Rahmen) (first limit body back budget : Nat) : Prop :=
  ∀ frame, (∃ n, Rahmen.LaufN code n origin frame) → frame.Aktiv →
    frame.pc = body → frame.fortsetzungen.length = origin.fortsetzungen.length →
    Binnen code budget frame (fun out =>
      SchleifenAusgang first limit origin out ∨
        out.Aktiv ∧ out.pc = back ∧ out.fortsetzungen.length = origin.fortsetzungen.length)

/-- One closed bound evaluation and setup, at most N+1 tests, and at most N
    bodies followed by a backward jump. A final true test requests the handler. -/
theorem boundedWhile_terminiert (a : Surface.BoundedWhileArgs scope result) (frame : Rahmen)
    (env : Umgebung scope) (initial : frame.pc = 0) (active : frame.Aktiv)
    (typed : frame.traegt env) (bodyBudget : Nat)
    (body : let f := (boundedWhileForm scope result).fragment a
      let test := (boundedWhileForm scope result).position a
      SchleifenKoerper f.code frame 0 f.code.length (test + 1) (f.code.length - 1) bodyBudget)
    (condition : let f := (boundedWhileForm scope result).fragment a
      let test := (boundedWhileForm scope result).position a
      ∀ atTest, (∃ n, Rahmen.LaufN f.code n frame atTest) →
        atTest.pc = test → atTest.fortsetzungen.length = frame.fortsetzungen.length →
        atTest.Aktiv → ((atTest.temp 0).bind alsBoolean).isSome = true) :
    let f := (boundedWhileForm scope result).fragment a
    let N := (a.bound.wert env).wert.toNat
    let bound := (expr 0 a.bound).code.length + 1 +
      (N + 1) * ((expr 0 a.condition).code.length + 1) + N * (bodyBudget + 1)
    Binnen f.code bound frame (SchleifenAusgang 0 f.code.length frame) := by
  -- Mirror expr_ergebnis_typ for bound and tests, then induct using pass_fortschritt.
  sorry

/-- The for setup computes the exact half-open range size from both static values.
    The two endpoint computations are separate; evaluating the upper endpoint
    does not overwrite the lower endpoint's value. -/
theorem forRange_passzahl (frame : Rahmen) (lower upper : Ganzzahl) (index : Ty .value)
    (readLower : frame.zahl 0 = some lower) (readUpper : frame.zahl 1 = some upper)
    (initial : Dynamisch) (fits : wertIn index lower.pack = some initial)
    (nonempty : lower.zahl.wert < upper.zahl.wert) (skipEmpty : Nat) :
    let next := (Befehl.forAnfang 0 1 index skipEmpty false false).auswerten frame
    next.pc = frame.pc + 1 ∧
      next.zaehler next.pc = some (upper.zahl.wert - lower.zahl.wert).toNat ∧
       next.lokale = some initial :: frame.lokale ∧ next.obergrenzen next.pc = some upper := by
  have hnot : ¬ upper.zahl.wert ≤ lower.zahl.wert := by omega
  simpa [Befehl.auswerten, readLower, readUpper, fits, hnot]

theorem forRange_leer (frame : Rahmen) (lower upper : Ganzzahl) (index : Ty .value)
    (readLower : frame.zahl 0 = some lower) (readUpper : frame.zahl 1 = some upper)
    (empty : upper.zahl.wert ≤ lower.zahl.wert) (skipEmpty : Nat) (missingHandler : Bool) :
    let next := (Befehl.forAnfang 0 1 index skipEmpty false missingHandler).auswerten frame
    next.pc = frame.pc + skipEmpty ∧ next.lokale = frame.lokale ∧ next.stopp = frame.stopp := by
  have hnot : ¬ lower.zahl.wert < upper.zahl.wert := by omega
  simpa [Befehl.auswerten, readLower, readUpper, empty, hnot]

theorem forRange_terminiert (a : Surface.ForRangeArgs scope result) (frame : Rahmen)
    (env : Umgebung scope) (initial : frame.pc = 0) (active : frame.Aktiv)
    (typed : frame.traegt env) (bodyBudget : Nat)
    (body : let f := (forRangeForm scope result).fragment a
      let test := (forRangeForm scope result).position a
      SchleifenKoerper f.code frame 0 f.code.length (test + 1) (f.code.length - 2) bodyBudget)
    (backEdge : let f := (forRangeForm scope result).fragment a
      ∀ back, (∃ n, Rahmen.LaufN f.code n frame back) →
        back.pc = f.code.length - 2 → back.fortsetzungen.length = frame.fortsetzungen.length →
        back.Aktiv → ∀ instruction, f.code[back.pc]? = some instruction →
        (instruction.auswerten back).Aktiv) :
    let f := (forRangeForm scope result).fragment a
    let N := ((a.upper.wert env).wert - (a.lower.wert env).wert).toNat
    let bound := (expr 0 a.lower).code.length + (expr 1 a.upper).code.length + 3 + N * (bodyBudget + 2)
    Binnen f.code bound frame (SchleifenAusgang 0 f.code.length frame) := by
  -- Mirror boundedWhile_terminiert using forRange_passzahl and the generated increment.
  sorry

/-- A finite table gives a total depth bound, even when recursive functions
    call each other. The saved activations are ordered from oldest to newest. -/
theorem function_stapeltiefe (names : List (List Char)) (upper : List Char → Nat)
    (frames : List (List Char × Nat))
    (declared : ∀ f ∈ frames, f.1 ∈ names ∧ f.2 ≤ upper f.1)
    (decreases : ∀ name ∈ names,
      ((frames.filter (fun f => f.1 == name)).map Prod.snd).Pairwise (fun old next => next < old)) :
    frames.length ≤ (names.map (fun name => upper name + 1)).sum := by
  have listBound : ∀ U : Nat, ∀ l : List Nat,
      l.Pairwise (fun old next => next < old) →
      (∀ v ∈ l, v ≤ U) → l.length ≤ U + 1 := by
    intro U
    induction U with
    | zero =>
      intro l hp hb
      cases l with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons v vs =>
        have hv : v = 0 := by
          have := hb v (by simp only [List.mem_cons_self, true_or])
          omega
        have hvs : vs = [] := by
          cases vs with
          | nil => rfl
          | cons b bs =>
            cases hp with
            | cons hhead htail =>
              have hb_lt : b < v := hhead b (by simp only [List.mem_cons_self, true_or])
              omega
        simp only [hvs, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]
        omega
    | succ U ih =>
      intro l hp hb
      cases l with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons v vs =>
        cases hp with
        | cons hhead htail =>
          have hv : v ≤ U + 1 := hb v (by simp only [List.mem_cons_self, true_or])
          have hb' : ∀ b ∈ vs, b ≤ U := by
            intro b hbmem
            have hb_lt : b < v := hhead b hbmem
            omega
          have ih' := ih vs htail hb'
          simp only [List.length_cons]
          omega
  have indicatorSum : ∀ (ns : List (List Char)) (x : List Char), x ∈ ns →
      1 ≤ (ns.map (fun n => if x == n then 1 else 0)).sum := by
    intro ns x hx
    induction ns with
    | nil => simpa using hx
    | cons n ns ih =>
      simp only [List.mem_cons] at hx
      rcases hx with hEq | hmem
      · subst n
        simp only [List.map_cons, List.sum_cons, beq_self_eq_true, ↓reduceIte]
        omega
      · simp only [List.map_cons, List.sum_cons]
        by_cases heq : (x == n) = true
        · rw [if_pos heq]
          omega
        · rw [if_neg heq]
          simpa only [Nat.zero_add] using ih hmem
  have splitSum : ∀ (ns : List (List Char)) (f : List Char × Nat) (fs : List (List Char × Nat)),
      (ns.map (fun n => ((f :: fs).filter (fun g => g.1 == n)).length)).sum =
      (ns.map (fun n => (if f.1 == n then 1 else 0) +
        (fs.filter (fun g => g.1 == n)).length)).sum := by
    intro ns f fs
    induction ns with
    | nil => simp only [List.map_nil, List.sum_nil]
    | cons n ns ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      by_cases heq : f.1 == n
      · simpa [List.filter_cons, heq, Nat.add_comm]
      · simpa [List.filter_cons, heq]
  have addSum : ∀ (ns : List (List Char)) (x : List Char) (fs : List (List Char × Nat)),
      (ns.map (fun n => (if x == n then 1 else 0) +
        (fs.filter (fun g => g.1 == n)).length)).sum =
      (ns.map (fun n => if x == n then 1 else 0)).sum +
      (ns.map (fun n => (fs.filter (fun g => g.1 == n)).length)).sum := by
    intro ns x fs
    induction ns with
    | nil => simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    | cons n ns ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega
  have countBound : ∀ name ∈ names,
      (frames.filter (fun f => f.1 == name)).length ≤ upper name + 1 := by
    intro name hname
    have hb := listBound (upper name) ((frames.filter (fun f => f.1 == name)).map Prod.snd)
      (decreases name hname) (by
        intro v hv
        rcases List.mem_map.mp hv with ⟨f, hf, rfl⟩
        have heqb : f.1 == name := (List.mem_filter.mp hf).2
        have heq : f.1 = name := by simpa using heqb
        simpa [heq] using (declared f (List.mem_of_mem_filter hf)).2)
    simpa using hb
  have cover : ∀ fs : List (List Char × Nat), (∀ f ∈ fs, f.1 ∈ names) →
      fs.length ≤ (names.map (fun n => (fs.filter (fun f => f.1 == n)).length)).sum := by
    intro fs
    induction fs with
    | nil => intro _; simp only [List.length_nil, List.filter_nil, List.map_const, List.sum_replicate, Nat.zero_le]
    | cons f fs ih =>
      intro h
      have hfname : f.1 ∈ names := h f (by simp only [List.mem_cons_self, true_or])
      have hfs : ∀ g ∈ fs, g.1 ∈ names := by
        intro g hg
        exact h g (by simp only [List.mem_cons, hg, or_true])
      have ih' := ih hfs
      rw [splitSum names f fs, addSum names f.1 fs]
      have hind := indicatorSum names f.1 hfname
      simp only [List.length_cons]
      omega
  have sumBound : ∀ ns : List (List Char),
      (∀ n ∈ ns, (frames.filter (fun f => f.1 == n)).length ≤ upper n + 1) →
      (ns.map (fun n => (frames.filter (fun f => f.1 == n)).length)).sum ≤
        (ns.map (fun n => upper n + 1)).sum := by
    intro ns hb
    induction ns with
    | nil => simp only [List.map_nil, List.sum_nil, le_refl]
    | cons n ns ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hb n (by simp only [List.mem_cons_self, true_or]))
        (ih (by intro m hm; exact hb m (by simp only [List.mem_cons, hm, or_true])))
  exact le_trans (cover frames (by intro f hf; exact (declared f hf).1)) (sumBound names countBound)

theorem program_eintritt (frame : Rahmen) (entry : Identifier) (target : Funktion)
    (unique : (frame.funktionen.map (fun f => f.name.val)).Nodup)
    (bounded : ∀ f ∈ frame.funktionen, Funktion.rekursiv frame.funktionen f = true → f.misstAbstieg = true)
    (resolved : ∀ call ∈ frame.funktionen.flatMap Funktion.ruft, call.passt frame.funktionen = true)
    (lookup : Funktion.finde frame.funktionen entry = some target)
    (parameters : target.parameter = []) (initial : frame.funktion = none ∧ frame.fortsetzungen = []) :
    let entered := (Befehl.starte entry).auswerten frame
    entered.pc = target.adresse ∧ entered.funktion = some entry ∧
      entered.lokale = frame.globale.drop (frame.globale.length - target.konstanten) ∧
       entered.fortsetzungen.length = 1 := by
  have noRec : frame.funktionen.find? (fun f =>
      !f.misstAbstieg && Funktion.rekursiv frame.funktionen f) = none := by
    simp only [List.find?_eq_none]
    intro f hf
    by_cases hrec : Funktion.rekursiv frame.funktionen f = true
    · have hm := bounded f hf hrec
      simpa [hm, hrec]
    · simpa [hrec]
  have noBad : (frame.funktionen.flatMap Funktion.ruft).find? (fun call =>
      !(call.passt frame.funktionen)) = none := by
    simp only [List.find?_eq_none]
    intro call hc
    have hp := resolved call hc
    simpa [hp]
  have hstep : (Befehl.starte entry |>.auswerten frame) =
      ({ frame with lokale := [] } : Rahmen).ruf entry [] target.result := by
    simpa [Befehl.auswerten, unique, noRec, noBad, lookup, parameters]
  rw [hstep]
  have typecheck : (⟨entry, [], target.result⟩ : Rufstelle).passt frame.funktionen = true := by
    cases hr : target.result with
    | none => simpa [Rufstelle.passt, lookup, parameters, hr]
    | some declared =>
      have hfit : tyFits declared declared = true := by cases declared <;> simpa [tyFits]
      simpa [Rufstelle.passt, lookup, parameters, hr, hfit]
  have hrec : target.misstAbstieg = true ∨
      ∀ saved ∈ ({ frame with lokale := [] } : Rahmen).fortsetzungen,
        saved.funktion.map Subtype.val ≠ some entry.val := by
    right
    intro saved hsaved
    exfalso
    simpa [initial.2] using hsaved
  have hself : target.misstAbstieg = true ∨
      ({ frame with lokale := [] } : Rahmen).funktion.map Subtype.val ≠ some entry.val := by
    right
    rw [initial.1]
    change ¬ (none : Option Text.RawText) = some entry.val
    simpa
  obtain ⟨hpc, hstack, hfun, _hmass, hloc⟩ := directCall_fortschritt
    ({ frame with lokale := [] } : Rahmen) ⟨entry, [], target.result⟩ target
    lookup typecheck [] (by simpa [Rahmen.rufArgumente, parameters]) hrec hself
  exact ⟨hpc, hfun, by simpa using hloc, by simpa [initial.2] using hstack⟩

theorem constant_initialisiert (a : Surface.ConstantArgs scope) (env : Umgebung scope)
    (frame : Rahmen) (active : frame.Aktiv) (typed : frame.traegt env) (initial : frame.pc = 0) :
    let code := ((constantForm scope).fragment a).code
    ∃ value, wertIn a.written.type ⟨a.type, a.value.wert env⟩ = some value ∧
      Binnen code code.length frame (fun out =>
        out.pc = code.length ∧ out.lokale = some value :: frame.lokale ∧
          out.globale = some value :: frame.globale) := by
  -- Mirror expr_ergebnis_typ, then apply wertIn_widen before committing the immutable value.
  sorry

/-- Counted transitions are public step units even when they transfer control
    backwards or across a caller boundary. A bound of zero refers to private steps. -/
theorem program_stotterLaenge (p : Fragment) (platform : Plattform) (b : Befehl) :
    (p.einheit platform).stotterLaenge b = 0 := by
  rfl

end Gabbro.Core.Ast.Semantik
