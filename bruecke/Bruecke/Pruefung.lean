module
public import Bruecke.Simulation
@[expose] public section


/-!
# S3, part 7: the per-unit conditions as Bool checks, with their soundness

`stimmigB u` decides the all-carried shape conditions, and `rangB u rk` the rank of the
call graph; `rangAuto u` computes a rank (the longest call path, with the function count as
fuel -- on a cycle the check fails). Each is closed per unit by `decide`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

def artPtrB (fn : UFn) : Bool :=
  (List.range fn.kinds.length).all fun j =>
    match fn.kinds[j]? with
    | some (.ptr ⟨0, ⟨true, _, none⟩, .table num⟩) =>
      match fn.params[j]? with
      | some (_, .ptr ⟨0, ⟨true, _, none⟩, .table num'⟩) => num' == num
      | _ => false
    | _ => true

def artB (fn : UFn) : Bool :=
  artPtrB fn && fn.kinds.all ArtSchlicht && fn.params.all ParamSchlicht

def tabEindB (u : UProg) : Bool :=
  (List.finRange u.tabs.length).all fun t =>
    match tabIdx u.tabs (tabAt u t).name with
    | .ok t' => t' == t
    | .error _ => false

def tabB (u : UProg) : Bool :=
  tabEindB u && u.tabs.all (fun t => t.werte.isEmpty)

def namenB (fn : UFn) : Bool := decide (fn.params.map (·.1)).Nodup

def oldNamen : List String := (List.range 9).map oldName

def freiB (fn : UFn) : Bool :=
  fn.params.all fun q => decide (q.1 ≠ "result") && decide (q.1 ∉ oldNamen)

def oldsB (u : UProg) (fn : UFn) : Bool :=
  fn.gives.all fun e =>
    match ensExpr u fn {} e with
    | some (_, A) => decide (A.olds.length ≤ 9)
    | none => true

def postB (u : UProg) (fn : UFn) : Bool := fn.gives.all fun e => (ensExpr u fn {} e).isSome

def schreibtB (u : UProg) (fn : UFn) : Bool :=
  fn.puts.all fun w => u.tabs.any (·.name == w)

/-- No `bool`, option or aggregate field and no `bool` result: the bridge speaks about numbers only
    (Body's shapes are `intIn`), so a unit with such a place is REFUSED here, by name, and
    the all-carried source duty is false. -/
def keinBoolB (u : UProg) : Bool :=
  u.tabs.all (fun t => t.bools.isEmpty && t.opts.isEmpty && t.werte.isEmpty) &&
    u.fns.all (fun f => !f.resBool && f.resTy.isNone && f.resOpt.isNone && f.resSum.isNone && f.resWhy.isNone)

def stimmigB (u : UProg) : Bool :=
  keinBoolB u && tabB u && u.fns.all (fun fn => fn.needs.isEmpty && fn.gruende == 0) && u.invs.isEmpty && u.globs.isEmpty &&
    u.fns.all fun fn =>
    artB fn && namenB fn && freiB fn && oldsB u fn && postB u fn && schreibtB u fn

/-- Generated transition bodies are lowered separately and have no Body simulation. -/
def ohneTransitionB (u : UProg) : Bool :=
  (List.finRange u.fns.length).all fun c => (transitionOfFn u c).isNone

theorem ohneTransitionB_ok {u : UProg} (h : ohneTransitionB u = true) :
    OhneGenerierteTransitions u := by
  intro c
  exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp h c (List.mem_finRange c))

theorem oldName_mem : ∀ i, oldName i ∈ oldNamen := by
  intro i
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | _ + 8 => simp [oldName, oldNamen]; exact ⟨8, by decide, rfl⟩

variable {u : UProg}

theorem artPtrB_ok {fn : UFn} (h : artPtrB fn = true) : ArtStimmtPtr fn := by
  intro j num w hp
  have hj : j < fn.kinds.length := by
    rcases Nat.lt_or_ge j fn.kinds.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hp; cases hp
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [hp] at this
  split at this
  · rename_i q w' num' hq
    have sameTable : num' = num := by simpa using this
    subst num'
    exact ⟨w', by rw [hq]; rfl⟩
  · cases this

theorem artB_ok {fn : UFn} (h : artB fn = true) : ArtStimmt fn := by
  simp only [artB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨artPtrB_ok h.1.1, h.1.2, h.2⟩

theorem tabEindB_ok (h : tabEindB u = true) :
    ∀ t : Fin u.tabs.length, tabIdx u.tabs (tabAt u t).name = .ok t := by
  intro t
  have := List.all_eq_true.mp h t (List.mem_finRange t)
  split at this
  · rename_i t' ht'
    rw [ht']
    have : t' = t := by simpa using this
    rw [this]
  · cases this

theorem tabB_ok (h : tabB u = true) : TabEindeutig u := by
  simp only [tabB, Bool.and_eq_true] at h
  refine ⟨tabEindB_ok h.1, fun t => ?_⟩
  have := List.all_eq_true.mp h.2 (tabAt u t) (List.get_mem _ _)
  exact List.isEmpty_iff.mp this

theorem freiB_ok {fn : UFn} (h : freiB fn = true) : NamenFrei fn := by
  intro q hq
  have := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨this.1, fun i e => ?_⟩
  have hm := oldName_mem i
  rw [← e] at hm
  exact this.2 hm

theorem oldsB_ok {fn : UFn} (h : oldsB u fn = true) : OldsKurz u fn := by
  intro e he
  have := List.all_eq_true.mp h e he
  split at this
  · rename_i x A hx
    rw [hx]
    exact of_decide_eq_true this
  · rename_i hx
    rw [hx]
    trivial

theorem postB_ok {fn : UFn} (h : postB u fn = true) : PostDef u fn :=
  fun e he => List.all_eq_true.mp h e he

theorem schreibtB_ok {fn : UFn} (h : schreibtB u fn = true) :
    ∀ w ∈ fn.puts, ∃ t : Fin u.tabs.length, (tabAt u t).name = w := by
  intro w hw
  have := List.all_eq_true.mp h w hw
  obtain ⟨x, hx, hxw⟩ := List.any_eq_true.mp this
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨⟨i, hi⟩, by simpa [tabAt] using hxw⟩

/-- **The name conditions, decided.** -/
theorem keinBoolB_ok (h : keinBoolB u = true) :
    (∀ t : Fin u.tabs.length, (tabAt u t).bools = [] ∧ (tabAt u t).opts = [] ∧ (tabAt u t).werte = []) ∧
      (∀ c : Fin u.fns.length, ErgSchlicht (fnAt u c)) := by
  simp only [keinBoolB, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun t => ?_, fun c => ?_⟩
  · have := List.all_eq_true.mp h1 (tabAt u t) (List.get_mem _ _)
    simp only [Bool.and_eq_true, List.isEmpty_iff] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := List.all_eq_true.mp h2 (fnAt u c) (List.get_mem _ _)
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Option.isNone_iff_eq_none] at this
    exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩

/-! ## The rank -/

/-- The longest call path from `n`, with fuel. -/
def tiefe (u : UProg) : Nat → String → Nat
  | 0, _ => 0
  | k + 1, n =>
    match fnSuch u n with
    | some f => (f.body.map fun st => match st with
        | .call g _ => tiefe u k g + 1
        | _ => 0).foldr max 0
    | none => 0

/-- A rank for every unit: the longest call path, the function count as fuel. -/
def rangAuto (u : UProg) : String → Nat := tiefe u (u.fns.length + 1)

def rangB (u : UProg) (rk : String → Nat) : Bool :=
  (List.finRange u.fns.length).all fun c =>
    (fnAt u c).body.all fun st =>
      match st with
      | .call g _ => decide (rk g < rk (fnAt u c).name)
      | _ => true

/-- **The rank, decided.** -/
theorem rang_of {rk : String → Nat} (h : rangB u rk = true) : Rang u rk := by
  intro c cname args hm
  have := List.all_eq_true.mp (List.all_eq_true.mp h c (List.mem_finRange c)) _ hm
  exact of_decide_eq_true this

end Gabbro.Bruecke
