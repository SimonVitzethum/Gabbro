import Bruecke.Simulation

/-!
# S3, part 7: the per-unit conditions as Bool checks, with their soundness

`stimmigB u` decides the name conditions `Stimmig u` rests on, and `rangB u rk` the rank of the
call graph; `rangAuto u` computes a rank (the longest call path, with the function count as
fuel -- on a cycle the check fails). Each is closed per unit by `decide`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

def artB (fn : UFn) : Bool :=
  (List.range fn.parten.length).all fun j =>
    match fn.parten[j]? with
    | some (.ptr num _) =>
      match fn.params[j]? with
      | some (_, .ptr num' _) => num' == num
      | _ => false
    | _ => true

def tabB (u : UProg) : Bool :=
  (List.finRange u.tabellen.length).all fun t =>
    match tabIdx u.tabellen (tabAt u t).name with
    | .ok t' => t' == t
    | .error _ => false

def namenB (fn : UFn) : Bool := decide (fn.params.map (·.1)).Nodup

def oldNamen : List String := (List.range 9).map oldName

def freiB (fn : UFn) : Bool :=
  fn.params.all fun q => decide (q.1 ≠ "result") && decide (q.1 ∉ oldNamen)

def oldsB (u : UProg) (fn : UFn) : Bool :=
  fn.sichert.all fun e =>
    match ensExpr u fn {} e with
    | some (_, A) => decide (A.olds.length ≤ 9)
    | none => true

def postB (u : UProg) (fn : UFn) : Bool := fn.sichert.all fun e => (ensExpr u fn {} e).isSome

def schreibtB (u : UProg) (fn : UFn) : Bool :=
  fn.schreibt.all fun w => u.tabellen.any (·.name == w)

def stimmigB (u : UProg) : Bool :=
  tabB u && u.fns.all fun fn =>
    artB fn && namenB fn && freiB fn && oldsB u fn && postB u fn && schreibtB u fn

theorem oldName_mem : ∀ i, oldName i ∈ oldNamen := by
  intro i
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | _ + 8 => simp [oldName, oldNamen]; exact ⟨8, by decide, rfl⟩

variable {u : UProg}

theorem artB_ok {fn : UFn} (h : artB fn = true) : ArtStimmt fn := by
  intro j num w hp
  have hj : j < fn.parten.length := by
    rcases Nat.lt_or_ge j fn.parten.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hp; cases hp
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simp only [hp] at this
  split at this
  · rename_i q num' w' hq
    refine ⟨w', ?_⟩
    rw [hq]
    simp only [Option.map_some, Option.some.injEq, Ty.ptr.injEq, and_true]
    simpa using this
  · cases this

theorem tabB_ok (h : tabB u = true) : TabEindeutig u := by
  intro t
  have := List.all_eq_true.mp h t (List.mem_finRange t)
  split at this
  · rename_i t' ht'
    rw [ht']
    have : t' = t := by simpa using this
    rw [this]
  · cases this

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
    ∀ w ∈ fn.schreibt, ∃ t : Fin u.tabellen.length, (tabAt u t).name = w := by
  intro w hw
  have := List.all_eq_true.mp h w hw
  obtain ⟨x, hx, hxw⟩ := List.any_eq_true.mp this
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨⟨i, hi⟩, by simpa [tabAt] using hxw⟩

/-- **The name conditions, decided.** -/
theorem stimmig_of (h : stimmigB u = true) : Stimmig u := by
  simp only [stimmigB, Bool.and_eq_true] at h
  obtain ⟨ht, hf⟩ := h
  have hc : ∀ c : Fin u.fns.length, (artB (fnAt u c) && namenB (fnAt u c) && freiB (fnAt u c) &&
      oldsB u (fnAt u c) && postB u (fnAt u c) && schreibtB u (fnAt u c)) = true :=
    fun c => List.all_eq_true.mp hf _ (List.get_mem _ _)
  simp only [Bool.and_eq_true] at hc
  exact ⟨tabB_ok ht, fun c => artB_ok (hc c).1.1.1.1.1, fun c => (of_decide_eq_true (hc c).1.1.1.1.2 : ((fnAt u c).params.map (·.1)).Nodup),
    fun c => freiB_ok (hc c).1.1.1.2, fun c => oldsB_ok (hc c).1.1.2, fun c => postB_ok (hc c).1.2,
    fun c => schreibtB_ok (hc c).2⟩

/-! ## The rank -/

/-- The longest call path from `n`, with fuel. -/
def tiefe (u : UProg) : Nat → String → Nat
  | 0, _ => 0
  | k + 1, n =>
    match fnSuch u n with
    | some f => (f.saetze.map fun st => match st with
        | .call g _ => tiefe u k g + 1
        | _ => 0).foldr max 0
    | none => 0

/-- A rank for every unit: the longest call path, the function count as fuel. -/
def rangAuto (u : UProg) : String → Nat := tiefe u (u.fns.length + 1)

def rangB (u : UProg) (rk : String → Nat) : Bool :=
  (List.finRange u.fns.length).all fun c =>
    (fnAt u c).saetze.all fun st =>
      match st with
      | .call g _ => decide (rk g < rk (fnAt u c).name)
      | _ => true

/-- **The rank, decided.** -/
theorem rang_of {rk : String → Nat} (h : rangB u rk = true) : Rang u rk := by
  intro c cname args hm
  have := List.all_eq_true.mp (List.all_eq_true.mp h c (List.mem_finRange c)) _ hm
  exact of_decide_eq_true this

end Gabbro.Bruecke
