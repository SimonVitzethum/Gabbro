module
public import Bruecke.Kette.Mass.Pflicht
public import Bruecke.Simulation
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
@[expose] public section

/-!
# The source measure on Body states

A function's `decreases` clause (`UFn.decreases`, one arithmetic expression over its entry
parameters and checked constants) is read here on a Body binding: `quellWert` evaluates it
exactly as `SourceValue` denotes it, a parameter through the Body local of its name, a
constant through `measureConstants`. `massTupel` is the tuple the clause stands for: empty
without a clause, one component with one.

`massTupel_wert` is the preservation theorem against the canonical measure: on a Body binding
that reads every parameter at its position (`LRel`), the Body tuple IS the exported
`Mass.wert` of the lowered measure (`Measures.Export`, the measure `lowerAllg` checks). At the
bridge's entry state (`eintritt`) this needs nothing but unique parameter names
(`massTupel_eintritt`), and `massTupel_faellt` reads the canonical gate's test (`lexLt` of
the exported values, what `massTor` asks) as a fall of the Body source value.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Measures

/-- The binary operators of a measure, with the values `SourceValue` gives them. -/
def binU (op : String) (x y : Int) : Option Int :=
  if op = "+" then some (x + y)
  else if op = "-" then some (x - y)
  else if op = "*" then some (x * y)
  else if op = "/" then some (x.tdiv y)
  else if op = "%" then some (x.tmod y)
  else if op = "&" then some ((x.toNat &&& y.toNat : Nat) : Int)
  else if op = "|" then some ((x.toNat ||| y.toNat : Nat) : Int)
  else if op = "^" then some ((x.toNat ^^^ y.toNat : Nat) : Int)
  else if op = "<<" then some (x * 2 ^ y.toNat)
  else if op = ">>" then some (x / 2 ^ y.toNat)
  else none

/-- A name in a measure: a parameter reads its Body local, any other name the checked
    constant of that name. -/
def nameU (fn : UFn) (β : Gabbro.Body.Binding) (name : String) : Option Int :=
  match paramPos fn.params name with
  | .ok _ =>
    match β name with
    | .int n => some n
    | _ => none
  | .error _ =>
    match fn.measureConstants.filter (fun p => p.1 == name) with
    | [(_, z)] => some z
    | _ => none

/-- **The value of a measure expression on a Body binding.** -/
def quellWert (fn : UFn) (β : Gabbro.Body.Binding) : UMeasure → Option Int
  | .lit n => some (Int.ofNat n)
  | .variable name => nameU fn β name
  | .bin op a b =>
    match quellWert fn β a, quellWert fn β b with
    | some x, some y => binU op x y
    | _, _ => none
  | .un op a => if op = "-" ∨ op = "-()" then (quellWert fn β a).map (fun x => -x) else none
  | .conv _ a => quellWert fn β a

/-- **The tuple of a `decreases` clause on a Body binding**: empty without a clause. -/
def massTupel (fn : UFn) (β : Gabbro.Body.Binding) : List Nat :=
  match fn.decreases with
  | none => []
  | some m => [((quellWert fn β m).getD 0).toNat]

theorem massTupel_laenge (fn : UFn) (β : Gabbro.Body.Binding) : (massTupel fn β).length ≤ 1 := by
  unfold massTupel
  split <;> simp

variable {u : UProg}

/-- **Every source value is the Body value**: on a binding that reads each parameter at its
    position, the Body evaluation of a measure gives exactly what `SourceValue` denotes. -/
theorem quellWert_of_source {Γ : Ctx} {fn : UFn} {env : Env (declOf u) Γ}
    {β : Gabbro.Body.Binding} (hN : NamenEindeutig fn) (hL : LRel fn 0 env β) :
    ∀ (m : UMeasure) (x : Int), SourceValue fn fn.measureConstants env m.source x →
      quellWert fn β m = some x
  | .lit n, x, h => by
      simp only [UMeasure.source] at h
      cases h
      rfl
  | .variable name, x, h => by
      simp only [UMeasure.source] at h
      cases h with
      | parameter _ j lo hi v found position =>
        have hp := paramPos_of_nodup fn.params j name (.int lo hi) hN found
        have hb := hL name j hp
        rw [Nat.zero_add, nthVal_lowVar Γ j (.int lo hi) v env position, valOf_int] at hb
        simp only [quellWert, nameU, hp, hb]
      | constant _ z unbound found =>
        cases hpp : paramPos fn.params name with
        | ok j =>
          obtain ⟨τ, hτ⟩ := paramPos_name fn.params name j hpp
          have hf := (List.findIdx?_eq_none_iff.mp unbound) _ (List.mem_of_getElem? hτ)
          simp at hf
        | error e => simp only [quellWert, nameU, hpp, found]
  | .bin op a b, x, h => by
      have iha := quellWert_of_source hN hL a
      have ihb := quellWert_of_source hN hL b
      simp only [UMeasure.source] at h
      cases h with
      | add ha hb | sub ha hb | mul ha hb | div ha hb | rem ha hb
      | band ha hb | bor ha hb | bxor ha hb | shl ha hb | shr ha hb =>
        simp [quellWert, binU, iha _ ha, ihb _ hb]
  | .un op a, x, h => by
      have iha := quellWert_of_source hN hL a
      simp only [UMeasure.source] at h
      cases h with
      | neg _ spelling ha =>
        simp only [quellWert]
        rw [if_pos spelling, iha _ ha]
        rfl
  | .conv f a, x, h => by
      have iha := quellWert_of_source hN hL a
      simp only [UMeasure.source] at h
      cases h with
      | conv _ ha =>
        simp only [quellWert]
        exact iha _ ha

/-- **Preservation**: the Body tuple of a function's clause is the exported canonical value
    `Mass.wert`, at every world, on every binding that reads the parameters at their
    positions. -/
theorem massTupel_wert (ex : Export u) (f : (declOf u).Fn) (hN : NamenEindeutig (fnAt u f))
    (σ : World (declOf u)) (env : Env (declOf u) ((declOf u).params f))
    {β : Gabbro.Body.Binding} (hL : LRel (fnAt u f) 0 env β) :
    massTupel (fnAt u f) β = ex.mass.wert f σ env := by
  have hs := ex.source f
  cases hd : (fnAt u f).decreases with
  | none =>
    simp only [SourceTuple, hd] at hs
    simp only [massTupel, hd, Mass.wert, hs, List.map_nil]
  | some m =>
    simp only [SourceTuple, hd] at hs
    obtain ⟨c, hc, hv⟩ := hs
    have hq := quellWert_of_source hN hL m _ (hv σ σ env)
    simp only [massTupel, hd, Mass.wert, hc, List.map_cons, List.map_nil, hq, Option.getD_some]

/-- Preservation at the bridge's entry state of a G entry. -/
theorem massTupel_eintritt (ex : Export u) (c : Fin u.fns.length) (hN : NamenEindeutig (fnAt u c))
    (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params c)) :
    massTupel (fnAt u c) (eintritt u c σ ρ).local' = ex.mass.wert c σ ρ :=
  massTupel_wert ex c hN σ ρ (eintritt_lrel c σ ρ)

/-- On tuples of at most one component, the lexicographic order compares the heads. -/
theorem lexLt_kopf : ∀ {a b : List Nat}, lexLt a b = true → a.length ≤ 1 → b.length ≤ 1 →
    a.headD 0 < b.headD 0
  | [], _, h, _, _ => ((lexLt_laenge h).1 rfl).elim
  | _, [], h, _, _ => ((lexLt_laenge h).2 rfl).elim
  | [x], [y], h, _, _ => by
      have h0 : lexLt [] [] = false := rfl
      simp only [lexLt, h0, Bool.and_false, Bool.or_false, decide_eq_true_eq] at h
      simpa using h
  | _ :: _ :: _, _, _, ha, _ => by simp only [List.length_cons] at ha; omega
  | _, _ :: _ :: _, _, _, hb => by simp only [List.length_cons] at hb; omega

/-- **The canonical measure gate, read on Body entries**: where `massTor` lets a call of `g`
    from an entry of `f` through (the exported value of the call falls below the entry value),
    the Body source value of the callee's entry state lies below the caller's. -/
theorem massTupel_faellt (ex : Export u) {f g : Fin u.fns.length}
    (hNf : NamenEindeutig (fnAt u f)) (hNg : NamenEindeutig (fnAt u g))
    (σ σ' : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params f))
    (ρ' : Env (declOf u) ((declOf u).params g))
    (h : lexLt (ex.mass.wert g σ' ρ') (ex.mass.wert f σ ρ) = true) :
    (massTupel (fnAt u g) (eintritt u g σ' ρ').local').headD 0 <
      (massTupel (fnAt u f) (eintritt u f σ ρ).local').headD 0 := by
  rw [← massTupel_eintritt ex g hNg σ' ρ', ← massTupel_eintritt ex f hNf σ ρ] at h
  exact lexLt_kopf h (massTupel_laenge _ _) (massTupel_laenge _ _)

end Gabbro.Bruecke
