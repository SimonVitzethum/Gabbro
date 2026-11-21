module
public import Bruecke.Kette.Quelle
public import Bruecke.Kette.Suche
@[expose] public section

/-!
# The duties of a unit given as data, function by function

GabbroV's generated files (`Bruecke/Vorlage.lean`) pin the ELABORATED unit `u` as Lean data and
state every duty over it; the front end is never evaluated in the kernel (owner, 2026-11-21). The
one link between the source text and `u` is the equation `uebersetzeAllg src = .ok ⟨u, P, fs⟩`,
a named premise of `nutzer_aus_einheit`, established by running the front end.

So that this scales to units of 500 000 lines, nothing here quantifies over function positions:
the per-function part `FnPflicht u rk f` is proved in a module of its own for each function, and
`pflichtenEinheit_of` assembles them through `∀ f ∈ u.fns`. The unit part (`nullB`,
`stimmigUnitB`, `ohneTransitionenB`) reads only the declarations, never the functions.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-! ## Readings through another callee lookup

A generated duty module computes the Body reading of a function with a logarithmic table
(`Kette/Suche.lean`) instead of the linear standard search; these theorems carry its result back to
the standard instance, about which every statement of the bridge is made. -/

/-- The standard lookup as a function: the first function of the name. -/
def standardSuche (u : UProg) (n : String) : Option UFn := u.fns.find? (fun f => f.name == n)

/-- A lookup function that answers as the standard one gives the standard instance. The instances
    are written explicitly: no instance is resolved from context in these statements. -/
theorem fnSuche_eq {u : UProg} (s : String → Option UFn) (h : ∀ n, s n = standardSuche u n) :
    (FnSuche.mk s : FnSuche u) = instFnSuche u := by
  have hs : s = fun n => u.fns.find? (fun f => f.name == n) := funext h
  subst hs
  rfl

theorem zuBodyZ_suche {u : UProg} (s : String → Option UFn) (h : ∀ n, s n = standardSuche u n)
    (f : UFn) : @zuBodyZ u ⟨s⟩ f = @zuBodyZ u (instFnSuche u) f := by
  rw [fnSuche_eq s h]

theorem meetsU_suche {u : UProg} (s : String → Option UFn) (h : ∀ n, s n = standardSuche u n)
    (wf : Gabbro.Body.State → Prop) (f : UFn) (body : List Gabbro.Body.Stmt) :
    @meetsU u ⟨s⟩ wf f body ↔ @meetsU u (instFnSuche u) wf f body := by
  rw [fnSuche_eq s h]

/-- A printed table built from the keyed list of `u.fns` answers as the standard lookup. -/
theorem tabelle_such {u : UProg} {tiefe : Nat} {t : Tabelle UFn} {ts : List (Nat × String × UFn)}
    (ht : t = Tabelle.bauenK tiefe ts) (hts : ts = tabellenSchluessel u.fns) (n : String) :
    Tabelle.suche tiefe t n = standardSuche u n := by
  subst ht hts
  exact funktionsTabelle_suche tiefe u.fns n

/-! ## The checks, split into a unit part and a function part -/

/-- The part of `stimmigB` that reads no function. -/
def stimmigUnitB (u : UProg) : Bool :=
  u.tabs.all (fun t => t.bools.isEmpty && t.werte.isEmpty) && tabB u && u.invs.isEmpty && staticsB u

/-- The part of `stimmigB` that reads one function (and the unit's declarations). -/
def stimmigFnB (u : UProg) (f : UFn) : Bool :=
  resultTypeB f && f.resSum.isNone && f.resWhy.isNone && f.needs.isEmpty &&
    (artB f && namenB f && freiB f && oldsB u f && postB u f && schreibtB u f)

theorem stimmigB_of {u : UProg} (hu : stimmigUnitB u = true)
    (hf : ∀ f ∈ u.fns, stimmigFnB u f = true) : stimmigB u = true := by
  simp only [stimmigUnitB, Bool.and_eq_true] at hu
  obtain ⟨⟨⟨ht, hb⟩, hi⟩, hs⟩ := hu
  have hf' : ∀ f ∈ u.fns, ((resultTypeB f && f.resSum.isNone && f.resWhy.isNone) = true ∧
      f.needs.isEmpty = true) ∧
      (artB f && namenB f && freiB f && oldsB u f && postB u f && schreibtB u f) = true := by
    intro f hm
    have h := hf f hm
    simp only [stimmigFnB, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩
  simp only [stimmigB, keinBoolB, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨ht, List.all_eq_true.mpr fun f hm => (hf' f hm).1.1⟩, hb⟩,
    List.all_eq_true.mpr fun f hm => (hf' f hm).1.2⟩, hi⟩, hs⟩,
    List.all_eq_true.mpr fun f hm => (hf' f hm).2⟩

/-- No state declares a generated (non-primitive) transition. -/
def ohneTransitionenB (u : UProg) : Bool :=
  u.zustaende.all fun state => state.transitions.all (·.primitive)

theorem ohneTransitionB_of {u : UProg} (h : ohneTransitionenB u = true) :
    ohneTransitionB u = true := by
  unfold ohneTransitionB
  refine List.all_eq_true.mpr fun c _ => ?_
  have hn : transitionOfFn u c = none := by
    unfold transitionOfFn
    refine List.findSome?_eq_none_iff.mpr fun state hs => ?_
    have hp := List.all_eq_true.mp (List.all_eq_true.mp h state hs)
    cases hf : state.transitions.find? (fun tr => !tr.primitive &&
        Parser.strEq (uTransitionFunction state.name tr.name) (fnAt u c).name) with
    | none => rfl
    | some tr =>
      have hm := List.mem_of_find?_eq_some hf
      have ht := List.find?_some hf
      simp only [hp tr hm, Bool.not_true, Bool.false_and, Bool.false_eq_true] at ht
  simp only [hn, Option.isNone_none]

/-- The rank condition of one function. -/
def rangFnB (rk : String → Nat) (f : UFn) : Bool :=
  f.body.all fun st =>
    match st with
    | .call g _ | .bindCall _ g _ => decide (rk g < rk f.name)
    | _ => true

theorem rangB_of {u : UProg} {rk : String → Nat} (h : ∀ f ∈ u.fns, rangFnB rk f = true) :
    rangB u rk = true :=
  List.all_eq_true.mpr fun c _ => h (fnAt u c) (List.get_mem _ _)

/-! ## The duty of one function and of the unit -/

/-- Everything one function owes: its checks and its Body duty. Proved in the function's own
    module of the generated files. -/
def FnPflicht (u : UProg) (rk : String → Nat) (f : UFn) : Prop :=
  stimmigFnB u f = true ∧ bindFrischB f = true ∧ rangFnB rk f = true ∧
    ∃ body, zuBodyZ u f = some body ∧ meetsU u (wfU u) f body

/-- The unit part: read only from the declarations. -/
def EinheitTeil (u : UProg) : Prop :=
  nullB u = true ∧ stimmigUnitB u = true ∧ ohneTransitionenB u = true

/-- The duties of the unit `u`: the unit part and every function's duty under one rank. -/
def PflichtenEinheit (u : UProg) : Prop :=
  EinheitTeil u ∧ ∃ rk : String → Nat, ∀ f ∈ u.fns, FnPflicht u rk f

/-- A list of functions all of which owe their duty; appends keep the assembly shallow. -/
theorem fnPflicht_append {u : UProg} {rk : String → Nat} {xs ys : List UFn}
    (hx : ∀ f ∈ xs, FnPflicht u rk f) (hy : ∀ f ∈ ys, FnPflicht u rk f) :
    ∀ f ∈ xs ++ ys, FnPflicht u rk f := fun f hm =>
  (List.mem_append.mp hm).elim (hx f) (hy f)

theorem fnPflicht_cons {u : UProg} {rk : String → Nat} {g : UFn} {ys : List UFn}
    (hg : FnPflicht u rk g) (hy : ∀ f ∈ ys, FnPflicht u rk f) :
    ∀ f ∈ g :: ys, FnPflicht u rk f := fun f hm =>
  (List.mem_cons.mp hm).elim (fun h => h ▸ hg) (hy f)

theorem fnPflicht_nil {u : UProg} {rk : String → Nat} : ∀ f ∈ ([] : List UFn), FnPflicht u rk f :=
  fun _ hm => absurd hm List.not_mem_nil

/-! ## Premise (b) -/

/-- **Premise (b) from the duties of a unit given as data**, for whichever front end built `u`:
    the only fact about the source is that the generic lowering accepts `u`. Every function of
    `u` is carried. -/
theorem nutzer_aus_senkung {u : UProg} (hp : PflichtenEinheit u)
    {P : Programm (declOf u)} {fs : List (declOf u).Fn} (hlow : lowerAllg u = .ok (P, fs)) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) := by
  obtain ⟨⟨hn, hs, ht⟩, rk, hf⟩ := hp
  have hS := getragenG_of_bools (stimmigB_of hs fun f hm => (hf f hm).1)
    (ohneTransitionB_of ht) (List.all_eq_true.mpr fun f hm => (hf f hm).2.1)
  have hZ : ∀ c : Fin u.fns.length, (fun _ => True) c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body := fun c _ => (hf (fnAt u c) (List.get_mem _ _)).2.2.2
  exact ⟨hn, bruecke_nutzer_M hlow hS _
    (massPflichtU_of_rang (rang_of (rangB_of fun f hm => (hf f hm).2.2.1)) hZ)
    (fun c hc => (hc True.intro).elim) hn (fun _ _ hc => (hc True.intro).elim)⟩

/-- **Premise (b) from the duties of a unit given as data**, the unit built by the Lean
    pipeline from `src`. -/
theorem nutzer_aus_einheit {u : UProg} (hp : PflichtenEinheit u) {src : String}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn) :=
  nutzer_aus_senkung hp (lower_of_uebersetze h)

/-- The same duties supply the atomic-rely form of premise (b). -/
theorem nutzerA_aus_einheit {u : UProg} (hp : PflichtenEinheit u) {src : String}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    ∃ hn : nullB u = true, Zielsatz.NutzerPflichtA (einheitAllg u P hn) := by
  obtain ⟨hn, hb⟩ := nutzer_aus_einheit hp h
  exact ⟨hn, Zielsatz.nutzerPflichtA_ohne_atomar (declOf_scalar_kein_atomar u (nullB_statics hn)) hb⟩

#print axioms nutzer_aus_senkung
#print axioms nutzer_aus_einheit
#print axioms nutzerA_aus_einheit

end Gabbro.Bruecke
