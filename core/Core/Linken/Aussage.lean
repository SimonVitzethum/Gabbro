module

public import Core.Linken.Modul
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Aggregate.Types.Model
public import Core.Annahme.Annahme
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability
public import Core.Ziel.Korrektheit.Zusammensetzung

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme

/-- A build plan is accepted exactly when linking yields a fragment whose unit is accepted.
    All theorems over accepted units (safety, noninterference) then hold for the linked program. -/
def BauplanAkzeptiert (plan : Bauplan) : Prop :=
  ∃ frag, linke plan = some frag ∧ Akzeptiert (frag.einheit plan.plattform)

/-- Acceptance of a plan is linking followed by unit acceptance. -/
def LinkAkzeptanzAussage : Prop :=
  ∀ plan : Bauplan, BauplanAkzeptiert plan ↔
    ∃ frag, linke plan = some frag ∧ Akzeptiert (frag.einheit plan.plattform)

/-- Linking is acceptance by definition. -/
theorem linkAkzeptanz : LinkAkzeptanzAussage :=
  fun _ => Iff.rfl

/-- The defining module: defines the function `main` with an empty body. -/
def modulDef : Modul :=
  { name := "a"
    fragment := (Fragment.einzel
      (Befehl.definiere mainName [] none 0 2 false [] none)).anhaengen
      (Fragment.einzel Befehl.rueckVoid)
    exporte := ["main"]
    importe := [] }

/-- The calling module: calls the function `main` defined in the other module. -/
def modulCall : Modul :=
  { name := "b"
    fragment := Fragment.einzel (Befehl.rufe mainName [] none)
    exporte := []
    importe := ["main"] }

/-- The two-module build plan: `b` calls the function `main` exported by `a`. -/
def beispielPlan : Bauplan :=
  { module := [modulDef, modulCall]
    abhaengigkeiten := [("b", "a")]
    plattform := .x86_64
    einstieg := "a" }

/-- The linked code defines `main` and then calls it. -/
def beispielFragment : Fragment :=
  verknuepfteFragmente beispielPlan

/-- There is an accepted linked plan with two modules where one calls the other's function. -/
def LinkErfuellbarAussage : Prop :=
  ∃ (plan : Bauplan) (frag : Fragment) (fn : Identifier),
    linke plan = some frag ∧
    plan.module.length = 2 ∧
    (∃ params result globale skip mass calls effects,
      Befehl.definiere fn params result globale skip mass calls effects ∈ frag.code) ∧
    (∃ args bind, Befehl.rufe fn args bind ∈ frag.code) ∧
    Akzeptiert (frag.einheit plan.plattform)

/-- The link check holds for the example plan. -/
theorem beispielOk : bauplanOk beispielPlan = true :=
  rfl

/-- Linking the example plan yields the concatenated fragments. -/
theorem beispielLinke : linke beispielPlan = some beispielFragment :=
  rfl

/-- The example plan has two modules. -/
theorem beispielZwei : beispielPlan.module.length = 2 :=
  rfl

/-- The example code is the three instructions. -/
theorem beispielCode : beispielFragment.code =
    [Befehl.definiere mainName [] none 0 2 false [] none, Befehl.rueckVoid,
      Befehl.rufe mainName [] none] := by
  rfl

/-- The example clauses are empty. -/
theorem beispielKlauseln : beispielFragment.klauseln = .leer := by
  rfl

/-- Every instruction of the example is guard-free. -/
theorem beispielGuard (b : Befehl) (present : b ∈ beispielFragment.code) (frame : Rahmen) :
    b.guard frame = none := by
  simp only [beispielCode, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

/-- Every instruction of the example is frame-only. -/
theorem beispielRein (b : Befehl) (present : b ∈ beispielFragment.code) : b.Privat := by
  simp only [beispielCode, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The example's linked unit is accepted. -/
theorem beispielAkzeptiert : Akzeptiert (beispielFragment.einheit beispielPlan.plattform) := by
  exact Fragment.akzeptiert_ohne_bedarf beispielFragment _ beispielKlauseln beispielRein
    (fun b present frame => beispielGuard b present frame)

/-- Two modules, one call: the satisfiability witness. -/
theorem link_erfuellbar : LinkErfuellbarAussage := by
  refine ⟨beispielPlan, beispielFragment, mainName, beispielLinke, beispielZwei, ?_, ?_,
    beispielAkzeptiert⟩
  · refine ⟨[], none, 0, 2, false, [], none, ?_⟩
    rw [beispielCode]
    exact List.mem_cons_self
  · refine ⟨[], none, ?_⟩
    rw [beispielCode]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Linking succeeds exactly when the declarative check holds, with the concatenated fragments. -/
theorem linke_eq_some {plan : Bauplan} {frag : Fragment} (h : linke plan = some frag) :
    bauplanOk plan = true ∧ frag = verknuepfteFragmente plan := by
  unfold linke at h
  by_cases hb : bauplanOk plan = true
  · rw [if_pos hb] at h
    exact ⟨hb, (Option.some_inj.mp h).symm⟩
  · rw [if_neg hb] at h
    exact nomatch h

/-- An empty list is the only list with `isEmpty`. -/
theorem isEmpty_eq_nil {α : Type} {l : List α} (h : l.isEmpty = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ =>
    have h2 : false = true := h
    exact (Bool.false_ne_true h2).elim

/-- An empty clause check means no written clauses. -/
theorem leer_of_klauselnLeer {frag : Fragment} (h : klauselnLeer frag = true) :
    frag.klauseln = .leer := by
  obtain ⟨code, klauseln, eingang, eintritte, speicher⟩ := frag
  simp only [klauselnLeer] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hxy, hi⟩ := h
  rw [Bool.and_eq_true] at hxy
  obtain ⟨hv, hs⟩ := hxy
  have e1 := isEmpty_eq_nil hv
  have e2 := isEmpty_eq_nil hs
  have e3 := isEmpty_eq_nil hi
  obtain ⟨voraus, sicher, invariant⟩ := klauseln
  subst e1; subst e2; subst e3
  rfl

/-- Concatenation preserves empty clauses. -/
theorem verknuepfte_klauseln_leer_aux (ms : List Modul)
    (h : ∀ m ∈ ms, klauselnLeer m.fragment = true) (acc : Fragment)
    (ha : acc.klauseln = .leer) :
    (ms.foldl (fun a m => a.anhaengen m.fragment) acc).klauseln = .leer := by
  induction ms generalizing acc with
  | nil => simpa using ha
  | cons m rest ih =>
    have hm : klauselnLeer m.fragment = true := h m List.mem_cons_self
    have hrest : ∀ x ∈ rest, klauselnLeer x.fragment = true :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    have step : (acc.anhaengen m.fragment).klauseln = .leer := by
      have e := leer_of_klauselnLeer hm
      show acc.klauseln.anhaengen _ = _
      rw [ha, e]
      rfl
    exact ih hrest _ step

/-- A compatible plan links to a clause-free fragment. -/
theorem verknuepfte_klauseln_leer {plan : Bauplan} (h : annahmenKompatibel plan = true) :
    (verknuepfteFragmente plan).klauseln = .leer := by
  have hall : ∀ m ∈ plan.module, klauselnLeer m.fragment = true := by
    simp only [annahmenKompatibel, List.all_eq_true] at h
    exact h
  unfold verknuepfteFragmente
  exact verknuepfte_klauseln_leer_aux _ hall _ rfl

/-- The linked code is the concatenation of the modules' code. -/
theorem verknuepfte_code_aux (ms : List Modul) (acc : Fragment) :
    (ms.foldl (fun a m => a.anhaengen m.fragment) acc).code =
      acc.code ++ ms.flatMap (fun m => m.fragment.code) := by
  induction ms generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons m rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih]
    show (acc.anhaengen m.fragment).code ++ _ = _
    show acc.code ++ m.fragment.code ++ _ = _
    rw [List.append_assoc]

/-- The linked code is the concatenation of the modules' code. -/
theorem verknuepfte_code (plan : Bauplan) :
    (verknuepfteFragmente plan).code =
      plan.module.flatMap (fun m => m.fragment.code) := by
  unfold verknuepfteFragmente
  have h := verknuepfte_code_aux plan.module Fragment.leer
  have e : Fragment.leer.code = [] := rfl
  rw [e] at h
  simpa using h

/-- The defining module alone is accepted: guard-free with empty clauses. -/
theorem modulDef_klauseln : modulDef.fragment.klauseln = .leer :=
  rfl

/-- The defining module uses no guarded instruction. -/
theorem modulDef_guard (b : Befehl) (present : b ∈ modulDef.fragment.code) (frame : Rahmen) :
    b.guard frame = none := by
  have hc : modulDef.fragment.code =
      [Befehl.definiere mainName [] none 0 2 false [] none, Befehl.rueckVoid] := rfl
  simp only [hc, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> rfl

/-- The defining module alone is accepted. -/
theorem modulDef_akzeptiert : Akzeptiert (modulDef.fragment.einheit .x86_64) := by
  exact Fragment.akzeptiert_ohne_bedarf modulDef.fragment _ modulDef_klauseln
    (fun b present frame => modulDef_guard b present frame)

/-- Two modules with the same name: the link check refuses, although each part
    alone is accepted. The duplicate name is one of the refused incompatibilities. -/
def doppelPlan : Bauplan :=
  { module := [{ name := "a", fragment := modulDef.fragment, exporte := ["main"], importe := [] },
               { name := "a", fragment := modulDef.fragment, exporte := [], importe := ["main"] }]
    abhaengigkeiten := []
    plattform := .x86_64
    einstieg := "a" }

/-- The duplicate name fails the link check. -/
theorem doppelBauplan : bauplanOk doppelPlan = false :=
  rfl

/-- Linking the duplicate-name plan fails. -/
theorem doppelLinke : linke doppelPlan = none := by
  have hneg : ¬ bauplanOk doppelPlan = true := by
    intro ht
    rw [doppelBauplan] at ht
    exact Bool.false_ne_true ht
  unfold linke
  rw [if_neg hneg]

/-- Both parts of the refused plan are accepted. -/
theorem doppelTeile :
    ∀ m ∈ doppelPlan.module, Akzeptiert (m.fragment.einheit doppelPlan.plattform) := by
  intro m hm
  simp only [doppelPlan, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> exact modulDef_akzeptiert

/-- The linker is not trivial: it links a two-module plan, and it refuses a plan
    whose parts are each accepted (a refuse-everything linker would fail the first
    conjunct, an accept-everything linker the second). -/
theorem linker_nichtTrivial : Gabbro.Core.Ziel.Korrektheit.LinkerNichtTrivialAussage := by
  refine ⟨⟨beispielPlan, beispielFragment, beispielLinke, ?_⟩,
    ⟨doppelPlan, doppelLinke, doppelTeile⟩⟩
  rw [beispielZwei]

end Gabbro.Core.Linken
