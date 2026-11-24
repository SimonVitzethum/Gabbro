/-
  File:      core/Core/Speicher/Viele.lean
  Subject:   THE MULTI-EVENT APPEND (step M4): a machine step of M4 appends a LIST of graph events, one
             graph-machine step each (`Viele`). It extends the state (`Viele.erweitert`), keeps reachability
             (`Viele.erreichbar`), and composes (`Viele.append`). And a step EXISTS for every access
             (`schritt_existiert`): an access that reads takes the write last in `mo` at its location
             (`mo_letzte_existiert`), program order comes from the context's own events and what precedes
             them; so the memory of the machines never blocks an access whose location has a write.
-/
module

public import Core.Speicher.Anhaengen
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Zustand

variable {F Ort Wert : Type}

/-- **Appending a list of events**, one graph-machine step each, in list order. -/
inductive Viele : Zustand F Ort Wert → List (F × Etikett Ort Wert) → Zustand F Ort Wert → Prop
  | nil (Z : Zustand F Ort Wert) : Viele Z [] Z
  | cons {Z Z₁ Z₂ : Zustand F Ort Wert} {k : F} {l : Etikett Ort Wert}
      {xs : List (F × Etikett Ort Wert)} :
      Schritt Z k l Z₁ → Viele Z₁ xs Z₂ → Viele Z ((k, l) :: xs) Z₂

theorem Viele.erweitert {Z Z' : Zustand F Ort Wert} {xs : List (F × Etikett Ort Wert)}
    (h : Viele Z xs Z') : Erweitert Z Z' := by
  induction h with
  | nil Z => exact Erweitert.refl Z
  | cons s _ ih => exact s.erweitert.trans ih

theorem Viele.erreichbar {Z Z' : Zustand F Ort Wert} {xs : List (F × Etikett Ort Wert)}
    (h : Viele Z xs Z') (hz : Erreichbar Z) : Erreichbar Z' := by
  induction h with
  | nil Z => exact hz
  | cons s _ ih => exact ih (.schritt _ _ hz s)

theorem Viele.append {Z Z' Z'' : Zustand F Ort Wert} {xs ys : List (F × Etikett Ort Wert)}
    (h1 : Viele Z xs Z') (h2 : Viele Z' ys Z'') : Viele Z (xs ++ ys) Z'' := by
  induction h1 with
  | nil Z => exact h2
  | cons s _ ih => exact .cons s (ih h2)

/-- The appended events are the listed ones, in order. -/
theorem Viele.ev {Z Z' : Zustand F Ort Wert} {xs : List (F × Etikett Ort Wert)}
    (h : Viele Z xs Z') : Z'.ev = Z.ev ++ xs.map (fun x => ⟨x.1, x.2⟩) := by
  induction h with
  | nil Z => exact (List.append_nil _).symm
  | cons s _ ih =>
    rw [ih, s.ev, List.map_cons, List.append_assoc]
    rfl

/-- A consistent complete state stays so along appends from a consistent complete state. -/
theorem Viele.gut {Z Z' : Zustand F Ort Wert} {xs : List (F × Etikett Ort Wert)}
    (h : Viele Z xs Z') (hk : Z.graph.Konsistent) (hv : Z.graph.Vollstaendig) :
    Z'.graph.Konsistent ∧ Z'.graph.Vollstaendig := by
  induction h with
  | nil Z => exact ⟨hk, hv⟩
  | cons s _ ih => exact ih s.konsistent s.vollstaendig

/-- The program-order predecessors of a new event of context `k`: every earlier event of `k` and
    every event before one of them. -/
def vorK (Z : Zustand F Ort Wert) (k : F) (i : Nat) : Prop :=
  i < Z.ev.length ∧ ((∃ h : i < Z.ev.length, (Z.ev[i]'h).kontext = k) ∨
    ∃ j, ∃ hj : j < Z.ev.length, (Z.ev[j]'hj).kontext = k ∧ Z.po i j)

/-- **A step exists for every access**: an access of context `k` of kind `a` at `x` with mode `m`
    writing `v` is a step of the graph machine; when it reads, the value it reads is that of a write
    last in `mo` at `x`. -/
theorem schritt_existiert {Z : Zustand F Ort Wert} (hk : Z.graph.Konsistent)
    (hv : Z.graph.Vollstaendig) (k : F) (a : Art) (x : Ort) (m : Modus) (v : Wert)
    (hw : a.liest → ∃ i, ∃ h : i < Z.ev.length,
      (Z.ev[i]'h).lab.art.schreibt ∧ (Z.ev[i]'h).lab.ort = x) :
    ∃ r Z', Schritt Z k ⟨a, x, m, r, v⟩ Z' ∧
      (a.liest → ∃ w, Z.graph.MoLetzte x w ∧ (Z.graph.lab w).geschrieben = r) := by
  have hzu : ∀ i j, i < Z.ev.length → j < Z.ev.length → vorK Z k j → Z.po i j → vorK Z k i := by
    intro i j hi hj hP hpo
    refine ⟨hi, Or.inr ?_⟩
    rcases hP.2 with ⟨_, hjk⟩ | ⟨j', hj', hjk, hpo'⟩
    · exact ⟨j, hj, hjk, hpo⟩
    · exact ⟨j', hj', hjk, hk.wf.po_trans ⟨i, hi⟩ ⟨j, hj⟩ ⟨j', hj'⟩ hpo hpo'⟩
  have hfa : ∀ i (h : i < Z.ev.length), (Z.ev[i]'h).kontext = k → vorK Z k i :=
    fun i h hi => ⟨h, Or.inl ⟨h, hi⟩⟩
  by_cases hl : a.liest
  · obtain ⟨i, hi, his, hio⟩ := hw hl
    obtain ⟨w, hws, hwo, hmax⟩ := Graph.mo_letzte_existiert (G := Z.graph) hk.wf
      ⟨⟨i, hi⟩, his, hio⟩
    let l : Etikett Ort Wert := ⟨a, x, m, (Z.graph.lab w).geschrieben, v⟩
    have A : Anhang Z k l (vorK Z k) w.1 :=
      ⟨hfa, hzu, fun _ => ⟨w.2, hws, hwo, rfl, fun u hu hus huo => by
        rcases hmax ⟨u, hu⟩ hus huo with e | e
        · exact Or.inl (congrArg Fin.val e)
        · exact Or.inr e⟩⟩
    exact ⟨_, _, senke_schritt A hk hv, fun _ => ⟨w, ⟨hws, hwo, hmax⟩, rfl⟩⟩
  · have A : Anhang Z k ⟨a, x, m, v, v⟩ (vorK Z k) 0 :=
      ⟨hfa, hzu, fun h => absurd h hl⟩
    exact ⟨v, _, senke_schritt A hk hv, fun h => absurd h hl⟩

end Zustand

end Gabbro.Core.Speicher
