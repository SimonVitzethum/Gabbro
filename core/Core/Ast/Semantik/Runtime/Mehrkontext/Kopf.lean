/-
  File:      core/Core/Ast/Semantik/Runtime/Mehrkontext/Kopf.lean
  Subject:   THE PROGRAM FORMS RUN IN EVERY CONTEXT (MK-01). `kopf` gives every context that runs the
             instruction at its own position; the head depends on the status and the frame of that context
             alone (`kopf_kontextgleich`). A step of an instruction changes the frame of the acting context
             and nothing else (`Befehl.nach_lokal_anderer`, `Befehl.nach_rest`), so the steps of two
             different contexts commute (`Befehl.nach_kommutiert`): the commutation the linearisation
             argument of `I` needs between the local steps of different contexts.
-/
module

public import Core.Ast.Semantik.Runtime.Regeln

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- **Only a running context has a head.** -/
theorem kopf_laeuft {code : List Befehl} {s : Zustand} {c : Kontext} {b : Befehl}
    (h : kopf code s c = some b) : s.status c = .laeuft := by
  unfold kopf at h
  cases hs : s.status c with
  | laeuft => rfl
  | ruht => rw [hs] at h; cases h
  | beendet e => rw [hs] at h; cases h

/-- A context that has not started has no head. -/
theorem kopf_ruht {code : List Befehl} {s : Zustand} {c : Kontext}
    (h : s.status c = .ruht) : kopf code s c = none := by
  unfold kopf
  rw [h]

/-- A context that has ended has no head. -/
theorem kopf_beendet {code : List Befehl} {s : Zustand} {c : Kontext} {e}
    (h : s.status c = .beendet e) : kopf code s c = none := by
  unfold kopf
  rw [h]

/-- **The head of a running context that has neither returned nor stopped** is the instruction at
    its position. -/
theorem kopf_laufend {code : List Befehl} {s : Zustand} {c : Kontext}
    (laeuft : s.status c = .laeuft) (rueckgabe : (s.lokal c).rueckgabe = none)
    (stopp : (s.lokal c).stopp = none) : kopf code s c = code[(s.lokal c).pc]? := by
  unfold kopf
  rw [laeuft, rueckgabe, stopp]
  try rfl

/-- **The head depends on the status and the frame of its own context alone**, never on the
    identity of the context or on another context. -/
theorem kopf_kontextgleich {code : List Befehl} {s s' : Zustand} {c d : Kontext}
    (status : s.status c = s'.status d) (rahmen : s.lokal c = s'.lokal d) :
    kopf code s c = kopf code s' d := by
  unfold kopf
  rw [status, rahmen]

/-- **Conservativity for the entry context.** If no context but `eintritt` runs, only `eintritt` can
    have a head, exactly the situation of a program that runs in one thread. -/
theorem kopf_nur_eintritt {code : List Befehl} {s : Zustand}
    (ruhig : ∀ d, d ≠ eintritt → s.status d ≠ .laeuft) {c : Kontext} (hc : c ≠ eintritt) :
    kopf code s c = none := by
  cases h : kopf code s c with
  | none => rfl
  | some b => exact absurd (kopf_laeuft h) (ruhig c hc)

/-- **A step of an instruction changes the frame of the acting context and nothing else.** -/
theorem Befehl.nach_lokal_anderer (b : Befehl) {c d : Kontext} (h : d ≠ c) (s : Zustand) :
    (b.nach c s).lokal d = s.lokal d := by
  simp only [Befehl.nach, Function.update_of_ne h]

theorem Befehl.nach_lokal_eigener (b : Befehl) (c : Kontext) (s : Zustand) :
    (b.nach c s).lokal c = b.auswerten (s.lokal c) s.regionLive := by
  simp only [Befehl.nach, Function.update_self]

/-- The machine fields a step leaves alone: status, cores, locks, authority, graph, questions,
    answers and the rest. -/
theorem Befehl.nach_rest (b : Befehl) (c : Kontext) (s : Zustand) :
    (b.nach c s).status = s.status ∧ (b.nach c s).kerne = s.kerne ∧
      (b.nach c s).sperren = s.sperren ∧ (b.nach c s).rechte = s.rechte ∧
      (b.nach c s).leihen = s.leihen ∧ (b.nach c s).graph = s.graph ∧
      (b.nach c s).fragen = s.fragen ∧ (b.nach c s).antworten = s.antworten :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Liveness of a region reads the authority state, which an instruction step does not move. -/
theorem Befehl.nach_regionLive (b : Befehl) (c : Kontext) (s : Zustand) :
    (b.nach c s).regionLive = s.regionLive := rfl

/-- **The local steps of two different contexts commute.** -/
theorem Befehl.nach_kommutiert (b b' : Befehl) {c d : Kontext} (h : c ≠ d) (s : Zustand) :
    b.nach c (b'.nach d s) = b'.nach d (b.nach c s) := by
  have hc : (b'.nach d s).lokal c = s.lokal c := b'.nach_lokal_anderer h s
  have hd : (b.nach c s).lokal d = s.lokal d := b.nach_lokal_anderer h.symm s
  have left : b.nach c (b'.nach d s) =
      { s with lokal := Function.update (Function.update s.lokal d (b'.auswerten (s.lokal d) s.regionLive)) c (b.auswerten (s.lokal c) s.regionLive) } := by
    change { (b'.nach d s) with lokal := Function.update (b'.nach d s).lokal c (b.auswerten ((b'.nach d s).lokal c) (b'.nach d s).regionLive) } = _
    rw [hc, Befehl.nach_regionLive]
    all_goals rfl
  have right : b'.nach d (b.nach c s) =
      { s with lokal := Function.update (Function.update s.lokal c (b.auswerten (s.lokal c) s.regionLive)) d (b'.auswerten (s.lokal d) s.regionLive) } := by
    change { (b.nach c s) with lokal := Function.update (b.nach c s).lokal d (b'.auswerten ((b.nach c s).lokal d) (b.nach c s).regionLive) } = _
    rw [hd, Befehl.nach_regionLive]
    all_goals rfl
  rw [left, right, Function.update_comm h.symm]

end Gabbro.Core.Ast.Semantik
