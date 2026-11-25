module

public import Core.Ast.LowLevel.Execution
public import Core.Ast.LowLevel.Proofs.Preservation
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Region
public import Core.Beobachtung.Review.Spur
public import Core.Beobachtung.Nichtinterferenz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.LowLevel (Instruction unit)

/-- For the low-level unit every source place is public, so source-state equality is equality
    of the local stores. -/
private theorem qsg_lokal {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.lokal = u.lokal := by
  unfold QuellzustandGleich LokaleGleich at h
  dsimp [unit, Flussdaten.leer, LokaleEtiketten.ganz, LokaleEtiketten.gleich, Etiketten.leer] at h
  funext c
  exact h.1 c ⟨0, Nat.zero_lt_one⟩ (by decide)

/-- The authority and loan ledgers are public in the low-level unit. -/
private theorem qsg_rechte {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.rechte = u.rechte := by
  unfold QuellzustandGleich at h
  exact h.2.2.2.1

private theorem qsg_leihen {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.leihen = u.leihen := by
  unfold QuellzustandGleich at h
  exact h.2.2.2.2.1

/-- The initial memory view is public in the low-level unit. -/
private theorem qsg_initial {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.initial = u.initial := by
  unfold QuellzustandGleich at h
  have hx := h.2.2.1
  funext x
  simpa only [unit, Etiketten.leer, sichtbar, oeffentlich, decide_true] using hx x

/-- The question label of the empty label assignment is public. -/
private theorem leer_frage {Ort : Type} (q : Frage) : (Etiketten.leer : Etiketten Ort).frage q = ∅ := by
  simp only [Etiketten.frage, Etiketten.leer, List.map, Finset.foldl, Finset.empty_union]

/-- A pending answer is public in the low-level unit. -/
private theorem qsg_antwort {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) (c : Kontext) : v.naechsteAntwort c = u.naechsteAntwort c := by
  unfold QuellzustandGleich at h
  have hx := h.2.2.2.2.2 c
  simpa only [unit, Flussdaten.leer, Etiketten.leer, AntwortSicht, leer_frage,
    sichtbar, oeffentlich, decide_true] using hx

/-- An occupied cut has a predecessor cut with a defined state. -/
private theorem zustand_vor {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} {t : Nat} {b : Zustand L Ort Wert Raum Lok Grund}
    (h : ρ.zeit.zustand (t + 1) = some b) : ∃ a, ρ.zeit.zustand t = some a := by
  have tak := ρ.zeit.takt t
  cases tak with
  | schritt _ step =>
      cases step with
      | schritt _ => exact ⟨_, rfl⟩
  | wartet _ eq _ =>
      refine ⟨b, ?_⟩
      rw [← eq]
      exact h

end Gabbro.Core.Beobachtung
