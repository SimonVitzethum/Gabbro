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
  dsimp [unit, Flussdaten.leer, LokaleEtiketten.ganz, LokaleEtiketten.gleich, Etiketten.leer,
    oeffentlich] at h
  funext c
  exact h.1 c ⟨0, Nat.zero_lt_one⟩ rfl

/-- The authority and loan ledgers are public in the low-level unit. -/
private theorem qsg_rechte {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.rechte = u.rechte := by
  unfold QuellzustandGleich at h
  exact h.2.2.1

private theorem qsg_leihen {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.leihen = u.leihen := by
  unfold QuellzustandGleich at h
  exact h.2.2.2.1

/-- The initial memory view is public in the low-level unit. -/
private theorem qsg_initial {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.initial = u.initial := by
  unfold QuellzustandGleich at h
  dsimp [unit, Flussdaten.leer, Etiketten.leer, sichtbar, oeffentlich] at h
  funext x
  exact h.2.1.1 x

/-- The status of every context is public in the low-level unit. -/
private theorem qsg_status {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) (c : Kontext) : v.status c = u.status c := by
  unfold QuellzustandGleich at h
  have hs := h.2.1.2.1 c
  dsimp [unit, Flussdaten.leer, Etiketten.leer] at hs
  unfold EndeSicht sichtbar oeffentlich at hs
  cases hv : v.status c <;> cases hu : u.status c <;> simp only [hv, hu] at hs ⊢
  · exact hs
  · cases hs

/-- A pending answer is public in the low-level unit. -/
private theorem qsg_antwort {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) (c : Kontext) : v.naechsteAntwort c = u.naechsteAntwort c := by
  unfold QuellzustandGleich at h
  have hs := h.2.2.2.2 c
  unfold AntwortSicht sichtbar oeffentlich at hs
  dsimp [unit, Flussdaten.leer, Etiketten.leer] at hs
  exact hs

/-- An occupied cut has a predecessor cut with a defined state. -/
private theorem zustand_vor {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} {t : Nat} {b : Zustand L Ort Wert Raum Lok Grund}
    (h : ρ.zeit.zustand (t + 1) = some b) : ∃ a, ρ.zeit.zustand t = some a := by
  have tak := ρ.zeit.takt t
  cases tak with
  | schritt _ _ => rename_i s; exact ⟨s, rfl⟩
  | wartet _ eq _ =>
      refine ⟨b, ?_⟩
      rw [← eq]
      exact h

end Gabbro.Core.Beobachtung
