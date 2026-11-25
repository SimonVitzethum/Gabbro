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
  exact Option.some.inj (by
    simpa only [unit, Etiketten.leer, sichtbar, oeffentlich, decide_true, if_true] using hx x)

/-- The question label is public whenever the object and endpoint labels are. -/
private theorem frage_leer {Ort : Type} (e : Etiketten Ort)
    (ho : ∀ o, e.objekt o = ∅) (hp : ∀ p, e.endpunkt p = ∅) (q : Frage) : e.frage q = ∅ := by
  unfold Etiketten.frage
  rw [hp q.endpoint]
  induction q.zugriffe with
  | nil => rfl
  | cons t ts ih =>
      rw [List.map_cons, List.foldl_cons, ho t.handle.origin.object, Finset.empty_union]
      exact ih

private theorem bind_some {α : Type} (x : Option α) : x.bind some = x := by
  cases x <;> rfl

private theorem etiketten_leer_frage {Ort : Type} (q : Frage) : (Etiketten.leer : Etiketten Ort).frage q = ∅ := by
  exact frage_leer (Etiketten.leer : Etiketten Ort) (fun _ => rfl) (fun _ => rfl) q

/-- A pending answer is public in the low-level unit. -/
private theorem qsg_antwort {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) (c : Kontext) : v.naechsteAntwort c = u.naechsteAntwort c := by
  unfold QuellzustandGleich at h
  have hx := h.2.2.2.2.2 c
  simpa only [unit, Flussdaten.leer, AntwortSicht, sichtbar, oeffentlich,
    decide_true, if_true, etiketten_leer_frage, bind_some] using hx

/-- A failed state stays failed at the next cut. -/
private theorem zustand_nach {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} {t : Nat} (h : ρ.zeit.zustand t = none) : ρ.zeit.zustand (t + 1) = none := by
  have tak := ρ.zeit.takt t
  rw [h] at tak
  cases tak with
  | wartet _ eq _ => exact eq
  | schritt _ step => cases step

end Gabbro.Core.Beobachtung
