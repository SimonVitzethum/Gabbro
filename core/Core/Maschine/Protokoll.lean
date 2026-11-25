module

public import Core.Maschine.Schritte
public import Core.Maschine.Speicherwahl

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog
open Speicher (Etikett)

variable {L Ort Wert Raum Lok Grund Bedingung : Type}
variable {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}

private theorem sperr_bestimmt {aktion c z z' z''} (a : SperrSchritt aktion c z z')
    (b : SperrSchritt aktion c z z'') : z' = z'' := by
  cases a with
  | ticket _ _ => cases b; rfl
  | nehmen step =>
    cases step
    cases b with | nehmen next => cases next; rfl
  | geben step =>
    cases step
    cases b with | geben next => cases next; rfl

private theorem rueckkehr_kern {s : Zustand L Ort Wert Raum Lok Grund} {c k k'}
    (a : KehrtZurueck s c k) (b : KehrtZurueck s c k') : k = k' := by
  cases a <;> cases b <;> rfl

theorem FuehrtAus.bestimmt [DecidableEq L] {t c s u aktion lock lock' outside outside' v v'}
    (a : FuehrtAus e t c s u aktion lock outside v)
    (b : FuehrtAus e t c s u aktion lock' outside' v') :
    lock = lock' ∧ outside = outside' ∧ v = v' := by
  cases a with
  | intern => cases b; exact ⟨rfl, rfl, rfl⟩
  | warte _ => cases b; exact ⟨rfl, rfl, rfl⟩
  | frage _ => cases b; exact ⟨rfl, rfl, rfl⟩
  | verbrauche _ => cases b; exact ⟨rfl, rfl, rfl⟩
  | sperre left _ =>
    cases b with
    | sperre right _ =>
      cases sperr_bestimmt left right
      exact ⟨rfl, rfl, rfl⟩
  | rueckkehr left _ =>
    cases b with
    | rueckkehr right _ =>
      cases rueckkehr_kern left right
      exact ⟨rfl, rfl, rfl⟩
  | starte _ => cases b; exact ⟨rfl, rfl, rfl⟩
  | verbinde _ _ => cases b; exact ⟨rfl, rfl, rfl⟩
  | beende _ => cases b; exact ⟨rfl, rfl, rfl⟩
  | wechsle _ _ _ _ => cases b; exact ⟨rfl, rfl, rfl⟩

private theorem spur_gleich {spur spur' : SchrittSpur Ort Wert}
    (memory : spur.speicher = spur'.speicher) (outside : spur.aussen = spur'.aussen) : spur = spur' := by
  cases spur
  cases spur'
  cases memory
  cases outside
  rfl

private theorem append_bestimmt {init : Ort → Wert} {actor : SpeicherAkteur Ort}
    {s v s' s'' : Zustand L Ort Wert Raum Lok Grund} {labels : List (Etikett Ort Wert)}
    {spur spur' : SchrittSpur Ort Wert}
    (a : Speicherfolge init actor s.graph labels spur.speicher s'.graph)
    (b : Speicherfolge init actor s.graph labels spur'.speicher s''.graph)
    (outside : spur.aussen = spur'.aussen)
    (state : s' = { v with graph := s'.graph }) (state' : s'' = { v with graph := s''.graph })
    (wahl : SpeicherWahlGleich s'.graph s''.graph) :
    spur = spur' ∧ s' = s'' := by
  obtain ⟨trace, graph⟩ := a.bestimmt b wahl
  exact ⟨spur_gleich trace outside,
    state.trans ((congrArg (fun g => { v with graph := g }) graph).trans state'.symm)⟩

theorem FuehrtSchrittAus.bestimmt [DecidableEq L] {t c s u plan spur spur' s' s''}
    (a : FuehrtSchrittAus e t c s u plan spur s') (b : FuehrtSchrittAus e t c s u plan spur' s'')
    (wahl : SpeicherWahlGleich s'.graph s''.graph) : spur = spur' ∧ s' = s'' := by
  obtain ⟨_, _, _, _, left, mem, state⟩ := a
  obtain ⟨_, _, _, _, right, mem', state'⟩ := b
  obtain ⟨rfl, outside, rfl⟩ := left.bestimmt right
  rw [← outside] at mem'
  exact append_bestimmt mem mem' outside state state' wahl

theorem AntwortSchritt.bestimmt {k hw t a s spur spur' s' s''}
    (left : AntwortSchritt e k hw t a s spur s') (right : AntwortSchritt e k hw t a s spur' s'')
    (wahl : SpeicherWahlGleich s'.graph s''.graph) : spur = spur' ∧ s' = s'' :=
  append_bestimmt left.2.2.1 right.2.2.1 (left.2.1.trans right.2.1.symm)
    left.2.2.2 right.2.2.2 wahl

private theorem eintritt_bestimmt {z : KernZustand Raum} {k id irq c c' nmi nmi'}
    (left : NimmtUnterbrechung z k id irq c nmi) (right : NimmtUnterbrechung z k id irq c' nmi') :
    c = c' ∧ nmi = nmi' := by
  cases left <;> cases right <;> exact ⟨rfl, rfl⟩

theorem UnterbrechungsSchritt.bestimmt {hw t id s spur spur' s' s''}
    (left : UnterbrechungsSchritt e hw t id s spur s') (right : UnterbrechungsSchritt e hw t id s spur' s'')
    (wahl : SpeicherWahlGleich s'.graph s''.graph) : spur = spur' ∧ s' = s'' := by
  obtain ⟨k, irq, _, _, _, pending, enter, _, trace, append, next⟩ := left
  obtain ⟨k', irq', _, _, _, pending', enter', _, trace', append', next'⟩ := right
  have same := Option.some.inj (pending.2.2.1.symm.trans pending'.2.2.1)
  cases same
  obtain ⟨rfl, rfl⟩ := eintritt_bestimmt enter enter'
  exact append_bestimmt append append' (trace.trans trace'.symm) next next' wahl

end Gabbro.Core.Maschine
