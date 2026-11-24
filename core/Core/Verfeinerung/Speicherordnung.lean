module

public import Core.Verfeinerung.Folgen
public import Core.Speicher.SCOrdnung

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Katalog
open Gabbro.Core.Speicher (Azyklisch)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl F : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl F}

/-- Graph event numbers are reused only after a crash, in a new epoch. The
    whole-run SC order resolves each epoch's RC11 order constraints once. -/
structure SCOrdnung (ordnung : Nat → Nat → Nat → Prop) : Prop where
  transitiv : ∀ e a b c, ordnung e a b → ordnung e b c → ordnung e a c
  irreflexiv : ∀ e a, ¬ ordnung e a a
  total : ∀ e a b, a ≠ b → ordnung e a b ∨ ordnung e b a

def SCOrdnung.Erfasst (ordnung : Nat → Nat → Nat → Prop)
    (s : Zustand L Ort Wert Raum Lok Grund) : Prop :=
  ∀ a b, s.graph.graph.psc a b → ordnung s.epoche a.val b.val

private theorem aktion_epoche {t c s u action events outside v}
    (h : FuehrtAus E.einrichtung t c s u action events outside v) : v.epoche = u.epoche := by
  cases h <;> rfl

private theorem ausgefuehrte_epoche {t c s u plan spur s'}
    (h : FuehrtSchrittAus E.einrichtung t c s u plan spur s') : s'.epoche = s.epoche := by
  obtain ⟨frame, _, _, _, action, _, state⟩ := h
  have same := congrArg Zustand.epoche state
  exact same.trans ((aktion_epoche action).trans frame.epoche)

private theorem schritt_epoche {hw t s label s'}
    (h : Schritt E.einrichtung E.system E.katalog hw t s label s') :
    (s'.epoche = s.epoche ∧ s.graph.Erweitert s'.graph) ∨ s'.epoche = t + 1 := by
  cases h with
  | kontext _ _ _ execute => exact Or.inl ⟨ausgefuehrte_epoche execute, (execute.viele _).erweitert⟩
  | antwort _ arrives =>
    have same := congrArg Zustand.epoche arrives.2.2.2
    exact Or.inl ⟨same, (arrives.viele _).erweitert⟩
  | interrupt _ enters =>
    refine Or.inl ⟨?_, (enters.viele _).erweitert⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, state⟩ := enters
    have same := congrArg Zustand.epoche state
    exact same
  | absturz crash => exact Or.inr crash.neustart.2.2.2.2.2.2.1

private theorem takt_epoche (η : Lauf E) (t : Nat) :
    ((η.zeit.zustand (t + 1)).epoche = (η.zeit.zustand t).epoche ∧
      (η.zeit.zustand t).graph.Erweitert (η.zeit.zustand (t + 1)).graph) ∨
    (η.zeit.zustand (t + 1)).epoche = t + 1 := by
  cases η.zeit.takt t with
  | schritt _ step => exact schritt_epoche step
  | wartet _ same _ =>
    rw [same]
    exact Or.inl ⟨rfl, Speicher.Zustand.Erweitert.refl _⟩

private theorem epoche_bound {η : Lauf E} (valid : Laeufe E η) (t : Nat) :
    (η.zeit.zustand t).epoche ≤ t := by
  induction t with
  | zero =>
    rw [valid.2.2.2.1]
    exact Nat.le_refl _
  | succ t ih =>
    rcases takt_epoche η t with ⟨same, _⟩ | fresh
    · rw [same]
      exact Nat.le_succ_of_le ih
    · rw [fresh]

private theorem graph_in_epoche {η : Lauf E} (valid : Laeufe E η) {a b : Nat} (le : a ≤ b)
    (same : (η.zeit.zustand a).epoche = (η.zeit.zustand b).epoche) :
    (η.zeit.zustand a).graph.Erweitert (η.zeit.zustand b).graph := by
  induction b, le using Nat.le_induction with
  | base => exact Speicher.Zustand.Erweitert.refl _
  | succ b le ih =>
    rcases takt_epoche η b with ⟨unchanged, grows⟩ | fresh
    · exact (ih (same.trans unchanged)).trans grows
    · have impossible := (epoche_bound valid a).trans le
      rw [same, fresh] at impossible
      exact (Nat.not_succ_le_self _ impossible).elim

private def NummernKante (g : SpeicherGraph Ort Wert) (a b : Nat) : Prop :=
  ∃ (ha : a < g.ev.length) (hb : b < g.ev.length), g.graph.psc ⟨a, ha⟩ ⟨b, hb⟩

private theorem nummernKante_monoton {g g' : SpeicherGraph Ort Wert} (grows : g.Erweitert g') {a b : Nat}
    (edge : NummernKante g a b) : NummernKante g' a b := by
  obtain ⟨ha, hb, psc⟩ := edge
  exact ⟨ha.trans_le grows.laenge_le, hb.trans_le grows.laenge_le, grows.einbettung.psc psc⟩

private theorem nummernPfad {g : SpeicherGraph Ort Wert} {a b : Nat}
    (path : Relation.TransGen (NummernKante g) a b) :
    ∃ (ha : a < g.ev.length) (hb : b < g.ev.length), Relation.TransGen g.graph.psc ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction path with
  | single edge =>
    obtain ⟨ha, hb, psc⟩ := edge
    exact ⟨ha, hb, .single psc⟩
  | tail _ edge ih =>
    obtain ⟨ha, _, pf⟩ := ih
    obtain ⟨_, hb, psc⟩ := edge
    exact ⟨ha, hb, pf.tail psc⟩

private def EpochenKante (η : Lauf E) (epoch a b : Nat) : Prop :=
  ∃ t, (η.zeit.zustand t).epoche = epoch ∧ NummernKante (η.zeit.zustand t).graph a b

private theorem epochenPfad {η : Lauf E} (valid : Laeufe E η) {epoch a b : Nat}
    (path : Relation.TransGen (EpochenKante η epoch) a b) :
    ∃ t, (η.zeit.zustand t).epoche = epoch ∧ Relation.TransGen (NummernKante (η.zeit.zustand t).graph) a b := by
  induction path with
  | single edge =>
    obtain ⟨t, epochEq, seen⟩ := edge
    exact ⟨t, epochEq, .single seen⟩
  | tail _ edge ih =>
    obtain ⟨i, epochI, earlierPath⟩ := ih
    obtain ⟨j, epochJ, last⟩ := edge
    rcases Nat.le_total i j with earlier | later
    · have grows := graph_in_epoche valid earlier (epochI.trans epochJ.symm)
      have mapped : Relation.TransGen (NummernKante (η.zeit.zustand j).graph) _ _ :=
        Relation.TransGen.mono (r := NummernKante (η.zeit.zustand i).graph)
          (fun _ _ h => nummernKante_monoton grows h) _ _ earlierPath
      exact ⟨j, epochJ, mapped.tail last⟩
    · have grows := graph_in_epoche valid later (epochJ.trans epochI.symm)
      exact ⟨i, epochI, earlierPath.tail (nummernKante_monoton grows last)⟩

private theorem epochenKonsistent {η : Lauf E} (valid : Laeufe E η) (epoch : Nat) :
    Azyklisch (EpochenKante η epoch) := by
  intro a cycle
  obtain ⟨t, _, seen⟩ := epochenPfad valid cycle
  obtain ⟨ha, _, cyclic⟩ := nummernPfad seen
  exact (speicher_gut_im_lauf valid t).1.psc ⟨a, ha⟩ cyclic

/-- A finite cycle in the union for one epoch would already occur in one
    concrete prefix of that epoch. A single linear extension therefore covers
    all cuts of a finite or infinite run. -/
theorem sc_ordnung_im_lauf {η : Lauf E} (valid : Laeufe E η) :
    ∃ ordnung, SCOrdnung ordnung ∧ ∀ t, SCOrdnung.Erfasst ordnung (η.zeit.zustand t) := by
  have erweiterung (e : Nat) := Speicher.lineare_erweiterung (epochenKonsistent valid e)
  let ordnung := fun e => Classical.choose (erweiterung e)
  have ord (e : Nat) := Classical.choose_spec (erweiterung e)
  exact ⟨ordnung, ⟨fun e => (ord e).1, fun e => (ord e).2.1, fun e => (ord e).2.2.1⟩,
    fun t a b edge => (ord _).2.2.2 a.val b.val ⟨t, rfl, a.isLt, b.isLt, edge⟩⟩

end Gabbro.Core.Maschine.I
