module

public import Core.Beobachtung.Fluss.Quellregel
public import Core.Beobachtung.Review.Spur
public import Core.Beobachtung.Fluss.Beschriftung.Pegel

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Maschine

variable {Wert Ort Grund Form : Type}

def Ausgabe.projizieren (d : Nat → Option (Freigabe Wert)) : Ausgabe Wert → Ausgabe Wert
  | .wert kanal w => .wert kanal w
  | .freigabe id _ w =>
    match d id with
    | some g => .freigabe id g.quelle (g.projektion w)
    | none => .freigabe id ∅ w

def Ausgabe.ereignis (c : Kontext) : Ausgabe Wert → NiedrigesEreignis Ort Wert Grund Form
  | .wert kanal w => .ausgabe c kanal w
  | .freigabe id _ w => .freigabe c id w

def FreigabenDeklariert (d : Nat → Option (Freigabe Wert)) (journal : List (Ausgabe Wert)) : Prop :=
  ∀ id q w, .freigabe id q w ∈ journal → ∃ g, d id = some g

/-- The ideal rule compares release projections, while the implementation trace records
    raw releases. A declared projection with equal results authorises exactly that
    payload difference at the same context and site. -/
def AusgabeJournalAussage : Prop :=
  ∀ {Ort Wert Grund Form : Type} (d : Nat → Option (Freigabe Wert)) (c : Kontext)
    (links rechts : List (Ausgabe Wert)),
    FreigabenDeklariert d links → FreigabenDeklariert d rechts →
    links.map (Ausgabe.projizieren d) = rechts.map (Ausgabe.projizieren d) →
    List.Forall₂ (EreignisAequiv (Ort := Ort) (Grund := Grund) (Form := Form) d)
      (links.map (Ausgabe.ereignis c)) (rechts.map (Ausgabe.ereignis c))

theorem ausgabeJournalAussage_beweis : AusgabeJournalAussage := by
  intro Ort Wert Grund Form d c links
  induction links with
  | nil =>
    intro rechts _ _ gleich
    cases rechts with
    | nil => exact .nil
    | cons r rs => cases gleich
  | cons l ls ih =>
    intro rechts dl dr gleich
    cases rechts with
    | nil => cases gleich
    | cons r rs =>
      simp only [List.map_cons, List.cons.injEq] at gleich ⊢
      refine .cons ?_ (ih rs (fun id q w mem => dl id q w (List.mem_cons_of_mem _ mem))
        (fun id q w mem => dr id q w (List.mem_cons_of_mem _ mem)) gleich.2)
      have kopf := gleich.1
      cases l with
      | wert kanal w =>
        cases r with
        | wert kanal' w' =>
          change Ausgabe.wert kanal w = Ausgabe.wert kanal' w' at kopf
          cases kopf
          exact .gleich _
        | freigabe id q v =>
          obtain ⟨g, hg⟩ := dr id q v List.mem_cons_self
          simp only [Ausgabe.projizieren, hg] at kopf
          cases kopf
      | freigabe id q w =>
        obtain ⟨g, hg⟩ := dl id q w List.mem_cons_self
        cases r with
        | wert kanal v =>
          simp only [Ausgabe.projizieren, hg] at kopf
          cases kopf
        | freigabe id' q' v =>
          obtain ⟨g', hg'⟩ := dr id' q' v List.mem_cons_self
          simp only [Ausgabe.projizieren, hg, hg', Ausgabe.freigabe.injEq] at kopf
          rcases kopf with ⟨rfl, _, hwert⟩
          have same := Option.some.inj (hg.symm.trans hg')
          cases same
          exact .freigabe c id w v g hg hwert

theorem ausgabeJournalAussage_erfuellbar :
    ∃ (d : Nat → Option (Freigabe Int)) (q : Etikett) (links rechts : List (Ausgabe Int)),
      oeffentlich q = false ∧ links ≠ rechts ∧
      FreigabenDeklariert d links ∧ FreigabenDeklariert d rechts ∧
      links.map (Ausgabe.projizieren d) = rechts.map (Ausgabe.projizieren d) := by
  let q := Pegel.geheim.zuEtikett
  let g : Freigabe Int := ⟨q, 0, fun w => w % 2⟩
  let d : Nat → Option (Freigabe Int) := fun _ => some g
  refine ⟨d, q, [.freigabe 0 q 1], [.freigabe 0 q 3], pegel_secret_verborgen, ?_, ?_, ?_, rfl⟩
  · intro eq
    simp only [List.cons.injEq, Ausgabe.freigabe.injEq] at eq
    omega
  · exact fun _ _ _ _ => ⟨g, rfl⟩
  · exact fun _ _ _ _ => ⟨g, rfl⟩

theorem freigabeProjektion_gleich {d : Nat → Option (Freigabe Wert)} {c : Kontext}
    {id : Nat} {links rechts : Wert} {g : Freigabe Wert} (h : d id = some g)
    (vergleich : EreignisAequiv (Ort := Ort) (Grund := Grund) (Form := Form) d
      (.freigabe c id links) (.freigabe c id rechts)) :
    g.projektion links = g.projektion rechts := by
  cases vergleich with
  | gleich => rfl
  | freigabe =>
    rename_i g' hg' proj
    have same := Option.some.inj (h.symm.trans hg')
    cases same
    exact proj

theorem ausgabeBeob_ausgabeSicht
    {L Raum Lok Bedingung Wahl : Type} (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {f : Form} {c : Kontext} {v₁ u₁ v₂ u₂ : Zustand L Ort Wert Raum Lok Grund}
    (a : AusgabeLokal E f c v₁ u₁) (b : AusgabeLokal E f c v₂ u₂)
    (gleich : AusgabeSicht E c v₁ u₁ = AusgabeSicht E c v₂ u₂) :
    List.Forall₂ (EreignisAequiv E.fluss.freigabe)
      (ausgabeBeob E c (v₁.lokal c) (u₁.lokal c)) (ausgabeBeob E c (v₂.lokal c) (u₂.lokal c)) :=
  ausgabeJournalAussage_beweis E.fluss.freigabe c _ _
    (fun id q w mem => (a.2 id q w (List.mem_of_mem_filter mem)).imp fun _ g => g.1)
    (fun id q w mem => (b.2 id q w (List.mem_of_mem_filter mem)).imp fun _ g => g.1) gleich

end Gabbro.Core.Beobachtung
