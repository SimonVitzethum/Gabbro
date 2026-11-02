module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Geteilte Deckung mit Ausnahmen: schreibt ein zweiter Faden denselben Traeger, so ist
    der Traeger geteilt UND beide halten entweder eine gemeinsame Sperre seiner Wache
    ODER eine Ausnahme greift (atomar oder Paarung). Das steht NEBEN `GeteiltGedeckt`,
    nicht an seiner Stelle. -/
def GeteiltGedecktMitAusnahmen (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) : Prop :=
  ∀ (f : Faden), f ∈ J.faeden → ∀ (g : Faden), g ∈ J.faeden → f ≠ g →
    ∀ (c : D.Tab ⊕ D.Glob),
      TraegerSchreibt (J.code f) c = true → TraegerSchreibt (J.code g) c = true →
        Geteilt c = true ∧ (GemeinsameSperre (J.code f) (J.code g) c ∨
          AtomarAusgenommen (D := D) c ∨ PaarungAusgenommen (D := D) c)

/-! ## 14. Zusicherungen mit Umgebung: Q ueber Welt mal Belegung als Gestalt (G7) -/

/-- Eine Zusicherung mit Umgebung: sie spricht ueber die Welt UND die Belegung des
    Sichtbereichs -- kein Faden teilt sie, jeder traegt seine eigene. -/
def EnvZusicherung (Γ : Ctx) : Type := World D → Env D Γ → Prop

/-- Eine Zusicherung mit Umgebung je Faden: jeder Faden traegt seine Belegung ueber
    seinen eigenen Parametern (`D.params` seines Rumpfs). -/
def FadenEnvZusicherung (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) : Type :=
  ∀ (f : Faden), World D → Env D (D.params (J.code f)) → Prop

/-- Der Umgebungserhalt in einem Schritt: die fremde Welt bewegt sich, die eigene
    Belegung bleibt -- die Gestalt, die `hFremd` und `hEigen` je Belegung annimmt. -/
def EnvErhalt (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    (vor nach : World D) (ρ : Env D Γ) : Prop :=
  Q vor ρ ↔ Q nach ρ

/-! ## 15. G4-Einloesung: befreite Traeger brauchen kein Sperrargument -/

/-- **Deckung mit Ausnahmen aus Deckung ohne.** Wer die gemeinsame Sperre je
    doppelt geschriebenem Traeger nachweist, erfuellt erst recht die Deckung mit
    Ausnahmen -- die linke Seite der Disjunktion genuegt. -/
theorem geteiltGedecktMitAusnahmen_aus_gedeckt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (hD : GeteiltGedeckt Nb J) : GeteiltGedecktMitAusnahmen Nb J := by
  intro f hf g hg hne c hfc hgc
  obtain ⟨hT, hS⟩ := hD f hf g hg hne c hfc hgc
  exact ⟨hT, Or.inl hS⟩

/-- **Atomar entlaedt.** Ein `atomic`-Global braucht kein Sperrargument und keine
    Paarung: die mittlere Seite der Disjunktion steht von vornherein, gleichgueltig
    was links (`S`) und rechts (`P`) stuende. -/
theorem atomarAusgenommen_entlaedt (c : D.Tab ⊕ D.Glob)
    (hT : Geteilt c = true) (hA : AtomarAusgenommen (D := D) c)
    (S P : Prop) :
    Geteilt c = true ∧ (S ∨ AtomarAusgenommen (D := D) c ∨ P) :=
  ⟨hT, Or.inr (Or.inl hA)⟩

/-- **Paarung entlaedt.** Nutzlast D.Fn D.passt einer Veroeffentlichung braucht kein
    Sperrargument und keine Atomarseite: die rechte Seite der Disjunktion steht von
    vornherein, gleichgueltig was links (`S`, `A`) stuende. -/
theorem paarungAusgenommen_entlaedt (c : D.Tab ⊕ D.Glob)
    (hT : Geteilt c = true) (hP : PaarungAusgenommen (D := D) c)
    (S A : Prop) :
    Geteilt c = true ∧ (S ∨ A ∨ PaarungAusgenommen (D := D) c) :=
  ⟨hT, Or.inr (Or.inr hP)⟩

/-- **Deckung aus lauter Ausnahmen.** Ist jeder doppelt geschriebene Traeger geteilt
    und ausgenommen (atomar oder Paarung), so gilt die Deckung mit Ausnahmen ganz
    ohne Sperrargument -- die rechte Seite der Disjunktion traegt jeden Fall. -/
theorem geteiltGedecktMitAusnahmen_von_Ausnahmen (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (h : ∀ (f : Faden), f ∈ J.faeden → ∀ (g : Faden), g ∈ J.faeden → f ≠ g →
      ∀ (c : D.Tab ⊕ D.Glob),
        TraegerSchreibt (J.code f) c = true → TraegerSchreibt (J.code g) c = true →
          Geteilt c = true ∧
            (AtomarAusgenommen (D := D) c ∨ PaarungAusgenommen (D := D) c)) :
    GeteiltGedecktMitAusnahmen Nb J := by
  intro f hf g hg hne c hfc hgc
  obtain ⟨hT, hA⟩ := h f hf g hg hne c hfc hgc
  exact ⟨hT, Or.inr hA⟩

/-- **Invariant stability under the exceptions deck.** Where `Q` is the
    invariant itself, the shared side needs no lock argument: every step --
    foreign or own -- is carried by the context (`invErhalt_aus_Kontext`),
    and the chain folds as usual (`kette_erhaelt`, the discharge engine
    behind `allgemeinStabil`). `hDeck` is carried, not consumed: freed
    carriers change nothing for invariant `Q`, since the invariant comes
    from the context rather than from the lock. -/
theorem allgemeinStabil_invariant_mitAusnahmen (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedecktMitAusnahmen Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (I.inv c))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → I.inv c σ := by
  intro σ hletzte f hf
  have hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (I.inv c vor ↔ I.inv c nach) := by
    intro k g vor nach _ hkv hkn
    exact invErhalt_aus_Kontext Nb J I hInv c vor nach
      (List.mem_of_getElem? hkv) (List.mem_of_getElem? hkn)
  have hall := kette_erhaelt J.welten J.schrittFaden J.hKette (I.inv c) (hInit f hf) hStep
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

#print axioms Gabbro.Grammatik.allgemeinStabil_invariant_mitAusnahmen

/-! ## 16. G6-Einloesung: die Kindwelt kommt aus der eingetragenen Stelle -/

/-- **Erzeugung nennt eine Welt.** Steht die eingetragene Stelle noch in der Kette,
    so nennt der Erzeugungseintrag eine Eintrittswelt -- keine eigene Welt, die
    Kettenwelt an eben dieser Stelle. -/
theorem kindEintrittAusSpawn_belegt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (eltern kind : Faden) (k : Nat) (hk : k < J.welten.length) :
    ∃ σ, KindEintrittAusSpawn Nb J (eltern, kind, k) = some σ := by
  unfold KindEintrittAusSpawn
  show ∃ σ, J.welten[k]? = some σ
  exact kette_welt_belegt J.welten k hk

/-- **Vereinigung nennt eine Welt.** Dasselbe an der Rueckkehrstelle: die
    Rueckkehrwelt ist die Kettenwelt an der eingetragenen Stelle. -/
theorem kindEintrittAusJoin_belegt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (eltern kind : Faden) (k : Nat) (hk : k < J.welten.length) :
    ∃ σ, KindEintrittAusJoin Nb J (eltern, kind, k) = some σ := by
  unfold KindEintrittAusJoin
  show ∃ σ, J.welten[k]? = some σ
  exact kette_welt_belegt J.welten k hk

/-- **Was die Erzeugung nennt, liegt in der Kette.** Jede genannte Eintrittswelt ist
    eine Kettenwelt. -/
theorem kindEintrittAusSpawn_mem (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (s : SpawnEintrag) (σ : World D)
    (h : KindEintrittAusSpawn Nb J s = some σ) : σ ∈ J.welten := by
  unfold KindEintrittAusSpawn at h
  exact List.mem_of_getElem? h

/-- **Was die Vereinigung nennt, liegt in der Kette.** Dasselbe an der
    Rueckkehrstelle. -/
theorem kindEintrittAusJoin_mem (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (j : JoinEintrag) (σ : World D)
    (h : KindEintrittAusJoin Nb J j = some σ) : σ ∈ J.welten := by
  unfold KindEintrittAusJoin at h
  exact List.mem_of_getElem? h

/-- **Die Gabel nennt eine Welt, wo der Eintrag eine nennt.** Findet die
    Erzeugungsliste das Kind an gueltiger Stelle, so nennt die Liste seine
    Eintrittswelt. -/
theorem kindEintrittAusGabel_belegt_aus_find (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (spawns : List SpawnEintrag) (kind : Faden) (s : SpawnEintrag)
    (hfind : spawns.find? (fun s => decide (s.2.1 = kind)) = some s)
    (hk : s.2.2 < J.welten.length) :
    ∃ σ, KindEintrittAusGabel Nb J spawns kind = some σ := by
  unfold KindEintrittAusGabel
  rw [hfind]
  exact kette_welt_belegt J.welten s.2.2 hk

/-- **Was die Gabel nennt, liegt in der Kette.** Jede genannte Kindwelt -- ueber
    welchen Eintrag auch immer -- ist eine Kettenwelt. -/
theorem kindEintrittAusGabel_mem (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (spawns : List SpawnEintrag) (kind : Faden) (σ : World D)
    (h : KindEintrittAusGabel Nb J spawns kind = some σ) : σ ∈ J.welten := by
  unfold KindEintrittAusGabel at h
  cases heq : spawns.find? (fun s => decide (s.2.1 = kind)) with
  | none => simp only [heq, reduceCtorEq] at h
  | some s => simp only [heq] at h; exact List.mem_of_getElem? h

/-- **The spawned entry keeps the invariant.** The named entry world is a
    chain world (`kindEintrittAusSpawn_mem`), and the context holds the
    invariant at every chain world -- so the child starts under it. -/
theorem kindEintrittAusSpawn_inv (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (s : SpawnEintrag) (σ : World D)
    (h : KindEintrittAusSpawn Nb J s = some σ) : I.inv c σ :=
  hInv c σ (kindEintrittAusSpawn_mem Nb J s σ h)

/-- **The joined return keeps the invariant.** Same, at the reunion entry. -/
theorem kindEintrittAusJoin_inv (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (j : JoinEintrag) (σ : World D)
    (h : KindEintrittAusJoin Nb J j = some σ) : I.inv c σ :=
  hInv c σ (kindEintrittAusJoin_mem Nb J j σ h)

/-- **The fork-list entry keeps the invariant.** Same, through the whole
    spawn list (`kindEintrittAusGabel_mem`). -/
theorem kindEintrittAusGabel_inv (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (spawns : List SpawnEintrag) (kind : Faden) (σ : World D)
    (h : KindEintrittAusGabel Nb J spawns kind = some σ) : I.inv c σ :=
  hInv c σ (kindEintrittAusGabel_mem Nb J spawns kind σ h)

#print axioms Gabbro.Grammatik.kindEintrittAusSpawn_inv
#print axioms Gabbro.Grammatik.kindEintrittAusJoin_inv
#print axioms Gabbro.Grammatik.kindEintrittAusGabel_inv


end Gabbro.Grammatik
