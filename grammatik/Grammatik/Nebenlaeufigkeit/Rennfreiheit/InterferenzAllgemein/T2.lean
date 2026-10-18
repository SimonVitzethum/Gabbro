/- Part 2 of 5 of `InterferenzAllgemein` (split by instrumente/teile/lean-teilen.py; the umbrella `InterferenzAllgemein.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T1

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

/-- **Paarung entlaedt.** Nutzlast einer Veroeffentlichung braucht kein
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
  | none => simp [heq] at h
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

/-! ## 17. G7-Einloesung: die eigene Belegung bleibt je Schritt fest -/

/-- **Gleichheit je Schritt, reflexiv.** Wo die Welt steht, steht sie -- die eigene
    Belegung stellt keine Frage. -/
theorem envErhalt_refl (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    (σ : World D) (ρ : Env D Γ) : EnvErhalt Γ Q σ σ ρ := by
  rfl

/-- **Gleichheit je Schritt, symmetrisch.** -/
theorem envErhalt_symm (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    {vor nach : World D} {ρ : Env D Γ}
    (h : EnvErhalt Γ Q vor nach ρ) : EnvErhalt Γ Q nach vor ρ :=
  Iff.symm h

/-- **Gleichheit je Schritt, transitiv.** -/
theorem envErhalt_trans (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    {a b c : World D} {ρ : Env D Γ}
    (h1 : EnvErhalt Γ Q a b ρ) (h2 : EnvErhalt Γ Q b c ρ) :
    EnvErhalt Γ Q a c ρ :=
  Iff.trans h1 h2

/-- **Die Kette mit Umgebung.** Was am Kopf fuer die eigene Belegung gilt und jeden
    Schritt bei fester Belegung ueberlebt, gilt an jeder Stelle -- `kette_erhaelt`
    mit der Belegung als stummer Zeugin. -/
theorem kette_erhaelt_env (welten : List (World D)) (schrittFaden : List Faden)
    (hKette : welten.length = schrittFaden.length + 1)
    (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ) (ρ : Env D Γ)
    (hInit : ∀ σ₀ : World D, welten[0]? = some σ₀ → Q σ₀ ρ)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      schrittFaden[k]? = some g → welten[k]? = some vor →
        welten[k + 1]? = some nach → EnvErhalt Γ Q vor nach ρ) :
    ∀ (k : Nat) (σ : World D), welten[k]? = some σ → Q σ ρ := by
  exact kette_erhaelt welten schrittFaden hKette (fun σ => Q σ ρ) hInit hStep

/-- **Hebung aus der Welt.** Wo die Zusicherung mit Umgebung nur die Welt liest,
    traegt der Welterhalt den Umgebungserhalt -- die Gestalt, die `hFremd` und
    `hEigen` je Belegung annehmen, ohne je die Belegung anzufassen. -/
theorem envErhalt_aus_weltErhalt (Γ : Ctx) (P : World D → Prop)
    (Q : EnvZusicherung (D := D) Γ)
    (hQ : ∀ (σ : World D) (ρ : Env D Γ), Q σ ρ ↔ P σ)
    {vor nach : World D} (hP : P vor ↔ P nach) (ρ : Env D Γ) :
    EnvErhalt Γ Q vor nach ρ := by
  unfold EnvErhalt
  rw [hQ vor ρ, hQ nach ρ]
  exact hP

/-- **Die Fadenskette mit Umgebung.** Je Faden und eigener Belegung ueber seinen
    Parametern: Kopf plus schrittweiser Erhalt bei fester Belegung falten zur
    Kette -- die Form, die `allgemeinStabil` je Belegung annimmt. -/
theorem fadenEnv_kette_erhaelt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Q : FadenEnvZusicherung Nb J) (f : Faden) (ρ : Env D (D.params (J.code f)))
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q f σ₀ ρ)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ)) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Q f σ ρ :=
  kette_erhaelt J.welten J.schrittFaden J.hKette (fun σ => Q f σ ρ) hInit hStep

/-- **Die letzte Welt mit Umgebung.** Kopf plus schrittweiser Erhalt bei fester
    Belegung gelten an der letzten Welt der Kette -- der Schluss von
    `allgemeinStabil`, je Belegung. -/
theorem fadenEnv_letzte_erhaelt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Q : FadenEnvZusicherung Nb J) (f : Faden) (ρ : Env D (D.params (J.code f)))
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q f σ₀ ρ)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ))
    (σ : World D) (hletzte : J.welten.getLast? = some σ) : Q f σ ρ := by
  have hall := fadenEnv_kette_erhaelt Nb J Q f ρ hInit hStep
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

/-- **General stability with environments (N threads).** The main theorem
    lifted to per-thread scopes: where every thread's world-and-scope claim
    depends only on its own frame (per scope value), holds at the chain head,
    and survives foreign steps in disjointness or by preservation and own
    steps by preservation, it holds at the last world under every scope.
    The foreign disjoint side closes via `stabil` over the checked step
    frames (`hSchritt`); the chain folds at fixed scope
    (`fadenEnv_letzte_erhaelt`). Scopes stay per-thread throughout -- no
    thread ever reads another's. -/
theorem allgemeinStabil_env (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : FadenEnvZusicherung Nb J)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f))),
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (fun σ => Q f σ ρ))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f)))
      (σ₀ : World D), J.welten[0]? = some σ₀ → Q f σ₀ ρ)
    (hFremd : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f)))
      (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨ (Q f vor ρ ↔ Q f nach ρ))
    (hEigen : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f)))
      (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ)) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden →
      ∀ (ρ : Env D (D.params (J.code f))), Q f σ ρ := by
  intro σ hletzte f hf ρ
  have hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ) := by
    intro k g vor nach hkg hkv hkn
    by_cases heq : g = f
    · subst heq
      exact hEigen g hf ρ k vor nach hkg hkv hkn
    · obtain ⟨hgm, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
      cases hFremd f hf ρ k g vor nach hgm heq hkg hkv hkn with
      | inl hd => exact stabil (hAb f hf ρ) hR hd
      | inr hiff => exact hiff
  exact fadenEnv_letzte_erhaelt Nb J Q f ρ (hInit f hf ρ) hStep σ hletzte

#print axioms Gabbro.Grammatik.allgemeinStabil_env

#print axioms Gabbro.Grammatik.geteiltGedecktMitAusnahmen_aus_gedeckt
#print axioms Gabbro.Grammatik.atomarAusgenommen_entlaedt
#print axioms Gabbro.Grammatik.paarungAusgenommen_entlaedt
#print axioms Gabbro.Grammatik.geteiltGedecktMitAusnahmen_von_Ausnahmen
#print axioms Gabbro.Grammatik.kindEintrittAusSpawn_belegt
#print axioms Gabbro.Grammatik.kindEintrittAusJoin_belegt
#print axioms Gabbro.Grammatik.kindEintrittAusSpawn_mem
#print axioms Gabbro.Grammatik.kindEintrittAusJoin_mem
#print axioms Gabbro.Grammatik.kindEintrittAusGabel_belegt_aus_find
#print axioms Gabbro.Grammatik.kindEintrittAusGabel_mem
#print axioms Gabbro.Grammatik.envErhalt_refl
#print axioms Gabbro.Grammatik.envErhalt_symm
#print axioms Gabbro.Grammatik.envErhalt_trans
#print axioms Gabbro.Grammatik.kette_erhaelt_env
#print axioms Gabbro.Grammatik.envErhalt_aus_weltErhalt
#print axioms Gabbro.Grammatik.fadenEnv_kette_erhaelt
#print axioms Gabbro.Grammatik.fadenEnv_letzte_erhaelt

/-! ## 18. Owicki-Gries step: sequential triples plus interference freedom (P15) -/

/-- Sequential triple for one thread `f`: valid at the chain head and preserved
    by its own steps. This is the sequential-logic side of the Owicki-Gries
    method: each thread is proved in isolation, carrying exactly the `hInit`
    and `hEigen` premises that `allgemeinStabil` consumes. -/
def SeqTriple (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop) (f : Faden) : Prop :=
  (∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q f σ₀) ∧
    ∀ (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → (Q f vor ↔ Q f nach)

/-- Interference freedom for `Q`: every assertion of `f` survives every step
    of every distinct thread `g`. This is the Owicki-Gries check: one
    preservation obligation per foreign step, discharged independently of the
    sequential proofs. It feeds the shared (preserved) side of the `hFremd`
    disjunction of `allgemeinStabil`. -/
def InterferenceFree (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop) : Prop :=
  ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
    g ∈ J.faeden → g ≠ f →
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → (Q f vor ↔ Q f nach)

/-- Interference freedom discharges the foreign premise of `allgemeinStabil`
    through the shared (preserved) side of the disjunction. -/
theorem interferenceFree_gives_hFremd (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (hFree : InterferenceFree Nb J Q)
    (f : Faden) (hf : f ∈ J.faeden)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hgm : g ∈ J.faeden) (hne : g ≠ f)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
      (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨
      (Q f vor ↔ Q f nach) :=
  Or.inr (hFree f hf k g vor nach hgm hne hkg hkv hkn)

/-- Owicki-Gries stability (N threads): sequential triples plus interference
    freedom give stable assertions at the last world, via the proved N-thread
    theorem `allgemeinStabil`. The sequential proofs supply `hInit`/`hEigen`;
    the interference check supplies `hFremd` through its preserved side. -/
theorem owickiGries_stabil (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (Q f))
    (hSeq : ∀ (f : Faden), f ∈ J.faeden → SeqTriple Nb J Q f)
    (hFree : InterferenceFree Nb J Q) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ := by
  refine allgemeinStabil Nb J I Q hInv hDeck hAb
    (fun f hf σ₀ h₀ => (hSeq f hf).1 σ₀ h₀) ?_ ?_
  · intro f hf k g vor nach hgm hne hkg hkv hkn
    exact Or.inr (hFree f hf k g vor nach hgm hne hkg hkv hkn)
  · intro f hf k vor nach hkg hkv hkn
    exact (hSeq f hf).2 k vor nach hkg hkv hkn

#print axioms Gabbro.Grammatik.interferenceFree_gives_hFremd
#print axioms Gabbro.Grammatik.owickiGries_stabil

end Gabbro.Grammatik

/-! ## 19. Sequential contracts as triples: the Owicki-Gries bind (P15 to shape)

    `owickiGries_stabil` (§18) consumes abstract assertions `Q` with sequential
    validity (`SeqTriple`) plus interference freedom (`InterferenceFree`). This
    section binds that shape to CONTRACT-shaped obligations, without importing
    them: `QRequires`/`QEnsures` live downstream in `Extraktion.lean`, which
    already imports THIS file -- importing them here would be circular (and
    `Interferenz.lean` (S1) books exactly this cut: contracts as abstract `Q`,
    substitution downstream). So the triple below is stated over explicit
    `Pre`/`Post` predicates (`D.Fn → World D → Prop`), and the remainder names
    precisely where each premise is discharged.

    Covered fragment (named): the HEAD-VALID CONTRACT CONJUNCTION -- for one
    thread `f` running `J.code f`, the assertion
    `SpecQ Pre Post f σ := Pre (J.code f) σ ∧ Post (J.code f) σ`, valid at the
    chain head (`requiresHead`/`ensuresHead`), preserved by its own steps
    (`requiresEigen`/`ensuresEigen`, the sequential-logic side), and preserved
    by every foreign step (`InterferenceFree`, the Owicki-Gries check).
    `seqTriple_from_spec` folds the triple into `SeqTriple`;
    `stabil_from_spec` closes it to the last world via `owickiGries_stabil`.

    Honest remainder:
    (R1) The instantiation `Pre := QRequires P`, `Post := QEnsures P`
    (`Extraktion.lean`) happens downstream, where the import direction allows
    it -- not here.
    (R2) `hAb` (frame-locality of the conjunction) stays a premise; downstream
    it is `haengtAb_vertrag_gesamt` once both footprints lie in the signature
    frame (the checker's footprint duty).
    (R3) `hFree` (interference freedom) stays a premise; it IS the
    Owicki-Gries check, discharged per program by the verifier (own logic).
    (R4) `requiresEigen`/`ensuresEigen` are carried, not derived from `exec`
    (G7 carries over: own-step preservation is assumed, not executed).
    (R5) `Ziel.lean`'s `hSeqLogic` premise (`ziel_nutzer_last`) still needs
    rewriting to consume `stabil_from_spec` -- owned by the proof architect
    (`Ziel.lean` is not touched here).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The contract conjunction for one thread: `Pre` (requires-side) and `Post`
    (ensures-side) over the function that thread runs. This is the covered
    fragment -- the head-valid contract conjunction -- as an assertion. -/
def SpecQ (Pre Post : D.Fn → World D → Prop)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) :
    Faden → World D → Prop :=
  fun f σ => Pre (J.code f) σ ∧ Post (J.code f) σ

/-- A sequential contract triple for one thread `f`: both sides valid at the
    chain head and both preserved by its own steps. The MINIMAL spec-triple
    predicate: exactly the `SeqTriple` obligations under contract names, so
    that `seqTriple_from_spec` is a folding, not a claim. -/
structure SpecTriple (Pre Post : D.Fn → World D → Prop)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (f : Faden) : Prop where
  /-- The requires-side holds at the chain head (caller obligation at entry). -/
  requiresHead : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Pre (J.code f) σ₀
  /-- The ensures-side holds at the chain head (sequential proof concludes). -/
  ensuresHead : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Post (J.code f) σ₀
  /-- Own steps preserve the requires-side. -/
  requiresEigen : ∀ (k : Nat) (vor nach : World D),
    J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
      J.welten[k + 1]? = some nach → (Pre (J.code f) vor ↔ Pre (J.code f) nach)
  /-- Own steps preserve the ensures-side. -/
  ensuresEigen : ∀ (k : Nat) (vor nach : World D),
    J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
      J.welten[k + 1]? = some nach → (Post (J.code f) vor ↔ Post (J.code f) nach)

/-- The triple folds into `SeqTriple` over the conjunction: head validity
    pairs up, own-step preservation meets under `and_congr`. -/
theorem seqTriple_from_spec (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Pre Post : D.Fn → World D → Prop) (f : Faden)
    (h : SpecTriple Pre Post Nb J f) :
    SeqTriple Nb J (SpecQ Pre Post Nb J) f := by
  refine ⟨?_, ?_⟩
  · intro σ₀ h₀
    show Pre (J.code f) σ₀ ∧ Post (J.code f) σ₀
    exact ⟨h.requiresHead σ₀ h₀, h.ensuresHead σ₀ h₀⟩
  · intro k vor nach hkg hkv hkn
    show (Pre (J.code f) vor ∧ Post (J.code f) vor) ↔
      (Pre (J.code f) nach ∧ Post (J.code f) nach)
    exact and_congr (h.requiresEigen k vor nach hkg hkv hkn)
      (h.ensuresEigen k vor nach hkg hkv hkn)


end Gabbro.Grammatik
