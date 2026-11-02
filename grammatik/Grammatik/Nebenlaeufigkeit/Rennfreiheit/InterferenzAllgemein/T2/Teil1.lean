module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T2.Teil1Basis

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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
