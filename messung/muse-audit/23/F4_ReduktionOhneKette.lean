/-
  Audit probe F4: `SerialLink` + `reduktion_seriell` give an HB order over
  run indices that no chain conclusion consumes; `mover_nonwriter_past`
  ignores the non-writer's position (pattern a/b).

  Demonstrations:
  (a) `serial_chain_from_run` concludes `... ∧ ∃ j₁ j₂, HB run j₁ j₂ ∨ HB run j₂ j₁`.
      The second conjunct is proved from `hLink` + `reduktion_seriell` alone;
      the first conjunct (chain observations) is proved from the §21 package
      alone. Neither uses the other: the HB order is a sidecar.
  (b) `mover_nonwriter_past`: the non-writing step `g` at `k` commutes "past"
      the writer `g'` without any premise linking `g`'s frame, `g =/≠ g'`,
      or the middle world to a swapped order. The proof applies `hRet` to the
      `nichtschreiber` transport; `hW'`, `hgm'`, and the whole `g`-step
      indexing (`hkg`, `hkv`) serve only to feed those two lemmas. In
      particular the conclusion `I.inv c nach` follows from `hVor` via ANY
      non-writing step and ANY restoring writer -- no commutation is shown.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- (a1): the HB sidecar from link + order lemmas alone. This is exactly the
    second conjunct of `serial_chain_from_run`, with the chain-observation
    hypotheses (`hAb`, `hFrameT`, `hFrameG`, `hGuardT`, `hEntry`, `hReturn`,
    `hCov`, `hForm`) erased. -/
theorem audit_hb_sidecar_ohne_kette
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (t₀ : D.Tab)
    (run : Lauf D) (hG : Gesittet run)
    (hLink : SerialLink Nb J run t₀)
    (k₁ k₂ : Nat) (g₁ g₂ : Faden)
    (hK : SectionConflict Nb J t₀ k₁ k₂ g₁ g₂) :
    ∃ (j₁ j₂ : Nat), HB run j₁ j₂ ∨ HB run j₂ j₁ := by
  obtain ⟨_, _, _, hne, hkg₁, hkg₂, hW₁, hW₂⟩ := hK
  obtain ⟨j₁, w₁, Λ₁, hh₁, hw₁⟩ := hLink k₁ g₁ hkg₁ hW₁
  obtain ⟨j₂, w₂, Λ₂, hh₂, hw₂⟩ := hLink k₂ g₂ hkg₂ hW₂
  exact ⟨j₁, j₂,
    reduktion_seriell run hG t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ hh₁ hh₂ hw₁ hw₂⟩

/-- (a2): the observation conjunct without run, link, conflict, or HB.
    Same proof as in `serial_chain_from_run`, minus the run side. -/
theorem audit_kette_ohne_run
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hForm : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ : World D),
      Q f σ ↔ I.inv (.inl t₀) σ) :
    ∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → Q f σ := by
  intro σ hletzte f hf
  rw [hForm f hf σ]
  have hChain := hinv_kette_aus_disziplin Nb J I (.inl t₀) L Wc Gc hAb hFrameT hFrameG
    hGuardT hEntry hReturn
    (fun k g vor nach hgm hkg hkv hkn hW =>
      wache_aus_schuld Nb J t₀ L hGuardT g hgm hW (hCov g hgm hW))
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hChain _ σ hlast

/-- (b): `mover_nonwriter_past` restated to expose that the non-writer `g`
    contributes only a frame-preservation transport and the writer only a
    restore step: no swapped order, no `g ≠ g'`, no writer frame premise. -/
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv c))
    (hFrameT : ∀ t : D.Tab, Wc t = true → c = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → c = .inr x)
    (k : Nat) (g g' : Faden) (vor mid nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkm : J.welten[k + 1]? = some mid)
    (hkg' : J.schrittFaden[k + 1]? = some g') (hkn : J.welten[k + 1 + 1]? = some nach)
    (hN : TraegerSchreibt (J.code g) c = false)
    (hRet : I.inv c mid → I.inv c nach)
    (hVor : I.inv c vor) : I.inv c nach :=
  hRet ((nichtschreiber_erhaelt Nb J I c Wc Gc hAb hFrameT hFrameG
    k g vor mid hkg hkv hkm hN).mp hVor)

/-
CUTS:
- (a) shows independence of the two conjuncts, not that either is false.
- (b) shows the "mover" proves transport-then-restore, i.e. sequential
  composition `vor → mid → nach`, not commutation of two sections.
- `reduktion_seriell` itself (two accesses order by HB via `kein_wettlauf`)
  is not challenged; the finding is that the ORDER never feeds the CHAIN.
-/
#print axioms Gabbro.Grammatik.audit_hb_sidecar_ohne_kette
#print axioms Gabbro.Grammatik.audit_kette_ohne_run
