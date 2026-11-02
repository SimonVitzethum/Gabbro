module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T3
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Non-writers preserve.** Where the invariant reads only its carrier (frame covered
    by `c`) and the step's writer does not write `c`, the whole-frame step (`hSchritt`
    via `schritt_rahmen_aus_korn`) preserves the invariant by `stabil`. -/
theorem nichtschreiber_erhaelt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv c))
    (hFrameT : ∀ t : D.Tab, Wc t = true → c = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → c = .inr x)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach)
    (hN : TraegerSchreibt (J.code g) c = false) :
    I.inv c vor ↔ I.inv c nach := by
  refine stabil hAb (schritt_rahmen_aus_korn Nb J k g vor nach hkg hkv hkn) ?_
  constructor
  · intro t ht
    have hc := hFrameT t ht
    cases c with
    | inl t₀ =>
      simp only [Sum.inl.injEq] at hc
      subst hc
      simp only [TraegerSchreibt] at hN
      exact hN
    | inr x₀ => simp only [reduceCtorEq] at hc
  · intro x hx
    have hc := hFrameG x hx
    cases c with
    | inl t₀ => simp only [reduceCtorEq] at hc
    | inr x₀ =>
      simp only [Sum.inr.injEq] at hc
      subst hc
      simp only [TraegerSchreibt] at hN
      exact hN

/-- **The chain lemma: entry plus return plus watch.** The invariant holds at every
    chain world: at the head by entry; across a writing step by return-under-guard
    (unlocked by the single watch premise); across a non-writing step by frame
    preservation (`nichtschreiber_erhaelt`). The guard link `hGuard` is carried
    (G5-style): it ties `L` to `c`, and is consumed where the watch is discharged
    (`wache_aus_schuld`). -/
theorem hinv_kette_aus_disziplin (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv c))
    (hFrameT : ∀ t : D.Tab, Wc t = true → c = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → c = .inr x)
    (hGuard : Bewacht (D := D) c L)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) c = true →
          L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) c = true →
          L ∈ D.haelt (J.code g)) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → I.inv c σ := by
  intro k
  induction k with
  | zero => exact hEntry
  | succ k ih =>
    intro σ hσ
    have hK := J.hKette
    have hlen : k + 1 < J.welten.length := lt_of_belegt J.welten (k + 1) σ hσ
    have hsk : k < J.schrittFaden.length := by omega
    have hwk : k < J.welten.length := by omega
    obtain ⟨g, hg⟩ := kette_welt_belegt J.schrittFaden k hsk
    obtain ⟨vor, hvor⟩ := kette_welt_belegt J.welten k hwk
    have hgm : g ∈ J.faeden := (J.hSchritt k g vor σ hg hvor hσ).1
    cases heq : TraegerSchreibt (J.code g) c with
    | true =>
      exact hReturn k g vor σ hgm hg hvor hσ heq
        (hWatch k g vor σ hgm hg hvor hσ heq)
    | false =>
      exact (nichtschreiber_erhaelt Nb J I c Wc Gc hAb hFrameT hFrameG
        k g vor σ hg hvor hσ heq).mp (ih vor hvor)

/-- Membership anywhere in a list is membership at some index. -/
theorem kette_belegt_of_mem {α : Type} (w : List α) (σ : α) (h : σ ∈ w) :
    ∃ k : Nat, w[k]? = some σ := by
  induction w with
  | nil => simp only [List.not_mem_nil] at h
  | cons a as ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero]⟩
    · obtain ⟨k, hk⟩ := ih h
      exact ⟨k + 1, by simp only [List.getElem?_cons_succ]; exact hk⟩

/-- A `schreibt`-hit inside a carrier list fires the `any`: the `schuldet` unfolding
    step for `wache_aus_schuld`. -/
theorem any_of_mem_true {α : Type} (ts : List α) (P : α → Bool) (t₀ : α)
    (hm : t₀ ∈ ts) (hP : P t₀ = true) : ts.any P = true := by
  induction ts with
  | nil => simp only [List.not_mem_nil] at hm
  | cons a as ih =>
    simp only [List.mem_cons] at hm
    simp only [List.any_cons]
    rcases hm with rfl | hm
    · simp only [hP, Bool.true_or]
    · cases hPa : P a with
      | true => simp only [Bool.true_or]
      | false => simp only [ih hm, Bool.or_true]

/-- **The watch, discharged for tables.** A writer of table `t₀` holds every guard in
    `t₀`'s watch list: coverage gives an owed invariant over `t₀` (its carrier list hits
    the writer's frame, so `schuldet` fires), U003 (`J.hSchuld`, proved per body by
    `schuldnerHaelt_gilt`) gives the declared holds, and the guard fact picks `L`.
    Globals are OUTSIDE this discharge: U003 is table-only (`Syntax.lean`:181-182). -/
theorem wache_aus_schuld (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (g : Faden) (hg : g ∈ J.faeden)
    (hW : TraegerSchreibt (J.code g) (.inl t₀) = true)
    (hCov : ∃ i : D.Inv, Sum.inl t₀ ∈ D.traeger i) :
    L ∈ D.haelt (J.code g) := by
  obtain ⟨i, hi⟩ := hCov
  have hP : D.schreibt (J.code g) t₀ = true := by
    unfold TraegerSchreibt at hW
    exact hW
  have hs : schuldet (J.code g) i = true := by
    unfold schuldet
    exact any_of_mem_true (D.traeger i) (Sum.elim (D.schreibt (J.code g)) (D.gschreibt (J.code g)))
      (Sum.inl t₀) hi hP
  exact J.hSchuld g hg i hs (Sum.inl t₀) hi L hGuardT

/-- **The invariant from discipline, CSL-exact (`lockFree → inv`).** For a table carrier
    with guard `L`: entry plus return-under-guard plus frame-locality, where the watch
    premise is DISCHARGED (`wache_aus_schuld` from `J.hSchuld` plus coverage) rather than
    assumed -- so no lock premise is owed here; the discipline cited above does the work.
    Table-scoped because U003 is table-only; see the section prose. -/
theorem hinv_aus_disziplin (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (t₀ : D.Tab) (L : D.Lock)
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
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, Sum.inl t₀ ∈ D.traeger i) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → LockFrei (D := D) L σ →
      I.inv (.inl t₀) σ := by
  intro k σ h _
  exact hinv_kette_aus_disziplin Nb J I (.inl t₀) L Wc Gc hAb hFrameT hFrameG
    hGuardT hEntry hReturn
    (fun k g vor nach hgm hkg hkv hkn hW =>
      wache_aus_schuld Nb J t₀ L hGuardT g hgm hW (hCov g hgm hW))
    k σ h

/-- **The derived context.** The per-carrier lemma folded over all carriers: entry,
    return-under-guard, frame-locality, guard existence, and the single watch premise
    per carrier yield the full `InvariantenKontext` (§4:207) -- the premise §20 assumed.
    For tables the watch discharges via `wache_aus_schuld`; for globals it is
    checker-side (see section prose). -/
theorem invariantenKontext_aus_disziplin (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (I : TraegerInv (D := D))
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAb : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameT : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameG : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g)) :
    InvariantenKontext Nb J I := by
  intro c σ hmem
  obtain ⟨k, hk⟩ := kette_belegt_of_mem J.welten σ hmem
  obtain ⟨L, hL⟩ := hGuardEx c
  exact hinv_kette_aus_disziplin Nb J I c L (Wc c) (Gc c) (hAb c) (hFrameT c)
    (hFrameG c) hL (hEntry c)
    (fun k g vor nach hgm hkg hkv hkn hW hHold =>
      hReturn c L k g vor nach hL hgm hkg hkv hkn hW hHold)
    (fun k g vor nach hgm hkg hkv hkn hW =>
      hWatch c L k g vor nach hL hgm hkg hkv hkn hW)
    k σ hk

/-- **The §20 chain on the derived premise.** `interferenceFree_of_invariantForm`
    (§20:1128) with the context derived above instead of assumed: same conclusion
    (`InterferenceFree`), §20 itself untouched. -/
theorem interferenceFree_of_invariantForm_aus_disziplin (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAb : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameT : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameG : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g))
    (hForm : InvariantForm Nb J I Q) :
    InterferenceFree Nb J Q :=
  interferenceFree_of_invariantForm Nb J I Q hForm
    (invariantenKontext_aus_disziplin Nb J I Wc Gc hAb hFrameT hFrameG hGuardEx
      hEntry hReturn hWatch)


end Gabbro.Grammatik
