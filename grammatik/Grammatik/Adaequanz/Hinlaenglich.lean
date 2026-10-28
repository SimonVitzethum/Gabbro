/-
  File:      Grammatik/Adaequanz/Hinlaenglich.lean
  Subject:   THEOREM 1 (SUFFICIENCY): the W-method of Chow (1978) for tree automata, with the bound `m` on the
             implementation's states (Vasilevskii's extension to `m > n`), over an arbitrary ranked signature.

  The spec `S` has the state type `Q` with `n = card Q` states, every state with an ACCESS tree
  (`S.lauf (acc q) = q`), and a list `W` of DISTINGUISHING contexts with the hole among them: two states with
  the same result in every context of `W` are equal (`trennt`; so `Q` is the set of Myhill-Nerode classes
  of the spec's result function, and `n` is its index). Then:

      every implementation `I` (a tree automaton, any state type `Q'` with `card Q' ≤ m`) that agrees with `S`
      on every tree of `testmenge W (m - n + 1)` agrees with `S` on EVERY tree.          (`hinlaenglich`)

  PROOF. (1) Two trees of the test layer with one `I`-state have one `S`-state (`W` sees no difference in `I`,
  hence none in `S`). (2) So the access trees reach `n` distinct `I`-states; the sets `R d` of `I`-states that
  layer `d` reaches grow, and a set that does not grow in one step is closed under every constructor; in a
  type of at most `m` elements it stops growing by `d = m - n`. (3) So every tree has the `I`-state of a tree
  of layer `m - n`, and that tree has the tree's `S`-state (induction over the tree, through the cells of
  layer `m - n + 1`). (4) The output then agrees through the hole context.

  Hypotheses, all explicit: the implementation is a tree automaton over the SAME signature (program-neutral),
  with at most `m` states; the spec is separated by `W` and reachable by `acc`; the lists `ks`/`qs` are
  complete.
-/
import Grammatik.Adaequanz.Schichten

namespace Gabbro.Grammatik.Adaequanz

set_option linter.unusedSectionVars false

variable {σ : Sig} {Q O : Type} [Fintype Q]

/-- The hypotheses on the spec: complete constructor and state lists, access trees, distinguishing contexts
    with the hole. -/
structure Spezifiziert (S : Automat σ Q O) (ks : List σ.K) (qs : List Q) (acc : Q → Baum σ)
    (W : List (Kontext σ)) : Prop where
  ks_voll : ∀ k, k ∈ ks
  qs_voll : ∀ q, q ∈ qs
  zugang : ∀ q, S.lauf (acc q) = q
  loch : Kontext.loch ∈ W
  trennt : ∀ q q', (∀ K ∈ W, S.semK K q = S.semK K q') → q = q'

section Beweis

variable {S : Automat σ Q O} {ks : List σ.K} {qs : List Q} {acc : Q → Baum σ} {W : List (Kontext σ)}
  (hS : Spezifiziert S ks qs acc W) {Q' : Type} [Fintype Q'] (I : Automat σ Q' O) {D : Nat}
  (hpass : ∀ p ∈ testmenge ks (qs.map acc) W D, I.sem p = S.sem p)

include hS hpass

/-- (1) Two trees of the test layer with one `I`-state have one `S`-state. -/
theorem trennt_schicht {t u : Baum σ} (ht : t ∈ schicht ks (qs.map acc) D)
    (hu : u ∈ schicht ks (qs.map acc) D) (h : I.lauf t = I.lauf u) : S.lauf t = S.lauf u := by
  apply hS.trennt
  intro K hK
  have h1 := hpass _ (ein_mem_testmenge ks _ hK ht)
  have h2 := hpass _ (ein_mem_testmenge ks _ hK hu)
  rw [Automat.sem_ein, Automat.sem_ein] at h1 h2
  rw [← h1, ← h2, h]

omit hpass in
theorem zugang_mem (q : Q) (d : Nat) : acc q ∈ schicht ks (qs.map acc) d :=
  schicht_mono ks _ (Nat.zero_le d) (List.mem_map.mpr ⟨q, hS.qs_voll q, rfl⟩)

end Beweis

open Classical in
/-- The `I`-states that layer `d` reaches. -/
noncomputable def erreicht {Q' : Type} (I : Automat σ Q' O) (ks : List σ.K) (a : List (Baum σ)) (d : Nat) :
    Finset Q' :=
  ((schicht ks a d).map I.lauf).toFinset

theorem mem_erreicht {Q' : Type} {I : Automat σ Q' O} {ks : List σ.K} {a : List (Baum σ)} {d : Nat} {x : Q'} :
    x ∈ erreicht I ks a d ↔ ∃ u ∈ schicht ks a d, I.lauf u = x := by
  classical
  simp only [erreicht, List.mem_toFinset, List.mem_map]

theorem erreicht_mono {Q' : Type} (I : Automat σ Q' O) (ks : List σ.K) (a : List (Baum σ)) (d : Nat) :
    erreicht I ks a d ⊆ erreicht I ks a (d + 1) := fun _ hx => by
  obtain ⟨u, hu, rfl⟩ := mem_erreicht.mp hx
  exact mem_erreicht.mpr ⟨u, schicht_mono ks a (Nat.le_succ d) hu, rfl⟩

/-- (2a) A layer that adds no state is closed: every tree has a state the layer reaches. -/
theorem erreicht_abgeschlossen {Q' : Type} (I : Automat σ Q' O) {ks : List σ.K} (hks : ∀ k, k ∈ ks)
    (a : List (Baum σ)) {d : Nat} (h : erreicht I ks a (d + 1) ⊆ erreicht I ks a d) :
    ∀ t, I.lauf t ∈ erreicht I ks a d := by
  intro t
  induction t with
  | knoten k ch ih =>
      choose u hu hlu using fun i => mem_erreicht.mp (ih i)
      apply h
      refine mem_erreicht.mpr ⟨Baum.knoten k u, knoten_mem_schicht ks hks a d k u hu, ?_⟩
      simp only [Automat.lauf_knoten, hlu]

section Beweis2

variable {S : Automat σ Q O} {ks : List σ.K} {qs : List Q} {acc : Q → Baum σ} {W : List (Kontext σ)}
  (hS : Spezifiziert S ks qs acc W) {Q' : Type} [Fintype Q'] (I : Automat σ Q' O) {m : Nat}
  (hm : Fintype.card Q' ≤ m)
  (hpass : ∀ p ∈ testmenge ks (qs.map acc) W (m - Fintype.card Q + 1), I.sem p = S.sem p)

include hS hm hpass

/-- (2b) The access trees reach at least `n` distinct `I`-states. -/
theorem erreicht_null :
    Fintype.card Q ≤ (erreicht I ks (qs.map acc) 0).card := by
  classical
  have hinj : Function.Injective fun q => I.lauf (acc q) := by
    intro q q' h
    have := trennt_schicht hS I hpass (zugang_mem hS q _) (zugang_mem hS q' _) h
    rwa [hS.zugang, hS.zugang] at this
  calc Fintype.card Q = (Finset.univ.image fun q => I.lauf (acc q)).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ _ := Finset.card_le_card fun x hx => by
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
        exact mem_erreicht.mpr ⟨acc q, zugang_mem hS q 0, rfl⟩

/-- (2c) The growth stops by layer `m - n`. -/
theorem erreicht_stopp :
    ∃ d ≤ m - Fintype.card Q, erreicht I ks (qs.map acc) (d + 1) ⊆ erreicht I ks (qs.map acc) d := by
  classical
  by_contra hne
  push Not at hne
  have h0 := erreicht_null hS I hm hpass
  have hle : ∀ d, (erreicht I ks (qs.map acc) d).card ≤ m := fun d =>
    (Finset.card_le_univ _).trans hm
  have hwachs : ∀ d ≤ m - Fintype.card Q + 1, Fintype.card Q + d ≤ (erreicht I ks (qs.map acc) d).card := by
    intro d
    induction d with
    | zero => intro _; simpa using h0
    | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        have hs : erreicht I ks (qs.map acc) d ⊂ erreicht I ks (qs.map acc) (d + 1) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨erreicht_mono I ks _ d, fun he => hne d (by omega) (he ▸ subset_refl _)⟩
        have := Finset.card_lt_card hs
        omega
  have h1 := hwachs (m - Fintype.card Q + 1) le_rfl
  have h2 := hle (m - Fintype.card Q + 1)
  have h3 := hle 0
  omega

/-- (3) Every tree has the `I`-state of a tree of layer `m - n`, and that tree has its `S`-state. -/
theorem vertreter :
    ∀ t, ∃ u ∈ schicht ks (qs.map acc) (m - Fintype.card Q), I.lauf u = I.lauf t := by
  obtain ⟨d, hd, hstopp⟩ := erreicht_stopp hS I hm hpass
  intro t
  obtain ⟨u, hu, hlu⟩ := mem_erreicht.mp (erreicht_abgeschlossen I hS.ks_voll _ hstopp t)
  exact ⟨u, schicht_mono ks _ hd hu, hlu⟩

theorem vertreter_spez :
    ∀ t, ∀ u ∈ schicht ks (qs.map acc) (m - Fintype.card Q), I.lauf u = I.lauf t → S.lauf u = S.lauf t := by
  intro t
  induction t with
  | knoten k ch ih =>
      intro u hu hlu
      choose v hv hlv using fun i => vertreter hS I hm hpass (ch i)
      have hvS : ∀ i, S.lauf (v i) = S.lauf (ch i) := fun i => ih i (v i) (hv i) (hlv i)
      have hw := knoten_mem_schicht ks hS.ks_voll _ _ k v hv
      have hwI : I.lauf (Baum.knoten k v) = I.lauf (Baum.knoten k ch) := by
        simp only [Automat.lauf_knoten, hlv]
      have hwS : S.lauf (Baum.knoten k v) = S.lauf (Baum.knoten k ch) := by
        simp only [Automat.lauf_knoten, hvS]
      rw [← hwS]
      exact trennt_schicht hS I hpass (schicht_mono ks _ (Nat.le_succ _) hu) hw (hlu.trans hwI.symm)

/-- **THEOREM 1 (sufficiency).** An implementation with at most `m` states that agrees with the spec on the
    test set of depth `m - n + 1` agrees with the spec on every tree. -/
theorem hinlaenglich : ∀ t, I.sem t = S.sem t := by
  intro t
  obtain ⟨u, hu, hlu⟩ := vertreter hS I hm hpass t
  have hS' := vertreter_spez hS I hm hpass t u hu hlu
  have hp := hpass _ (ein_mem_testmenge ks _ hS.loch (schicht_mono ks _ (Nat.le_succ _) hu))
  simp only [Kontext.ein] at hp
  simp only [Automat.sem] at hp ⊢
  rw [← hlu, hp, hS']

end Beweis2

/-- **The size of the test set** for the bound `m`: `|W| * N (m - n + 1)`, and for `m = n` (the spec-states
    case) `|W| * (n + Σ_k n ^ ar k)` when the state list has no repetition. -/
theorem hinlaenglich_groesse (ks : List σ.K) (qs : List Q) (acc : Q → Baum σ) (W : List (Kontext σ)) (m : Nat) :
    (testmenge ks (qs.map acc) W (m - Fintype.card Q + 1)).length
      = W.length * anzahl ks qs.length (m - Fintype.card Q + 1) := by
  rw [testmenge_laenge, List.length_map]

end Gabbro.Grammatik.Adaequanz
