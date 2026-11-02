module
public import Grammatik.Speichermodell.Maschine.MaschineW.Teil1Basis

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Speichermodell.Maschine.Sicht

@[expose] public section



namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}
/-! ## 3. Views grow -/

section Wachsen

variable {ord : D.Glob → Ordnung}

theorem lesesicht_ge (wahl : D.Tab ⊕ D.Glob → NachrichtW D) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) (x : D.Tab ⊕ D.Glob),
      v x ≤ lesesicht ord wahl rs v x
  | [], _, _ => Nat.le_refl _
  | c :: rs, v, x => Nat.le_trans (lesesicht_ge wahl rs v x) (Sicht.verein_links _ _ x)

/-- A carrier read in the list: the view reaches the message read there. -/
theorem lesesicht_mem (wahl : D.Tab ⊕ D.Glob → NachrichtW D) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) (c : D.Tab ⊕ D.Glob), c ∈ rs →
      ∀ x, beitrag (ordVon ord c) c (wahl c) x ≤ lesesicht ord wahl rs v x
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | c' :: rs, v, c, h, x => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Sicht.verein_rechts _ _ x
      · exact Nat.le_trans (lesesicht_mem wahl rs v c h x) (Sicht.verein_links _ _ x)

/-- The view after reads stays below a bound that bounds the view and every contribution. -/
theorem lesesicht_le (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (T : D.Tab ⊕ D.Glob → Nat) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D), (∀ x, v x ≤ T x) →
      (∀ c ∈ rs, ∀ x, beitrag (ordVon ord c) c (wahl c) x ≤ T x) →
      ∀ x, lesesicht ord wahl rs v x ≤ T x
  | [], _, hv, _, x => hv x
  | c :: rs, v, hv, hb, x => by
      show max (lesesicht ord wahl rs v x) (beitrag (ordVon ord c) c (wahl c) x) ≤ T x
      exact Nat.max_le.mpr ⟨lesesicht_le wahl T rs v hv (fun c' h => hb c' (List.mem_cons_of_mem _ h)) x,
        hb c List.mem_cons_self x⟩

theorem locksicht_ge (ls : D.Lock → SichtW D) :
    ∀ (Ls : List D.Lock) (v : SichtW D) (x : D.Tab ⊕ D.Glob), v x ≤ locksicht ls Ls v x
  | [], _, _ => Nat.le_refl _
  | _ :: Ls, v, x => Nat.le_trans (locksicht_ge ls Ls v x) (Sicht.verein_links _ _ x)

theorem locksicht_mem (ls : D.Lock → SichtW D) :
    ∀ (Ls : List D.Lock) (v : SichtW D) (L : D.Lock), L ∈ Ls →
      ∀ x, ls L x ≤ locksicht ls Ls v x
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | L' :: Ls, v, L, h, x => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Sicht.verein_rechts _ _ x
      · exact Nat.le_trans (locksicht_mem ls Ls v L h x) (Sicht.verein_links _ _ x)

theorem locksicht_le (ls : D.Lock → SichtW D) (T : D.Tab ⊕ D.Glob → Nat) :
    ∀ (Ls : List D.Lock) (v : SichtW D), (∀ x, v x ≤ T x) → (∀ L ∈ Ls, ∀ x, ls L x ≤ T x) →
      ∀ x, locksicht ls Ls v x ≤ T x
  | [], _, hv, _, x => hv x
  | L :: Ls, v, hv, hL, x => by
      show max (locksicht ls Ls v x) (ls L x) ≤ T x
      exact Nat.max_le.mpr ⟨locksicht_le ls T Ls v hv (fun L' h => hL L' (List.mem_cons_of_mem _ h)) x,
        hL L List.mem_cons_self x⟩

/-- The view before the writes is at least the old view. -/
theorem vorSicht_ge (W : RufMaschineW D) (u : Faden) (σ : Speicher D) (M'' : RufMaschineG D)
    (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (x : D.Tab ⊕ D.Glob) :
    W.sicht u x ≤ vorSicht ord W u σ M'' wahl x :=
  Nat.le_trans (lesesicht_ge wahl _ _ x) (locksicht_ge _ _ _ x)

/-- **Views only grow**: the acting thread's view after a step is at least the one before. -/
theorem sicht_waechst {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (t : Faden) (x : D.Tab ⊕ D.Glob) : W.sicht t x ≤ W'.sicht t x := by
  by_cases ht : t = u
  · subst ht
    have hv := vorSicht_ge (ord := ord) W t σ M'' wahl x
    by_cases hw : SchreibG (mitSpeicher W.g σ) M'' t x
    · rw [h.sichtS x hw]
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt hv (h.frisch x hw).1)
    · rw [h.sichtU x hw]; exact hv
  · rw [h.sichtF t ht]; exact Nat.le_refl _

/-- The view after a step is at least the view before the writes. -/
theorem vor_le_nach {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (x : D.Tab ⊕ D.Glob) : vorSicht ord W u σ M'' wahl x ≤ W'.sicht u x := by
  by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u x
  · rw [h.sichtS x hw]; exact Nat.le_of_lt (h.frisch x hw).1
  · rw [h.sichtU x hw]; exact Nat.le_refl _

/-- A carrier the step reads is in its read list. -/
theorem lesenVon_mem {M M' : RufMaschineG D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    (h : LiestG M M' u c) : c ∈ lesenVon M M' u :=
  List.mem_filterMap.mpr ⟨(c, false), h, rfl⟩

/-- **Coherence of a read, on EVERY program** (by construction of W): the message a step
    reads at `c` lies at or above the reader's view, and afterwards the reader's view has
    reached it -- so a later read of `c` by the same thread never returns an older message
    (CoRR), nor one older than its own write (CoWR). -/
theorem schrittW_kohaerent {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hl : LiestG (mitSpeicher W.g σ) M'' u c) :
    W.sicht u c ≤ (wahl c).ts ∧ (wahl c).ts ≤ W'.sicht u c := by
  refine ⟨(h.lies c hl).1.2, ?_⟩
  have h1 := lesesicht_mem (ord := ord) wahl _ (W.sicht u) c (lesenVon_mem hl) c
  have h2 := beitrag_selbst (ordVon ord c) c (wahl c)
  exact Nat.le_trans h2 (Nat.le_trans h1 (Nat.le_trans (locksicht_ge _ _ _ c) (vor_le_nach h c)))

/-- **Release/acquire, on EVERY program** (by construction of W): an acquire read (a carrier of
    order `freigabe`) of a message joins the message's view -- for a release write, the writer's
    view at the write -- into the reader's view: every write the writer had seen, the reader
    now sees at least as new. -/
theorem schrittW_erwerb {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hl : LiestG (mitSpeicher W.g σ) M'' u c)
    (ho : ordVon ord c = .freigabe) (x : D.Tab ⊕ D.Glob) : (wahl c).sicht x ≤ W'.sicht u x := by
  have h1 := lesesicht_mem (ord := ord) wahl _ (W.sicht u) c (lesenVon_mem hl) x
  rw [ho] at h1
  exact Nat.le_trans (Sicht.verein_links _ _ x)
    (Nat.le_trans h1 (Nat.le_trans (locksicht_ge _ _ _ x) (vor_le_nach h x)))

theorem lsicht_waechst {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (L : D.Lock) (x : D.Tab ⊕ D.Glob) : W.lsicht L x ≤ W'.lsicht L x := by
  rw [h.lsicht L]
  split
  · exact Sicht.verein_links _ _ x
  · exact Nat.le_refl _

end Wachsen

/-! ## 4. Memories agreeing on every carrier are equal -/

theorem speicher_ext {s s' : Speicher D} (h : ∀ c, TraegerGleich s s' c) : s = s' := by
  cases s with
  | mk sl gl =>
    cases s' with
    | mk sl' gl' =>
      have e1 : sl = sl' := funext fun t => h (.inl t)
      have e2 : gl = gl' := funext fun g => h (.inr g)
      subst e1 e2
      rfl

theorem mitSpeicher_selbst (M : RufMaschineG D) : mitSpeicher M M.speicher = M := by
  cases M; rfl

/-- Not written: the step leaves the carrier as it was. -/
theorem traegerGleich_of_nicht_schreib {M M' : RufMaschineG D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    (h : ¬ SchreibG M M' u c) : TraegerGleich M'.speicher M.speicher c :=
  Classical.byContradiction fun hn => h (Or.inr hn)

theorem traegerGleich_trans {s s' s'' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h1 : TraegerGleich s s' c) (h2 : TraegerGleich s' s'' c) : TraegerGleich s s'' c := by
  cases c
  · exact h1.trans h2
  · exact h1.trans h2

theorem traegerGleich_symm {s s' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h : TraegerGleich s s' c) : TraegerGleich s' s c := by
  cases c
  · exact h.symm
  · exact h.symm

/-- **A step of W whose presented memory is G's own is a step of G**, and its G-part is G's
    successor. -/
theorem schrittW_g {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
    {W W' : RufMaschineW D} {u : Faden} {M'' : RufMaschineG D}
    {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' W.g.speicher M'' wahl neu) :
    RufSchrittG P O passes W.g u M'' ∧ W'.g = M'' := by
  have hs := h.schritt
  rw [mitSpeicher_selbst] at hs
  refine ⟨hs, ?_⟩
  have esp : W'.g.speicher = M''.speicher := speicher_ext fun c => by
    by_cases hw : SchreibG (mitSpeicher W.g W.g.speicher) M'' u c
    · exact h.speicherS c hw
    · have h1 := h.speicherU c hw
      have h2 := traegerGleich_of_nicht_schreib hw
      rw [mitSpeicher_selbst] at h2
      exact traegerGleich_trans h1 (traegerGleich_symm h2)
  have e1 := h.faeden
  have e2 := h.lauf
  have e3 := h.start
  cases hW' : W'.g with
  | mk sp fa la st =>
    cases M'' with
    | mk sp'' fa'' la'' st'' =>
      rw [hW'] at esp e1 e2 e3
      simp only at esp e1 e2 e3
      subst esp e1 e2 e3
      rfl

/-! ## 5. Every run of G is a run of W (`w_aus_g`) -/

section Einbettung

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-- **The SC shape of a W state**: a bound `T` per carrier that a message carrying G's value
    reaches, and that bounds every timestamp and every view. Always writing at `T + 1` and
    reading the message at `T` keeps it. -/
def SCForm (W : RufMaschineW D) : Prop :=
  ∃ T : D.Tab ⊕ D.Glob → Nat, ∀ c,
    (∃ m ∈ W.hist c, m.ts = T c ∧ TraegerGleich W.g.speicher m.wert c) ∧
    (∀ m ∈ W.hist c, m.ts ≤ T c) ∧ (∀ t, W.sicht t c ≤ T c) ∧ (∀ L, W.lsicht L c ≤ T c) ∧
    (∀ x, ∀ m ∈ W.hist x, m.sicht c ≤ T c)

theorem scForm_start (M0 : RufMaschineG D) : SCForm (RufStartW M0) :=
  ⟨fun _ => 0, fun c => ⟨⟨⟨0, M0.speicher, Sicht.null⟩, List.mem_singleton_self _, rfl,
    traegerGleich_refl _ c⟩, fun m hm => by rw [List.mem_singleton.mp hm]; exact Nat.le_refl 0,
    fun _ => Nat.le_refl _,
    fun _ => Nat.le_refl _, fun _ m hm => by rw [List.mem_singleton.mp hm]; exact Nat.le_refl _⟩⟩

theorem beitrag_le {T : D.Tab ⊕ D.Glob → Nat} {o : Ordnung} {c : D.Tab ⊕ D.Glob} {m : NachrichtW D}
    (hts : m.ts ≤ T c) (hs : ∀ x, m.sicht x ≤ T x) (x : D.Tab ⊕ D.Glob) : beitrag o c m x ≤ T x := by
  have heins : Sicht.eins c m.ts x ≤ T x := by
    unfold Sicht.eins
    split
    · rename_i h; subst h; exact hts
    · exact Nat.zero_le _
  cases o
  · exact heins
  · exact Nat.max_le.mpr ⟨hs x, heins⟩

end Einbettung
end Gabbro.Grammatik
