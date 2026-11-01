module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Speichermodell.Maschine.Sicht
public import Grammatik.Speichermodell.Maschine.MaschineW.Teil1

@[expose] public section

namespace Gabbro.Grammatik
open Speichermodell
variable {D : Deklaration}
section Einbettung
variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-- **One G step lifts to a W step** that keeps the SC shape; every write sits right above the
    message read at its carrier (`neu c = ts + 1`: the step is atomic for an RMW, `RMW.lean`). -/
theorem schrittW_aus_g {W : RufMaschineW D} (hF : SCForm W) {u : Faden} {M' : RufMaschineG D}
    (hs : RufSchrittG P O passes W.g u M') :
    ∃ W' σ M'' wahl neu, SchrittW P O passes ord W u W' σ M'' wahl neu ∧
      (∀ c, neu c = (wahl c).ts + 1) ∧ W'.g = M' ∧ SCForm W' := by
  obtain ⟨T, hT⟩ := hF
  let wahl : D.Tab ⊕ D.Glob → NachrichtW D := fun c => Classical.choose (hT c).1
  have hwahl : ∀ c, wahl c ∈ W.hist c ∧ (wahl c).ts = T c ∧
      TraegerGleich W.g.speicher (wahl c).wert c := fun c => by
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (hT c).1
    exact ⟨h1, h2, h3⟩
  let Mσ := mitSpeicher W.g W.g.speicher
  have eMσ : Mσ = W.g := mitSpeicher_selbst W.g
  let v := vorSicht ord W u W.g.speicher M' wahl
  have hvT : ∀ x, v x ≤ T x := by
    apply locksicht_le _ T _ _ _ (fun L _ x => (hT x).2.2.2.1 L)
    apply lesesicht_le wahl T _ _ (fun x => (hT x).2.2.1 u)
    intro c _ x
    exact beitrag_le (Nat.le_of_eq (hwahl c).2.1) (fun y => (hT y).2.2.2.2 c (wahl c) (hwahl c).1) x
  let neu : D.Tab ⊕ D.Glob → Nat := fun c => T c + 1
  let schreibt : D.Tab ⊕ D.Glob → Prop := fun c => SchreibG Mσ M' u c
  let T' : D.Tab ⊕ D.Glob → Nat := fun c => if schreibt c then T c + 1 else T c
  have hTT' : ∀ c, T c ≤ T' c := fun c => by
    show T c ≤ (if schreibt c then T c + 1 else T c)
    split <;> omega
  let s' : SichtW D := fun c => if schreibt c then neu c else v c
  let W' : RufMaschineW D :=
    ⟨M',
     fun c => if schreibt c then nachricht (ordVon ord c) v c (neu c) M'.speicher :: W.hist c
       else W.hist c,
     fun t => if t = u then s' else W.sicht t,
     fun L => if L ∈ gegebenVon Mσ M' u then (W.lsicht L).verein s' else W.lsicht L⟩
  have hs' : RufSchrittG P O passes Mσ u M' := by rw [eMσ]; exact hs
  have hs'T : ∀ x, s' x ≤ T' x := fun x => by
    show (if schreibt x then neu x else v x) ≤ (if schreibt x then T x + 1 else T x)
    split
    · exact Nat.le_refl _
    · exact hvT x
  refine ⟨W', W.g.speicher, M', wahl, neu, ?_, fun c => by
    show T c + 1 = (wahl c).ts + 1
    rw [(hwahl c).2.1], rfl, ?_⟩
  · refine {
      schritt := hs'
      lies := fun c _ => ⟨⟨(hwahl c).1, by rw [(hwahl c).2.1]; exact (hT c).2.2.1 u⟩,
        (hwahl c).2.2⟩
      ungelesen := fun c _ => traegerGleich_refl _ c
      frisch := fun c _ => ⟨Nat.lt_succ_of_le (hvT c), fun m hm he => by
        have := (hT c).2.1 m hm
        show False
        simp only [neu] at he
        omega⟩
      speicherS := fun c _ => traegerGleich_refl _ c
      speicherU := fun c hw => by
        have h := traegerGleich_of_nicht_schreib hw
        exact h
      faeden := rfl
      lauf := rfl
      start := rfl
      histS := fun c hw => by
        show (if schreibt c then _ else _) = _
        rw [if_pos hw]
      histU := fun c hw => by
        show (if schreibt c then _ else _) = _
        rw [if_neg hw]
      sichtS := fun c hw => by
        show (if u = u then s' else W.sicht u) c = neu c
        rw [if_pos rfl]
        show (if schreibt c then neu c else v c) = neu c
        rw [if_pos hw]
      sichtU := fun c hw => by
        show (if u = u then s' else W.sicht u) c = v c
        rw [if_pos rfl]
        show (if schreibt c then neu c else v c) = v c
        rw [if_neg hw]
      sichtF := fun t ht => by
        show (if t = u then s' else W.sicht t) = W.sicht t
        rw [if_neg ht]
      lsicht := fun L => by
        show (if L ∈ gegebenVon Mσ M' u then (W.lsicht L).verein s' else W.lsicht L) =
          (if L ∈ gegebenVon Mσ M' u then
            (W.lsicht L).verein (if u = u then s' else W.sicht u) else W.lsicht L)
        rw [if_pos (rfl : u = u)]
      rmw := fun g _ => by
        show T (.inr g) + 1 = (wahl (.inr g)).ts + 1
        rw [(hwahl (.inr g)).2.1] }
  · refine ⟨T', fun c => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · -- the message at the bound carries G's value
      by_cases hw : schreibt c
      · refine ⟨nachricht (ordVon ord c) v c (neu c) M'.speicher, ?_, ?_, traegerGleich_refl _ c⟩
        · show _ ∈ (if schreibt c then _ else _)
          rw [if_pos hw]; exact List.mem_cons_self
        · show neu c = (if schreibt c then T c + 1 else T c)
          rw [if_pos hw]
      · refine ⟨wahl c, ?_, ?_, ?_⟩
        · show _ ∈ (if schreibt c then _ else _)
          rw [if_neg hw]; exact (hwahl c).1
        · show (wahl c).ts = (if schreibt c then T c + 1 else T c)
          rw [if_neg hw]; exact (hwahl c).2.1
        · have h1 : TraegerGleich M'.speicher Mσ.speicher c := traegerGleich_of_nicht_schreib hw
          rw [eMσ] at h1
          exact traegerGleich_trans h1 (hwahl c).2.2
    · intro m hm
      change m ∈ (if schreibt c then _ else _) at hm
      by_cases hw : schreibt c
      · rw [if_pos hw] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · show neu c ≤ (if schreibt c then T c + 1 else T c)
          rw [if_pos hw]
          exact Nat.le_refl _
        · exact Nat.le_trans ((hT c).2.1 m hm) (hTT' c)
      · rw [if_neg hw] at hm
        exact Nat.le_trans ((hT c).2.1 m hm) (hTT' c)
    · intro t
      show (if t = u then s' else W.sicht t) c ≤ T' c
      split
      · exact hs'T c
      · exact Nat.le_trans ((hT c).2.2.1 t) (hTT' c)
    · intro L
      show (if L ∈ gegebenVon Mσ M' u then (W.lsicht L).verein s' else W.lsicht L) c ≤ T' c
      split
      · exact Nat.max_le.mpr ⟨Nat.le_trans ((hT c).2.2.2.1 L) (hTT' c), hs'T c⟩
      · exact Nat.le_trans ((hT c).2.2.2.1 L) (hTT' c)
    · intro x m hm
      change m ∈ (if schreibt x then _ else _) at hm
      by_cases hw : schreibt x
      · rw [if_pos hw] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · show (match ordVon ord x with
            | .entspannt => Sicht.eins x (neu x)
            | .freigabe => v.setze x (neu x)) c ≤ T' c
          have hx : neu x ≤ T' x := by
            show neu x ≤ (if schreibt x then T x + 1 else T x)
            rw [if_pos hw]
            exact Nat.le_refl _
          cases ordVon ord x
          · show (if c = x then neu x else 0) ≤ T' c
            split
            · rename_i h; subst h; exact hx
            · exact Nat.zero_le _
          · show (if c = x then neu x else v c) ≤ T' c
            split
            · rename_i h; subst h; exact hx
            · exact Nat.le_trans (hvT c) (hTT' c)
        · exact Nat.le_trans ((hT c).2.2.2.2 x m hm) (hTT' c)
      · rw [if_neg hw] at hm
        exact Nat.le_trans ((hT c).2.2.2.2 x m hm) (hTT' c)

/-- `schrittW_aus_g` with the witnesses packed (the shape its first callers use). -/
theorem schrittW_aus_gW {W : RufMaschineW D} (hF : SCForm W) {u : Faden} {M' : RufMaschineG D}
    (hs : RufSchrittG P O passes W.g u M') :
    ∃ W', RufSchrittW P O passes ord W u W' ∧ W'.g = M' ∧ SCForm W' := by
  obtain ⟨W', σ, M'', wahl, neu, hstep, _, hg, hF'⟩ := schrittW_aus_g (ord := ord) hF hs
  exact ⟨W', ⟨σ, M'', wahl, neu, hstep⟩, hg, hF'⟩

/-- **Every run of G is a run of W** (for every choice of orders): W adds behaviour, it
    removes none. -/
theorem w_aus_g {M0 M : RufMaschineG D} (hr : RufErreichbarG P O passes M0 M) :
    ∃ W, RufErreichbarW P O passes ord (RufStartW M0) W ∧ W.g = M ∧ SCForm W := by
  induction hr with
  | start => exact ⟨RufStartW M0, .start, rfl, scForm_start M0⟩
  | schritt M M' u _ hs ih =>
      obtain ⟨W, hW, rfl, hF⟩ := ih
      obtain ⟨W', σ, M'', wahl, neu, hstep, _, hg, hF'⟩ := schrittW_aus_g (ord := ord) hF hs
      exact ⟨W', .schritt W W' u hW ⟨σ, M'', wahl, neu, hstep⟩, hg, hF'⟩

/-- **Building a W step with ANY admissible reads** (for witnesses): given a G step on a
    presented memory that agrees with G's memory off the reads and with the chosen messages at
    the reads, and a bound `T` on every timestamp and view, W takes the step, writing at
    `T + 1`. -/
theorem schrittW_bau {W : RufMaschineW D} {σ : Speicher D} {u : Faden} {M'' : RufMaschineG D}
    (hs : RufSchrittG P O passes (mitSpeicher W.g σ) u M'')
    (wahl : D.Tab ⊕ D.Glob → NachrichtW D)
    (hl : ∀ c, LiestG (mitSpeicher W.g σ) M'' u c →
      Lesbar W.hist (W.sicht u) c (wahl c) ∧ TraegerGleich σ (wahl c).wert c)
    (hu : ∀ c, ¬ LiestG (mitSpeicher W.g σ) M'' u c → TraegerGleich σ W.g.speicher c)
    (T : D.Tab ⊕ D.Glob → Nat)
    (hT : ∀ c, (∀ m ∈ W.hist c, m.ts ≤ T c) ∧ (∀ t, W.sicht t c ≤ T c) ∧
      (∀ L, W.lsicht L c ≤ T c) ∧ (∀ x, ∀ m ∈ W.hist x, m.sicht c ≤ T c))
    (hwahl : ∀ c, wahl c ∈ W.hist c)
    (hrmw : ∀ g, ExchangeKopf W.g u g → T (.inr g) = (wahl (.inr g)).ts) :
    ∃ W', SchrittW P O passes ord W u W' σ M'' wahl (fun c => T c + 1) ∧
      (∀ c, SchreibG (mitSpeicher W.g σ) M'' u c → TraegerGleich W'.g.speicher M''.speicher c) ∧
      (∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c →
        TraegerGleich W'.g.speicher W.g.speicher c) := by
  classical
  let Mσ := mitSpeicher W.g σ
  let v := vorSicht ord W u σ M'' wahl
  have hvT : ∀ x, v x ≤ T x := by
    apply locksicht_le _ T _ _ _ (fun L _ x => (hT x).2.2.1 L)
    apply lesesicht_le wahl T _ _ (fun x => (hT x).2.1 u)
    intro c _ x
    exact beitrag_le ((hT c).1 _ (hwahl c)) (fun y => (hT y).2.2.2 c (wahl c) (hwahl c)) x
  let schreibt : D.Tab ⊕ D.Glob → Prop := fun c => SchreibG Mσ M'' u c
  let sp' : Speicher D :=
    ⟨fun t => if schreibt (.inl t) then M''.speicher.slots t else W.g.speicher.slots t,
     fun g => if schreibt (.inr g) then M''.speicher.globs g else W.g.speicher.globs g⟩
  have hsp1 : ∀ c, schreibt c → TraegerGleich sp' M''.speicher c := by
    intro c hc
    cases c with
    | inl t => show (if schreibt (.inl t) then _ else _) = _; rw [if_pos hc]
    | inr g => show (if schreibt (.inr g) then _ else _) = _; rw [if_pos hc]
  have hsp2 : ∀ c, ¬ schreibt c → TraegerGleich sp' W.g.speicher c := by
    intro c hc
    cases c with
    | inl t => show (if schreibt (.inl t) then _ else _) = _; rw [if_neg hc]
    | inr g => show (if schreibt (.inr g) then _ else _) = _; rw [if_neg hc]
  let s' : SichtW D := fun c => if schreibt c then T c + 1 else v c
  let W' : RufMaschineW D :=
    ⟨{ M'' with speicher := sp' },
     fun c => if schreibt c then nachricht (ordVon ord c) v c (T c + 1) sp' :: W.hist c
       else W.hist c,
     fun t => if t = u then s' else W.sicht t,
     fun L => if L ∈ gegebenVon Mσ M'' u then (W.lsicht L).verein s' else W.lsicht L⟩
  refine ⟨W', ?_, hsp1, hsp2⟩
  exact {
    schritt := hs
    lies := hl
    ungelesen := hu
    frisch := fun c _ => ⟨Nat.lt_succ_of_le (hvT c), fun m hm he => by
      have := (hT c).1 m hm
      omega⟩
    speicherS := hsp1
    speicherU := hsp2
    faeden := rfl
    lauf := rfl
    start := rfl
    histS := fun c hw => by
      show (if schreibt c then _ else _) = _
      rw [if_pos hw]
    histU := fun c hw => by
      show (if schreibt c then _ else _) = _
      rw [if_neg hw]
    sichtS := fun c hw => by
      show (if u = u then s' else W.sicht u) c = T c + 1
      rw [if_pos rfl]
      show (if schreibt c then T c + 1 else v c) = T c + 1
      rw [if_pos hw]
    sichtU := fun c hw => by
      show (if u = u then s' else W.sicht u) c = v c
      rw [if_pos rfl]
      show (if schreibt c then T c + 1 else v c) = v c
      rw [if_neg hw]
    sichtF := fun t ht => by
      show (if t = u then s' else W.sicht t) = W.sicht t
      rw [if_neg ht]
    lsicht := fun L => by
      show (if L ∈ gegebenVon Mσ M'' u then (W.lsicht L).verein s' else W.lsicht L) =
        (if L ∈ gegebenVon Mσ M'' u then
          (W.lsicht L).verein (if u = u then s' else W.sicht u) else W.lsicht L)
      rw [if_pos (rfl : u = u)]
    rmw := fun g hk => by
      show T (.inr g) + 1 = (wahl (.inr g)).ts + 1
      rw [hrmw g hk] }

end Einbettung

#print axioms Gabbro.Grammatik.schrittW_bau
#print axioms Gabbro.Grammatik.schrittW_g
#print axioms Gabbro.Grammatik.w_aus_g

end Gabbro.Grammatik
