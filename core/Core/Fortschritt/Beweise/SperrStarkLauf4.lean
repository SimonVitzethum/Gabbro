/-
  File:      Core/Fortschritt/Beweise/SperrStarkLauf4.lean
  Subject:   THE NON-VACUOUS HAND-OVER RUN AND SATISFIABILITY (M8 2b).

  The unit `E_4` starts with a FREE lock and tickets `[A, B]`. The run takes the lock with
  `A` at tick 0 (a genuine admitted `nehmen` from the free start), stutters, then hands
  `A → B → free`. At `a = 1` the waiter `B` is at position one behind the real holder `A`;
  the release premise is discharged by the give steps at ticks 2 and 3.
-/
module

public import Core.Fortschritt.Beweise.SperrStarkHalter4

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

theorem schreiben_folge_gut4 {g : SpeicherGraph Unit Unit} (hk : g.graph.Konsistent)
    (hv : g.graph.Vollstaendig) (c : Kontext) (x : Unit) :
    ∃ es g', Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext c) g
      [⟨.schreiben, x, .ra, (), ()⟩] es g' ∧ g'.graph.Konsistent ∧ g'.graph.Vollstaendig := by
  have hmem : (Speicher.Art.schreiben ≠ Speicher.Art.aussen) := by decide
  let lab : Speicher.Etikett Unit Unit := ⟨.schreiben, x, .ra, (), ()⟩
  by_cases hq : HatQuelle g x
  · obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen hk hv
      (SpeicherAkteur.kontext c) lab (fun h => h.elim)
    have hf : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext c) g [lab]
        [(SpeicherAkteur.kontext c, lab)] g' :=
      .cons (.ohne (Or.inr hq)) hs (.nil _)
    exact ⟨_, _, hf, (hf.viele.gut hk hv).1, (hf.viele.gut hk hv).2⟩
  · obtain ⟨gmid, hs_init⟩ := Speicher.Zustand.schritt_ohne_lesen hk hv
      (SpeicherAkteur.initial x) lab (fun h => h.elim)
    have hz : Initialisierung (fun _ => ()) lab g
        [((SpeicherAkteur.initial x), lab)] gmid := .erste hmem hq hs_init
    have gut := hz.viele.gut hk hv
    obtain ⟨g', hs⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2
      (SpeicherAkteur.kontext c) lab (fun h => h.elim)
    have hf : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext c) g [lab]
        ((SpeicherAkteur.initial x, lab) :: (SpeicherAkteur.kontext c, lab) :: []) g' :=
      .cons hz hs (.nil _)
    exact ⟨_, _, hf, (hf.viele.gut hk hv).1, (hf.viele.gut hk hv).2⟩

theorem rmw_folge_gut4 {g : SpeicherGraph Unit Unit} (hk : g.graph.Konsistent)
    (hv : g.graph.Vollstaendig) (c : Kontext) (x : Unit) :
    ∃ es g', Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext c) g
      [⟨.rmw, x, .ra, (), ()⟩] es g' ∧ g'.graph.Konsistent ∧ g'.graph.Vollstaendig := by
  obtain ⟨r, es, g', folge⟩ := speicherzug_existiert (fun _ => ())
    (SpeicherAkteur.kontext c) hk hv .rmw x .ra () (fun _ => by decide)
  cases r
  exact ⟨es, g', folge, (folge.viele.gut hk hv).1, (folge.viele.gut hk hv).2⟩

noncomputable def g4_wit :=
  rmw_folge_gut4 s4_0_graph_gut.1 s4_0_graph_gut.2 A (E_4.einrichtung.sperrOrt ())

noncomputable def g4_es : List (SpeicherAkteur Unit × Speicher.Etikett Unit Unit) :=
  Classical.choose g4_wit

noncomputable def g4_g : SpeicherGraph Unit Unit := Classical.choose (Classical.choose_spec g4_wit)

theorem g4_mem : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext A) s4_0.graph
    [⟨.rmw, (E_4.einrichtung.sperrOrt ()), .ra, (), ()⟩] g4_es g4_g :=
  (Classical.choose_spec (Classical.choose_spec g4_wit)).1

theorem g4_gut : g4_g.graph.Konsistent ∧ g4_g.graph.Vollstaendig :=
  (Classical.choose_spec (Classical.choose_spec g4_wit)).2

/-- The state after the admitted take: `A` owns the lock, `B` waits at position one. -/
noncomputable def s4_1 : Zustand Unit Unit Unit Unit Bool Unit :=
  { s4_0 with sperren := Function.update s4_0.sperren () ⟨some A, [B]⟩, graph := g4_g }

noncomputable def g5_wit :=
  schreiben_folge_gut4 g4_gut.1 g4_gut.2 B (E_4.einrichtung.sperrOrt ())

noncomputable def g5_es : List (SpeicherAkteur Unit × Speicher.Etikett Unit Unit) :=
  Classical.choose g5_wit

noncomputable def g5_g : SpeicherGraph Unit Unit := Classical.choose (Classical.choose_spec g5_wit)

theorem g5_mem : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext B) s4_1.graph
    [⟨.schreiben, (E_4.einrichtung.sperrOrt ()), .ra, (), ()⟩] g5_es g5_g :=
  (Classical.choose_spec (Classical.choose_spec g5_wit)).1

noncomputable def s4_2 : Zustand Unit Unit Unit Unit Bool Unit :=
  { s4_1 with sperren := Function.update s4_1.sperren () ⟨some B, []⟩, graph := g5_g }

noncomputable def g6_wit := schreiben_folge_gut4
  ((g5_mem.viele.gut g4_gut.1 g4_gut.2).1) ((g5_mem.viele.gut g4_gut.1 g4_gut.2).2) B
  (E_4.einrichtung.sperrOrt ())

noncomputable def g6_es : List (SpeicherAkteur Unit × Speicher.Etikett Unit Unit) :=
  Classical.choose g6_wit

noncomputable def g6_g : SpeicherGraph Unit Unit := Classical.choose (Classical.choose_spec g6_wit)

theorem g6_mem : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext B) s4_2.graph
    [⟨.schreiben, (E_4.einrichtung.sperrOrt ()), .ra, (), ()⟩] g6_es g6_g :=
  (Classical.choose_spec (Classical.choose_spec g6_wit)).1

noncomputable def s4_3 : Zustand Unit Unit Unit Unit Bool Unit :=
  { s4_2 with sperren := Function.update s4_2.sperren () ⟨none, []⟩, graph := g6_g }

theorem s4_0_nimmt : (s4_0.sperren ()).Nimmt A ⟨some A, [B]⟩ := by
  change (SperrZustand.mk none [A, B]).Nimmt A ⟨some A, [B]⟩
  exact SperrZustand.Nimmt.frei A [B]

theorem s4_1_gibt : (s4_1.sperren ()).Gibt A ⟨some B, []⟩ := by
  change (SperrZustand.mk (some A) [B]).Gibt A ⟨some B, []⟩
  exact SperrZustand.Gibt.besitzer A [B]

theorem s4_2_gibt : (s4_2.sperren ()).Gibt B ⟨none, []⟩ := by
  change (SperrZustand.mk (some B) []).Gibt B ⟨none, []⟩
  exact SperrZustand.Gibt.besitzer B []

theorem e4StotterAusfuehr (t : Nat) (c : Kontext)
    (s : Zustand Unit Unit Unit Unit Bool Unit) :
    FuehrtSchrittAus E_4.einrichtung t c s s stutterPlan ⟨[], []⟩ s := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], s, .intern, .nil _, rfl⟩

theorem ausfuehr_nehmen0 : FuehrtSchrittAus E_4.einrichtung 0 A s4_0 s4_0 nehmenPlan
    ⟨g4_es, []⟩ s4_1 := by
  have hF : FuehrtAus E_4.einrichtung 0 A s4_0 s4_0 (.sperre () .nehmen)
      [⟨.rmw, (E_4.einrichtung.sperrOrt ()), .ra, (), ()⟩] [] s4_1 :=
    .sperre (e := E_4.einrichtung) (t := 0) (c := A) (s := s4_0) (u := s4_0) (SperrSchritt.nehmen s4_0_nimmt) (fun _ => trivial)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _, _, hF, g4_mem, rfl⟩

theorem ausfuehr_geben1 : FuehrtSchrittAus E_4.einrichtung 2 A s4_1 s4_1 wGebenPlan
    ⟨g5_es, []⟩ s4_2 := by
  have hF : FuehrtAus E_4.einrichtung 2 A s4_1 s4_1 (.sperre () .geben)
      [⟨.schreiben, (E_4.einrichtung.sperrOrt ()), .ra, (), ()⟩] [] s4_2 :=
    .sperre (e := E_4.einrichtung) (t := 2) (c := A) (s := s4_1) (u := s4_1) (SperrSchritt.geben s4_1_gibt) (fun _ => trivial)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _, _, hF, g5_mem, rfl⟩

theorem ausfuehr_geben2 : FuehrtSchrittAus E_4.einrichtung 3 B s4_2 s4_2 wGebenPlan
    ⟨g6_es, []⟩ s4_3 := by
  have hF : FuehrtAus E_4.einrichtung 3 B s4_2 s4_2 (.sperre () .geben)
      [⟨.schreiben, (E_4.einrichtung.sperrOrt ()), .ra, (), ()⟩] [] s4_3 :=
    .sperre (e := E_4.einrichtung) (t := 3) (c := B) (s := s4_2) (u := s4_2) (SperrSchritt.geben s4_2_gibt) (fun _ => trivial)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _, _, hF, g6_mem, rfl⟩

noncomputable def z4 (t : Nat) : Zustand Unit Unit Unit Unit Bool Unit :=
  if t = 0 then s4_0 else if t = 1 ∨ t = 2 then s4_1 else
  if t = 3 then s4_2 else s4_3

theorem z4_ge4 (t : Nat) : z4 (t + 4) = s4_3 := by
  unfold z4
  rw [if_neg (by omega : ¬ t + 4 = 0)]
  rw [if_neg (by omega : ¬ (t + 4 = 1 ∨ t + 4 = 2))]
  rw [if_neg (by omega : ¬ t + 4 = 3)]

theorem z4_kerne (t : Nat) : (z4 t).kerne = s4_0.kerne := by
  unfold z4
  split_ifs <;> rfl

theorem z4_status (t : Nat) : (z4 t).status = s4_0.status := by
  unfold z4
  split_ifs <;> rfl

theorem z4_besitzer (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : z4 t = s) :
    (s.sperren ()).besitzer =
      if t = 0 then none else if t = 1 ∨ t = 2 then some A else
      if t = 3 then some B else none := by
  rw [← hzs]
  unfold z4
  by_cases h0 : t = 0
  · subst t
    rw [if_pos rfl]
    rfl
  · by_cases h12 : t = 1 ∨ t = 2
    · rw [if_neg h0, if_pos h12]
      rfl
    · by_cases h3 : t = 3
      · subst t
        rw [if_neg (by decide : ¬ ((3 : Nat) = 0)), if_neg (by decide : ¬ ((3 : Nat) = 1 ∨ 3 = 2)),
          if_pos rfl]
        rfl
      · rw [if_neg h0, if_neg h12, if_neg h3]
        rfl

noncomputable def spur4 : Nat → Option (SchrittWahl Unit × SchrittSpur Unit Unit)
  | 0 => some (.kontext A (), ⟨g4_es, []⟩)
  | 1 => spurw 1
  | 2 => some (.kontext A (), ⟨g5_es, []⟩)
  | 3 => some (.kontext B (), ⟨g6_es, []⟩)
  | t + 4 => spurw (t + 4)

theorem spur4_spurw (t : Nat) : spur4 (t + 4) = spurw (t + 4) := by
  rfl

def takt4 : ∀ t, Takt (Lauffolge E_4 hw2) (KeinSchritt (Lauffolge E_4 hw2))
    t (some (z4 t)) (spur4 t) (some (z4 (t + 1)))
  | 0 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 0)
      ⟨0, hw2_opp0 rfl, s4_0_kerne0, s4_0_live A⟩
      (e4_impl_nehmen statisch4_A s4_0_nimmt) ausfuehr_nehmen0))
  | 1 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 1)
      ⟨1, hw2_opp1 (by decide : (1 : Nat) % 2 = 1), s4_0_kerne1, s4_0_live B⟩
      ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩ (e4StotterAusfuehr 1 B s4_1)))
  | 2 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 2)
      ⟨0, hw2_opp0 (by decide : (2 : Nat) % 2 = 0), s4_0_kerne0, s4_0_live A⟩
      (e4_impl_geben s4_1_gibt) ausfuehr_geben1))
  | 3 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 3)
      ⟨1, hw2_opp1 (by decide : (3 : Nat) % 2 = 1), s4_0_kerne1, s4_0_live B⟩
      (e4_impl_geben s4_2_gibt) ausfuehr_geben2))
  | t + 4 => by
      rw [spur4_spurw, z4_ge4]
      rw [show z4 (t + 5) = s4_3 by simpa [Nat.add_assoc] using z4_ge4 (t + 1)]
      by_cases hpar : (t + 4) % 2 = 0
      · have hpar' : (t + 2 + 2) % 2 = 0 := by omega
        have hsp : spurw (t + 4) = some ticketA := by
          rw [show t + 4 = (t + 2) + 2 by omega]
          exact spurw_ge2 (t + 2) hpar'
        rw [hsp]
        exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (t + 4))
          ⟨0, hw2_opp0 hpar, s4_0_kerne0, s4_0_live A⟩
          ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩ (e4StotterAusfuehr (t + 4) A s4_3)))
      · have h1 : (t + 4) % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (t + 4) with h0 | h1
          · exact (hpar h0).elim
          · exact h1
        have h1' : (t + 2 + 2) % 2 = 1 := by omega
        have hsp : spurw (t + 4) = some ticketB := by
          rw [show t + 4 = (t + 2) + 2 by omega]
          exact spurw_ge2' (t + 2) h1'
        rw [hsp]
        exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (t + 4))
          ⟨1, hw2_opp1 h1, s4_0_kerne1, s4_0_live B⟩
          ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩ (e4StotterAusfuehr (t + 4) B s4_3)))

noncomputable def ρ_4 : Maschine.Lauf E_4 :=
  ⟨s2_start, hw2, ⟨fun t => some (z4 t), spur4, takt4⟩⟩

theorem ρ_4_zustand (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : ρ_4.zeit.zustand t = some s) : z4 t = s := by
  have hzt : ρ_4.zeit.zustand t = some (z4 t) := rfl
  exact Option.some.inj (hzt.symm.trans hzs)

theorem e4_lauf : Laeufe E_4 h2 ρ_4 :=
  ⟨fair2.hardware, fair2.konform, zul_2, rfl⟩

theorem spur4_kein_absturz (t : Nat) : spur4 t ≠ some (.absturz, absturzSpur) := by
  intro hcon
  cases t with
  | zero =>
    rw [show spur4 0 = some (.kontext A (), ⟨g4_es, []⟩) by rfl] at hcon
    have hfst := congrArg Prod.fst (Option.some.inj hcon)
    cases hfst
  | succ t =>
    cases t with
    | zero =>
      rw [show spur4 1 = spurw 1 by rfl, spurw1] at hcon
      simp only [ticketB] at hcon
      have hfst := congrArg Prod.fst (Option.some.inj hcon)
      cases hfst
    | succ t =>
      cases t with
      | zero =>
        rw [show spur4 2 = some (.kontext A (), ⟨g5_es, []⟩) by rfl] at hcon
        have hfst := congrArg Prod.fst (Option.some.inj hcon)
        cases hfst
      | succ t =>
        cases t with
        | zero =>
          rw [show spur4 3 = some (.kontext B (), ⟨g6_es, []⟩) by rfl] at hcon
          have hfst := congrArg Prod.fst (Option.some.inj hcon)
          cases hfst
        | succ t =>
          rw [spur4_spurw] at hcon
          exact spurw_kein_absturz _ hcon

theorem z4_nodup : (s4_1.sperren ()).schlange.Nodup := by
  change [B].Nodup
  decide

theorem e4_halte : HalteSchranken E_4 ρ_4 := by
  intro l c a n hcont
  cases l
  intro H' hH
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans e4halten)
  subst hH5
  by_cases hn0 : n = 0
  · subst n
    have hkk : Kontextkosten ρ_4 c a 0 = 0 := rfl
    omega
  · have hlt : a < a + n := by omega
    obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
    have hz := ρ_4_zustand a s hzs
    have hownA := z4_besitzer a s hz
    by_cases ha0 : a = 0
    · subst a
      rw [if_pos rfl] at hownA
      cases hownA
    · by_cases ha12 : a = 1 ∨ a = 2
      · rw [if_neg ha0, if_pos ha12] at hownA
        have hcA : c = A := Option.some.inj (hown.symm.trans hownA)
        subst hcA
        have hn2 : n ≤ 2 := by
          by_contra hcontra
          have hn3 : 3 ≤ n := by omega
          have hlt2 : a + 2 < a + n := by omega
          obtain ⟨s', hzs', hown'⟩ := hcont (a + 2) (by omega) hlt2
          have hz' := ρ_4_zustand (a + 2) s' hzs'
          have hb' := z4_besitzer (a + 2) s' hz'
          rcases ha12 with ha | ha <;> subst a
          · simp at hb'
            rw [hb'] at hown'
            cases hown'
          · simp at hb'
            rw [hb'] at hown'
            cases hown'
        have hcost : Kontextkosten ρ_4 A a n ≤ n := zaehle_le _ _ _
        omega
      · by_cases ha3 : a = 3
        · subst ha3
          rw [if_neg (by decide : ¬ ((3 : Nat) = 0)), if_neg (by decide : ¬ ((3 : Nat) = 1 ∨ 3 = 2)),
            if_pos rfl] at hownA
          have hcB : c = B := Option.some.inj (hown.symm.trans hownA)
          subst hcB
          have hn1 : n ≤ 1 := by
            by_contra hcontra
            have hn2 : 2 ≤ n := by omega
            have hlt1 : 4 < 3 + n := by omega
            obtain ⟨s', hzs', hown'⟩ := hcont 4 (by omega) hlt1
            have hz' := ρ_4_zustand 4 s' hzs'
            have hb' := z4_besitzer 4 s' hz'
            simp at hb'
            rw [hb'] at hown'
            cases hown'
          have hcost : Kontextkosten ρ_4 B 3 n ≤ n := zaehle_le _ _ _
          omega
        · rw [if_neg ha0, if_neg ha12, if_neg ha3] at hownA
          rw [hownA] at hown
          cases hown

theorem starkeWarteLauf4_erfuellbar : StarkeWarteLaufAussage := by
  refine ⟨E_4, h2, ρ_4, B, 5, 1, ?_, e4_lauf, fair2, e4_halte, e4halten, ?_, ?_, ?_, ?_⟩
  · exact akzeptiert_E_4
  · refine ⟨s4_1, ?_, ?_, ?_⟩
    · rfl
    · exact ⟨A, by rfl, w_AB_ne⟩
    · rfl
  · intro s hzs
    have hz := ρ_4_zustand 1 s hzs
    rw [← hz]
    exact z4_nodup
  · intro k _
    exact spur4_kein_absturz k
  · intro h' b s hb hzs hown
    have hz := ρ_4_zustand b s hzs
    have hbown := z4_besitzer b s hz
    by_cases hb1 : b = 1
    · subst hb1
      rw [if_neg (by decide : ¬ ((1 : Nat) = 0)), if_pos (Or.inl rfl)] at hbown
      have hh : h' = A := Option.some.inj (hown.symm.trans hbown)
      subst hh
      refine ⟨2, by decide, ?_, ?_⟩
      · exact ⟨s4_1, s4_2, rfl, rfl, s4_1_gibt⟩
      · exact Nat.le_trans (zaehle_le _ _ _) (by omega)
    · by_cases hb2 : b = 2
      · subst hb2
        rw [if_neg (by decide : ¬ ((2 : Nat) = 0)), if_pos (Or.inr (Or.inl rfl))] at hbown
        have hh : h' = A := Option.some.inj (hown.symm.trans hbown)
        subst hh
        refine ⟨2, le_rfl, ?_, ?_⟩
        · exact ⟨s4_1, s4_2, rfl, rfl, s4_1_gibt⟩
        · exact Nat.le_trans (zaehle_le _ _ _) (by omega)
      · by_cases hb3 : b = 3
        · subst hb3
          rw [if_neg (by decide : ¬ ((3 : Nat) = 0)),
            if_neg (by decide : ¬ ((3 : Nat) = 1 ∨ 3 = 2)), if_pos rfl] at hbown
          have hh : h' = B := Option.some.inj (hown.symm.trans hbown)
          subst hh
          refine ⟨3, le_rfl, ?_, ?_⟩
          · exact ⟨s4_2, s4_3, rfl, rfl, s4_2_gibt⟩
          · exact Nat.le_trans (zaehle_le _ _ _) (by omega)
        · rw [if_neg (by omega : ¬ b = 0), if_neg (fun h => h.elim hb1 hb2), if_neg hb3] at hbown
          rw [hbown] at hown
          cases hown

end Gabbro.Core.Fortschritt
