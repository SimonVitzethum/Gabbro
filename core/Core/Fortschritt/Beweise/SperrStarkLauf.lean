/-
  File:      Core/Fortschritt/Beweise/SperrStarkLauf.lean
  Subject:   THE CONCRETE HAND-OVER RUN AND SATISFIABILITY (M8 2b).

  The fixed trace for `E_3`: `A` gives twice (first to itself, then to `B`), `B` gives to
  nobody, stutter in between and in the tail. Every premise of `StarkeWarteLaufAussage` is
  discharged here; the acceptance of `E_3` comes from `SperrStarkEinheit`.
-/
module

public import Core.Fortschritt.Beweise.SperrStarkEinheit

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/- A non-reading write can always be appended, and the resulting graph stays good. -/

theorem schreiben_folge_gut {g : SpeicherGraph Unit Unit} (hk : g.graph.Konsistent)
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

theorem rmw_folge_gut {g : SpeicherGraph Unit Unit} (hk : g.graph.Konsistent)
    (hv : g.graph.Vollstaendig) (c : Kontext) (x : Unit) :
    ∃ es g', Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext c) g
      [⟨.rmw, x, .ra, (), ()⟩] es g' ∧ g'.graph.Konsistent ∧ g'.graph.Vollstaendig := by
  obtain ⟨r, es, g', folge⟩ := speicherzug_existiert (fun _ => ())
    (SpeicherAkteur.kontext c) hk hv .rmw x .ra () (fun _ => by decide)
  cases r
  exact ⟨es, g', folge, (folge.viele.gut hk hv).1, (folge.viele.gut hk hv).2⟩

/- The concrete trace: `A` gives twice (first to itself, then to `B`), `B` gives to nobody,
   stutter in between and in the tail. -/

noncomputable def s3_1 : Zustand Unit Unit Unit Unit Bool Unit :=
  { s3_0 with sperren := Function.update s3_0.sperren () ⟨some A, [B]⟩ }

noncomputable def g3_wit := rmw_folge_gut s3_0_graph_gut.1 s3_0_graph_gut.2 A
  (E_3.einrichtung.sperrOrt ())

noncomputable def g3_es : List (SpeicherAkteur Unit × Speicher.Etikett Unit Unit) := Classical.choose g3_wit

noncomputable def g3_g : SpeicherGraph Unit Unit := Classical.choose (Classical.choose_spec g3_wit)

theorem g3_mem : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext A) s3_0.graph
    [⟨.rmw, (E_3.einrichtung.sperrOrt ()), .ra, (), ()⟩] g3_es g3_g :=
  (Classical.choose_spec (Classical.choose_spec g3_wit)).1

theorem g3_gut : g3_g.graph.Konsistent ∧ g3_g.graph.Vollstaendig :=
  (Classical.choose_spec (Classical.choose_spec g3_wit)).2

noncomputable def s3_2 : Zustand Unit Unit Unit Unit Bool Unit :=
  { s3_1 with sperren := Function.update s3_1.sperren () ⟨some B, []⟩, graph := g3_g }

noncomputable def g4_wit := schreiben_folge_gut g3_gut.1 g3_gut.2 B
  (E_3.einrichtung.sperrOrt ())

noncomputable def g4_es : List (SpeicherAkteur Unit × Speicher.Etikett Unit Unit) := Classical.choose g4_wit

noncomputable def g4_g : SpeicherGraph Unit Unit := Classical.choose (Classical.choose_spec g4_wit)

theorem g4_mem : Speicherfolge (fun _ => ()) (SpeicherAkteur.kontext B) s3_2.graph
    [⟨.schreiben, (E_3.einrichtung.sperrOrt ()), .ra, (), ()⟩] g4_es g4_g :=
  (Classical.choose_spec (Classical.choose_spec g4_wit)).1

noncomputable def s3_3 : Zustand Unit Unit Unit Unit Bool Unit :=
  { s3_2 with sperren := Function.update s3_2.sperren () ⟨none, []⟩, graph := g4_g }

theorem s3_0_gibt : (s3_0.sperren ()).Gibt A ⟨some A, [B]⟩ := by
  simpa only [s3_0_lock, SperrZustand.abgeben] using
    (SperrZustand.Gibt.besitzer A [A, B])

theorem s3_1_gibt : (s3_1.sperren ()).Gibt A ⟨some B, []⟩ := by
  simpa only [show (s3_1.sperren ()) = ⟨some A, [B]⟩ by rfl, SperrZustand.abgeben] using
    (SperrZustand.Gibt.besitzer A [B])

theorem s3_2_gibt : (s3_2.sperren ()).Gibt B ⟨none, []⟩ := by
  simpa only [show (s3_2.sperren ()) = ⟨some B, []⟩ by rfl, SperrZustand.abgeben] using
    (SperrZustand.Gibt.besitzer B [])

noncomputable def z3 (t : Nat) : Zustand Unit Unit Unit Unit Bool Unit :=
  if t = 0 then s3_0 else if t = 1 then s3_1 else
  if t = 2 then s3_1 else if t = 3 then s3_2 else s3_3

theorem z3_ge4 (t : Nat) : z3 (t + 4) = s3_3 := by
  unfold z3
  split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> try omega
  rfl

theorem z3_kerne (t : Nat) : (z3 t).kerne = zE0.kerne := by
  unfold z3
  split_ifs <;> rfl

theorem z3_status (t : Nat) : (z3 t).status = zE0.status := by
  unfold z3
  split_ifs <;> rfl

theorem z3_besitzer (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : z3 t = s) :
    (s.sperren ()).besitzer =
      if t = 0 ∨ t = 1 ∨ t = 2 then some A else if t = 3 then some B else none := by
  rw [← hzs]
  unfold z3
  by_cases h0 : t = 0
  · subst t
    rw [if_pos (by decide : (0 : Nat) = 0 ∨ 0 = 1 ∨ 0 = 2)]
    rfl
  · by_cases h1 : t = 1
    · subst t
      rw [if_pos (by decide : (1 : Nat) = 0 ∨ 1 = 1 ∨ 1 = 2)]
      rfl
    · by_cases h2 : t = 2
      · subst t
        rw [if_pos (by decide : (2 : Nat) = 0 ∨ 2 = 1 ∨ 2 = 2)]
        rfl
      · by_cases h3 : t = 3
        · subst t
          rw [if_neg (by decide : ¬ ((3 : Nat) = 0 ∨ 3 = 1 ∨ 3 = 2))]
          rw [if_pos (by decide : (3 : Nat) = 3)]
          rfl
        · rw [if_neg (by omega : ¬ (t = 0 ∨ t = 1 ∨ t = 2))]
          rw [if_neg h0, if_neg h1, if_neg h2]
          simp only [if_neg h3]
          rfl

theorem ausfuehr_geben_0 : FuehrtSchrittAus E_3.einrichtung 0 A s3_0 s3_0 wGebenPlan
    ⟨[], []⟩ s3_1 := by
  have hF : FuehrtAus E_3.einrichtung 0 A s3_0 s3_0 (.sperre () .geben)
      [] [] { s3_0 with sperren := Function.update s3_0.sperren () ⟨some A, [B]⟩ } :=
    .sperre (SperrSchritt.geben s3_0_gibt) (fun _ => trivial)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, [], _,
    hF, Speicherfolge.nil _, rfl⟩

theorem ausfuehr_geben_1 : FuehrtSchrittAus E_3.einrichtung 2 A s3_1 s3_1 wGebenPlan
    ⟨g3_es, []⟩ s3_2 := by
  have hF : FuehrtAus E_3.einrichtung 2 A s3_1 s3_1 (.sperre () .geben)
      [⟨.rmw, (E_3.einrichtung.sperrOrt ()), .ra, (), ()⟩] []
      { s3_1 with sperren := Function.update s3_1.sperren () ⟨some B, []⟩ } :=
    .sperre (SperrSchritt.geben s3_1_gibt) (fun _ => trivial)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _, _, hF, g3_mem, rfl⟩

theorem ausfuehr_geben_2 : FuehrtSchrittAus E_3.einrichtung 3 B s3_2 s3_2 wGebenPlan
    ⟨g4_es, []⟩ s3_3 := by
  have hF : FuehrtAus E_3.einrichtung 3 B s3_2 s3_2 (.sperre () .geben)
      [⟨.schreiben, (E_3.einrichtung.sperrOrt ()), .ra, (), ()⟩] []
      { s3_2 with sperren := Function.update s3_2.sperren () ⟨none, []⟩ } :=
    .sperre (SperrSchritt.geben s3_2_gibt) (fun _ => trivial)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ h => (List.not_mem_nil h).elim, _, _, hF, g4_mem, rfl⟩

noncomputable def spur3 : Nat → Option (SchrittWahl Unit × SchrittSpur Unit Unit)
  | 0 => some (.kontext A (), ⟨[], []⟩)
  | 1 => spurw 1
  | 2 => some (.kontext A (), ⟨g3_es, []⟩)
  | 3 => some (.kontext B (), ⟨g4_es, []⟩)
  | t + 4 => spurw (t + 4)

theorem spur3_spurw (t : Nat) : spur3 (t + 4) = spurw (t + 4) := by
  rfl

def takt3 : ∀ t, Takt (Lauffolge E_3 hw2) (KeinSchritt (Lauffolge E_3 hw2))
    t (some (z3 t)) (spur3 t) (some (z3 (t + 1)))
  | 0 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 0)
      ⟨0, hw2_opp0 rfl, s3_0_kerne0, s3_0_live A⟩
      (e3_impl_geben s3_0_gibt) ausfuehr_geben_0))
  | 1 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 1)
      ⟨1, hw2_opp1 (by decide : (1 : Nat) % 2 = 1), s3_0_kerne1, s3_0_live B⟩
      ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
      (e1StotterAusfuehr 1 B s3_1)))
  | 2 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 2)
      ⟨0, hw2_opp0 (by decide : (2 : Nat) % 2 = 0), s3_0_kerne0, s3_0_live A⟩
      (e3_impl_geben s3_1_gibt) ausfuehr_geben_1))
  | 3 =>
    .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash 3)
      ⟨1, hw2_opp1 (by decide : (3 : Nat) % 2 = 1), s3_0_kerne1, s3_0_live B⟩
      (e3_impl_geben s3_2_gibt) ausfuehr_geben_2))
  | t + 4 => by
      rw [spur3_spurw, z3_ge4]
      rw [show z3 (t + 5) = s3_3 by simpa [Nat.add_assoc] using z3_ge4 (t + 1)]
      by_cases hpar : (t + 4) % 2 = 0
      · have hpar' : (t + 2 + 2) % 2 = 0 := by omega
        have hsp : spurw (t + 4) = some ticketA := by
          rw [show t + 4 = (t + 2) + 2 by omega]
          exact spurw_ge2 (t + 2) hpar'
        rw [hsp]
        exact .schritt rfl (.schritt (ImplSchritt.kontext (hw2_crash (t + 4))
          ⟨0, hw2_opp0 hpar, s3_0_kerne0, s3_0_live A⟩
          ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
          (e1StotterAusfuehr (t + 4) A s3_3)))
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
          ⟨1, hw2_opp1 h1, s3_0_kerne1, s3_0_live B⟩
          ⟨(), rfl, Or.inr ⟨rfl, rfl⟩⟩
          (e1StotterAusfuehr (t + 4) B s3_3)))

noncomputable def ρ_3 : Maschine.Lauf E_3 :=
  ⟨s2_start, hw2, ⟨fun t => some (z3 t), spur3, takt3⟩⟩

theorem ρ_3_zustand (t : Nat) (s : Zustand Unit Unit Unit Unit Bool Unit)
    (hzs : ρ_3.zeit.zustand t = some s) : z3 t = s := by
  have hzt : ρ_3.zeit.zustand t = some (z3 t) := rfl
  exact Option.some.inj (hzt.symm.trans hzs)

theorem e3_lauf : Laeufe E_3 h2 ρ_3 :=
  ⟨fair2.hardware, fair2.konform, zul_2, rfl⟩

theorem spur3_kein_absturz (t : Nat) : spur3 t ≠ some (.absturz, absturzSpur) := by
  intro hcon
  cases t with
  | zero =>
    rw [show spur3 0 = some (.kontext A (), ⟨[], []⟩) by rfl] at hcon
    have hfst := congrArg Prod.fst (Option.some.inj hcon)
    cases hfst
  | succ t =>
    cases t with
    | zero =>
      rw [show spur3 1 = spurw 1 by rfl, spurw1] at hcon
      simp only [ticketB] at hcon
      have hfst := congrArg Prod.fst (Option.some.inj hcon)
      cases hfst
    | succ t =>
      cases t with
      | zero =>
        rw [show spur3 2 = some (.kontext A (), ⟨g3_es, []⟩) by rfl] at hcon
        have hfst := congrArg Prod.fst (Option.some.inj hcon)
        cases hfst
      | succ t =>
        cases t with
        | zero =>
          rw [show spur3 3 = some (.kontext B (), ⟨g4_es, []⟩) by rfl] at hcon
          have hfst := congrArg Prod.fst (Option.some.inj hcon)
          cases hfst
        | succ t =>
          rw [spur3_spurw] at hcon
          exact spurw_kein_absturz _ hcon

theorem z3_nodup : (s3_0.sperren ()).schlange.Nodup := by
  rw [s3_0_lock]
  exact w_nodup

theorem e3_halte : HalteSchranken E_3 ρ_3 := by
  intro l c a n hcont
  cases l
  intro H' hH
  have hH5 : H' = 5 := Option.some.inj (hH.symm.trans e3halten)
  subst hH5
  by_cases hn0 : n = 0
  · subst n
    have hkk : Kontextkosten ρ_3 c a 0 = 0 := rfl
    omega
  · have hlt : a < a + n := by omega
    obtain ⟨s, hzs, hown⟩ := hcont a (Nat.le_refl _) hlt
    have hz3 := ρ_3_zustand a s hzs
    have hownA := z3_besitzer a s hz3
    by_cases haA : a = 0 ∨ a = 1 ∨ a = 2
    · rw [if_pos haA] at hownA
      have hcA : c = A := Option.some.inj (hown.symm.trans hownA)
      subst hcA
      have hn3 : n ≤ 3 := by
        by_contra hcontra
        have hn4 : 4 ≤ n := by omega
        have hlt3 : a + 3 < a + n := by omega
        obtain ⟨s', hzs', hown'⟩ := hcont (a + 3) (by omega) hlt3
        have hz3' := ρ_3_zustand (a + 3) s' hzs'
        have hb' := z3_besitzer (a + 3) s' hz3'
        rcases haA with ha | ha | ha <;> subst a
        · simp at hb'
          rw [hb'] at hown'
          cases hown'
        · simp at hb'
          rw [hb'] at hown'
          cases hown'
        · simp at hb'
          rw [hb'] at hown'
          cases hown'
      have hcost : Kontextkosten ρ_3 A a n ≤ n := zaehle_le _ _ _
      omega
    · by_cases ha3 : a = 3
      · subst ha3
        rw [if_neg haA, if_pos rfl] at hownA
        have hcB : c = B := Option.some.inj (hown.symm.trans hownA)
        subst hcB
        have hn1 : n ≤ 1 := by
          by_contra hcontra
          have hn2 : 2 ≤ n := by omega
          have hlt1 : 4 < 3 + n := by omega
          obtain ⟨s', hzs', hown'⟩ := hcont 4 (by omega) hlt1
          have hz3' := ρ_3_zustand 4 s' hzs'
          have hb' := z3_besitzer 4 s' hz3'
          simp at hb'
          rw [hb'] at hown'
          cases hown'
        have hcost : Kontextkosten ρ_3 B 3 n ≤ n := zaehle_le _ _ _
        omega
      · rw [if_neg haA, if_neg ha3] at hownA
        rw [hownA] at hown
        cases hown

theorem starkeWarteLauf_erfuellbar : StarkeWarteLaufAussage := by
  refine ⟨E_3, h2, ρ_3, B, 5, 0, ?_, e3_lauf, fair2, e3_halte, e3halten, ?_, ?_, ?_, ?_⟩
  · exact akzeptiert_E_3
  · refine ⟨s3_0, ?_, ?_, ?_⟩
    · rfl
    · exact ⟨A, by rw [s3_0_lock], w_AB_ne⟩
    · rw [s3_0_lock]
      rfl
  · intro s hzs
    have hz := ρ_3_zustand 0 s hzs
    rw [← hz]
    exact z3_nodup
  · intro k _
    exact spur3_kein_absturz k
  · intro h' b s hb hzs hown
    have hz := ρ_3_zustand b s hzs
    have hbown := z3_besitzer b s hz
    by_cases hb0 : b = 0
    · subst hb0
      rw [if_pos (Or.inl rfl)] at hbown
      have hh : h' = A := Option.some.inj (hown.symm.trans hbown)
      subst hh
      refine ⟨0, le_rfl, ?_, ?_⟩
      · exact ⟨s3_0, s3_1, rfl, rfl, s3_0_gibt⟩
      · exact Nat.le_trans (zaehle_le _ _ _) (by omega)
    · by_cases hb1 : b = 1
      · subst hb1
        rw [if_pos (Or.inr (Or.inl rfl))] at hbown
        have hh : h' = A := Option.some.inj (hown.symm.trans hbown)
        subst hh
        refine ⟨2, by decide, ?_, ?_⟩
        · exact ⟨s3_1, s3_2, rfl, rfl, s3_1_gibt⟩
        · exact Nat.le_trans (zaehle_le _ _ _) (by omega)
      · by_cases hb2 : b = 2
        · subst hb2
          rw [if_pos (Or.inr (Or.inr rfl))] at hbown
          have hh : h' = A := Option.some.inj (hown.symm.trans hbown)
          subst hh
          refine ⟨2, le_rfl, ?_, ?_⟩
          · exact ⟨s3_1, s3_2, rfl, rfl, s3_1_gibt⟩
          · exact Nat.le_trans (zaehle_le _ _ _) (by omega)
        · by_cases hb3 : b = 3
          · subst hb3
            rw [if_neg (by decide : ¬ ((3 : Nat) = 0 ∨ (3 : Nat) = 1 ∨ (3 : Nat) = 2)), if_pos rfl] at hbown
            have hh : h' = B := Option.some.inj (hown.symm.trans hbown)
            subst hh
            refine ⟨3, le_rfl, ?_, ?_⟩
            · exact ⟨s3_2, s3_3, rfl, rfl, s3_2_gibt⟩
            · exact Nat.le_trans (zaehle_le _ _ _) (by omega)
          · rw [if_neg (fun h => h.elim hb0 (fun h => h.elim hb1 hb2)), if_neg hb3] at hbown
            rw [hbown] at hown
            cases hown

end Gabbro.Core.Fortschritt
