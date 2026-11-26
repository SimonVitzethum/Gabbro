/-
  File:      Core/Fortschritt/Beweise/SperrStarkHalter.lean
  Subject:   GLOBAL HOLDER ELIGIBILITY for the non-vacuous hand-over unit (M8 2b).

  The invariant says: the lock only ever contains statically dispatched contexts; before a
  restart every vector is masked, an NMI is active and A, B, C stay live and dispatched; after a
  restart none of A, B, C is dispatched and the lock is empty. Therefore every reachable holder
  is live, dispatched and release-offering, on EVERY ideal cut, not only on the witness run.
-/
module

public import Core.Fortschritt.Beweise.SperrStarkEinheit4

@[expose] public section

namespace Gabbro.Core.Fortschritt

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung

/-- The lock only ever mentions statically dispatched contexts. -/
def lockStatisch4 (z : SperrZustand) : Prop :=
  (∀ h, z.besitzer = some h → statisch4 h) ∧
  ∀ c ∈ z.schlange, statisch4 c

/-- Before a restart: no preemption and all three contexts live and dispatched. -/
def vorCrash4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (∀ k, (s.kerne k).nmiAktiv = true ∧ (s.kerne k).maske = fun _ => true) ∧
  ∀ c, statisch4 c → s.status c = .laeuft ∧ ∃ k, (s.kerne k).laeuft = some c

/-- A restart empties the lock and leaves no static context on a core. -/
def nachCrash4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (∀ c, statisch4 c → ∀ k, (s.kerne k).laeuft ≠ some c) ∧
  (s.sperren ()) = .frei

def inv4 (s : Zustand Unit Unit Unit Unit Bool Unit) : Prop :=
  (lockStatisch4 (s.sperren ()) ∧ vorCrash4 s) ∨ nachCrash4 s

theorem lockStatisch4_schritt {a c z next}
    (h : SperrSchritt a c z next) (hc : statisch4 c) (hz : lockStatisch4 z) :
    lockStatisch4 next := by
  cases h with
  | ticket =>
    refine ⟨hz.1, fun d hd => ?_⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact hz.2 d hd
    · obtain rfl := List.mem_singleton.mp hd
      exact hc
  | nehmen hn =>
    cases hn with
    | frei c r =>
      exact ⟨fun d hd => (Option.some.inj hd) ▸ hc,
        fun d hd => hz.2 d (List.mem_cons_of_mem _ hd)⟩
  | geben hg =>
    cases hg with
    | besitzer c r =>
      cases r with
      | nil => exact ⟨(fun _ h => nomatch h), fun _ h => (List.not_mem_nil h).elim⟩
      | cons d r =>
        exact ⟨fun h he => hz.2 h (List.mem_cons.mpr (Or.inl (Option.some.inj he).symm)),
          fun h hm => hz.2 h (List.mem_cons_of_mem _ hm)⟩

theorem e4_inv_start : inv4 s4_ideal0 := by
  refine Or.inl ⟨⟨(fun _ h => nomatch h), fun _ h => (List.not_mem_nil h).elim⟩,
    fun k => ⟨s4_ideal0_nmi k, s4_ideal0_maske k⟩, ?_⟩
  intro c hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨s4_ideal0_live _, 0, s4_ideal0_kerne0⟩
  · exact ⟨s4_ideal0_live _, 1, s4_ideal0_kerne1⟩
  · exact ⟨s4_ideal0_live _, 2, s4_ideal0_kerne2⟩

theorem e4_inv_frame {s s' : Zustand Unit Unit Unit Unit Bool Unit}
    (hi : inv4 s) (hk : s'.kerne = s.kerne) (hs : s'.status = s.status)
    (hl : s'.sperren () = s.sperren ()) : inv4 s' := by
  simpa only [inv4, vorCrash4, nachCrash4, hk, hs, hl] using hi

theorem e4_inv_lock {s s' : Zustand Unit Unit Unit Unit Bool Unit} {a c}
    (hi : inv4 s) (hr : ∃ k, (s.kerne k).laeuft = some c)
    (h : SperrSchritt a c (s.sperren ()) (s'.sperren ()))
    (hc : statisch4 c ∨ a = .geben) (hk : s'.kerne = s.kerne) (hs : s'.status = s.status) :
    inv4 s' := by
  rcases hi with ⟨hz, hv⟩ | ⟨hd, hf⟩
  · have hstatic : statisch4 c := by
      rcases hc with hc | rfl
      · exact hc
      · cases h with
        | geben hg => exact hz.1 c hg.besitzt
    exact Or.inl ⟨lockStatisch4_schritt h hstatic hz, by
      simpa only [vorCrash4, hk, hs] using hv⟩
  · rcases hr with ⟨k, hrun⟩
    rcases hc with hc | rfl
    · exact (hd c hc k hrun).elim
    · rw [hf] at h
      cases h with
      | geben hg => cases hg

theorem e4_I_schritt_inv {hw : HwLauf} {t : Nat}
    {s : Zustand Unit Unit Unit Unit Bool Unit}
    {ev : SchrittWahl Unit × SchrittSpur Unit Unit} {s' : Zustand Unit Unit Unit Unit Bool Unit}
    (hi : inv4 s)
    (step : I.Schritt E_4.einrichtung E_4.system E_4.katalog hw t s ev s') :
    inv4 s' := by
  cases step with
  | @kontext _ u plan spur c w _ ready hreg haus =>
    obtain ⟨_, _, hreg⟩ := hreg
    change e4Regel c s w [plan] u at hreg
    obtain ⟨k, _, hrun, _⟩ := ready
    rcases hreg with ⟨hc, ⟨_, _, hp, hu⟩ | ⟨_, _, hp, hu⟩⟩ |
      ⟨_, _, hp, hu⟩ | ⟨hp, hu⟩
    all_goals
      subst u
      obtain rfl := (List.cons.inj hp).1
      obtain ⟨_, _, _, _, hF, _, hziel⟩ := haus
      simp only [ticketPlan, nehmenPlan, wGebenPlan, stutterPlan] at hF
      generalize hev : spur.aussen = evs at hF
      cases hF
      first
      | apply e4_inv_frame hi <;> rw [hziel] <;> rfl
      | have hh : s'.kerne = s.kerne := by rw [hziel] <;> rfl
        have hs : s'.status = s.status := by rw [hziel] <;> rfl
        have hhlock (a : SperrAktion) (ha : statisch4 c ∨ a = .geben)
            (hstep : SperrSchritt a c (s.sperren ()) (s'.sperren ())) : inv4 s' :=
          e4_inv_lock hi ⟨k, hrun⟩ hstep ha hh hs
        first
        | apply hhlock .ticket (Or.inl hc)
          rw [hziel]
          simp only [Function.update_self]
          assumption
        | apply hhlock .nehmen (Or.inl hc)
          rw [hziel]
          simp only [Function.update_self]
          assumption
        | apply hhlock .geben (Or.inr rfl)
          rw [hziel]
          simp only [Function.update_self]
          assumption
  | antwort _ h =>
    obtain ⟨_, _, _, heq⟩ := h
    apply e4_inv_frame hi <;> rw [heq] <;> rfl
  | interrupt _ h =>
    obtain ⟨k, irq, c, nmi, _, _, henter, _, _, _, heq⟩ := h
    rcases hi with ⟨_, hv⟩ | ⟨hd, hf⟩
    · obtain ⟨hn, hm⟩ := hv.1 k
      cases henter with
      | handler mask _ =>
        exfalso
        have hm' := mask.1
        rw [hm] at hm'
        cases hm'
      | nmi enabled _ =>
        change (s.kerne k).nmiAktiv = false at enabled
        rw [hn] at enabled
        cases enabled
    · refine Or.inr ⟨?_, by rw [heq]; exact hf⟩
      intro d hc j
      rw [heq]
      change (Function.update s.kerne k ((s.kerne k).unterbrechen c nmi) j).laeuft ≠ some d
      by_cases hj : j = k
      · subst j
        rw [Function.update_self]
        intro he
        have hcd : c = d := Option.some.inj he
        rcases hc with rfl | rfl | rfl <;> cases henter <;> cases hcd
      · rw [Function.update_of_ne hj]
        exact hd d hc j
  | absturz h =>
    rw [h.genau.2]
    refine Or.inr ⟨?_, rfl⟩
    intro c hc k
    change (if k = 0 then some eintritt4 else none) ≠ some c
    split
    · intro he
      exact eintritt4_nicht_statisch4 ((Option.some.inj he).symm ▸ hc)
    · intro he
      cases he

theorem e4_inv_I (ρ : I.Lauf E_4) (lauf : I.Laeufe E_4 ρ) (t : Nat) :
    inv4 (ρ.zeit.zustand t) := by
  induction t with
  | zero =>
    rw [lauf.2.2.2.1]
    exact e4_inv_start
  | succ t ih =>
    cases ρ.zeit.takt t with
    | wartet _ heq _ => rwa [heq]
    | schritt _ step => exact e4_I_schritt_inv ih step

theorem e4_halter : SperrHalterHalten E_4 := by
  intro ρ lauf t l h hown _
  cases l
  rcases e4_inv_I ρ lauf t.val with ⟨hz, hv⟩ | ⟨_, hf⟩
  · let s := ρ.zeit.zustand t.val
    obtain ⟨hl, hd⟩ := hv.2 h (hz.1 h hown)
    change (s.sperren ()).besitzer = some h at hown
    have hg : (s.sperren ()).Gibt h ((s.sperren ()).abgeben) := by
      cases hs : s.sperren () with
      | mk own queue =>
        rw [hs] at hown
        change own = some h at hown
        subst own
        exact .besitzer h queue
    refine ⟨hl, hd, (), wGebenPlan, s, ⟨(), rfl, ?_⟩, rfl, fun _ _ _ => trivial⟩
    exact Or.inr (Or.inl ⟨_, .geben hg, rfl, rfl⟩)
  · rw [hf] at hown
    cases hown

theorem waechter_E_4 : WaechterHalten E_4 :=
  ⟨fun ρ _ t op args h => by
      dsimp [kanonischeVerwendung, E_4, Quelltabellen.leer] at h
      exact h.elim,
    fun ρ _ t hC => by
      obtain ⟨C, hC⟩ := hC
      obtain ⟨c, hc⟩ := hC.1
      obtain ⟨b, hblock, _, _, _⟩ := hC.2 c hc
      exact hblock,
    e4_halter⟩

theorem akzeptiert_E_4 : Akzeptiert E_4 :=
  ⟨⟨Plattform.x86_64.katalog_wohlgeformt, e4_regel_lokal,
     ⟨Gabbro.Core.Aussen.zulassung_m2 _, e4_aussen_gueltig⟩, e4_fluss,
     e4_schranken_lokal, e4_sec, e4_domaenen⟩, e4_klauseln, waechter_E_4⟩

theorem e4_sperrSpeicher {g : SpeicherGraph Unit Unit} (hk : g.graph.Konsistent)
    (hv : g.graph.Vollstaendig) (c : Kontext) (a : Speicher.Art) :
    ∃ es g', Speicherfolge (fun _ => ()) (.kontext c) g [⟨a, (), .ra, (), ()⟩] es g' := by
  obtain ⟨r, es, g', hf⟩ := speicherzug_existiert (fun _ => ()) (.kontext c)
    hk hv a () .ra () (fun _ => by decide)
  cases r
  exact ⟨es, g', hf⟩

theorem e4_sperrAus {t c s u next} {a : SperrAktion}
    {p : SchrittPlan Unit Unit Unit Unit} {es g}
    (hp : p.aktion = .sperre () a) (hr : p.lesen = []) (hw : p.fuss = [])
    (hf : Zustandsrahmen s u) (hs : SperrSchritt a c (s.sperren ()) next)
    (hm : Speicherfolge s.initial (.kontext c) s.graph
      (sperrEreignisse (s.sperren ()) next () (s.initial ())) es g) :
    FuehrtSchrittAus E_4.einrichtung t c s u p ⟨es, []⟩
      { u with sperren := Function.update s.sperren () next, graph := g } := by
  refine ⟨hf, ?_, _, _, ?_, ?_, rfl⟩
  · rw [hr]
    exact fun _ h => (List.not_mem_nil h).elim
  · rw [hp]
    exact .sperre hs (fun _ => trivial)
  · simpa only [hr, hw, schreibEreignisse, List.filter_nil, List.map_nil, List.append_nil]
      using hm

theorem e4_frame (s : Zustand Unit Unit Unit Unit Bool Unit) :
    Zustandsrahmen s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The ideal run has a real owner and executes its release from the canonical empty lock. -/
theorem e4_ideal_halter_erfuellbar :
    ∃ ρ : I.Lauf E_4, I.Laeufe E_4 ρ ∧
      ((ρ.zeit.zustand 2).sperren ()).besitzer = some A ∧
      ((ρ.zeit.zustand 2).sperren ()).Gibt A ((ρ.zeit.zustand 3).sperren ()) ∧
      ∃ sp, ρ.zeit.spur 2 = some (.kontext A (), sp) ∧
        FuehrtSchrittAus E_4.einrichtung 2 A (ρ.zeit.zustand 2) (ρ.zeit.zustand 2)
          wGebenPlan sp (ρ.zeit.zustand 3) := by
  have fair := Umgebung.referenz_fair Plattform.x86_64.katalog 1 sicht0
    Plattform.x86_64.katalog_wohlgeformt (by decide)
  obtain ⟨start, hstart⟩ := zulStart_erfuellbar fair.hardware wBild_gueltig
  let i0 := (I.start E_4 start).2
  have hgraph : i0.graph.graph.Konsistent ∧ i0.graph.graph.Vollstaendig :=
    ⟨Speicher.Zustand.leer_konsistent, Speicher.Zustand.leer_vollstaendig⟩
  let i1 := { toggleUpdate A i0 with sperren := Function.update i0.sperren () ⟨none, [A]⟩ }
  obtain ⟨es2, g2, hg2⟩ := e4_sperrSpeicher hgraph.1 hgraph.2 A .rmw
  have hgood := hg2.viele.gut hgraph.1 hgraph.2
  let i2 := { i1 with sperren := Function.update i1.sperren () ⟨some A, []⟩, graph := g2 }
  obtain ⟨es3, g3, hg3⟩ := e4_sperrSpeicher hgood.1 hgood.2 A .schreiben
  let i3 := { i2 with sperren := Function.update i2.sperren () .frei, graph := g3 }
  have ht : SperrSchritt .ticket A (i0.sperren ()) ⟨none, [A]⟩ :=
    .ticket (fun h => nomatch h) List.not_mem_nil
  have hn : (i1.sperren ()).Nimmt A ⟨some A, []⟩ := .frei A []
  have hg : (i2.sperren ()).Gibt A (i3.sperren ()) := .besitzer A []
  have htAus : FuehrtSchrittAus E_4.einrichtung 0 A i0 (toggleUpdate A i0)
      ticketPlan ⟨[], []⟩ i1 :=
    e4_sperrAus rfl rfl rfl (e4_frame i0) ht (.nil _)
  have hnAus : FuehrtSchrittAus E_4.einrichtung 1 A i1 i1 nehmenPlan ⟨es2, []⟩ i2 :=
    e4_sperrAus rfl rfl rfl (e4_frame i1) (.nehmen hn) hg2
  have hgAus : FuehrtSchrittAus E_4.einrichtung 2 A i2 i2 wGebenPlan ⟨es3, []⟩ i3 :=
    e4_sperrAus rfl rfl rfl (e4_frame i2) (.geben hg) hg3
  let z : Nat → Zustand Unit Unit Unit Unit Bool Unit
    | 0 => i0
    | 1 => i1
    | 2 => i2
    | _ + 3 => i3
  let trace : Nat → SchrittWahl Unit × SchrittSpur Unit Unit
    | 1 => (.kontext A (), ⟨es2, []⟩)
    | 2 => (.kontext A (), ⟨es3, []⟩)
    | _ => (.kontext A (), ⟨[], []⟩)
  have ticks (t : Nat) : I.Schritt E_4.einrichtung E_4.system E_4.katalog hw1
      t (z t) (trace t) (z (t + 1)) := by
    match t with
    | 0 => exact .kontext (hw1_crash 0) ⟨0, hw1_opp0 0, rfl, rfl⟩
        (e4_impl_ticket statisch4_A ht) htAus
    | 1 => exact .kontext (hw1_crash 1) ⟨0, hw1_opp0 1, rfl, rfl⟩
        (e4_impl_nehmen statisch4_A (.nehmen hn)) hnAus
    | 2 => exact .kontext (hw1_crash 2) ⟨0, hw1_opp0 2, rfl, rfl⟩
        (e4_impl_geben hg) hgAus
    | t + 3 => exact .kontext (hw1_crash _) ⟨0, hw1_opp0 _, rfl, rfl⟩
        ⟨(), rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
        ⟨e4_frame i3, fun _ h => (List.not_mem_nil h).elim, [], i3, .intern, .nil _, rfl⟩
  let ρ : I.Lauf E_4 := ⟨start, h1, hw1, ⟨z, fun t => some (trace t),
    fun t => .schritt rfl (ticks t)⟩, fun _ => none⟩
  refine ⟨ρ, ⟨fair.hardware, fair.konform, hstart, rfl, ⟨?_, ?_⟩, ?_⟩,
    rfl, hg, ⟨_, rfl, hgAus⟩⟩
  · intro t ht _
    cases ht
  · exact fun _ => ⟨0, fun _ _ => rfl⟩
  · intro t c h
    cases h

end Gabbro.Core.Fortschritt
