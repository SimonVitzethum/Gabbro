/-
  File:      core/Core/Speicher/DRFSC.lean
  Subject:   THE DRF-SC THEOREM of the memory model W (PERFECT-MODEL §8, step M3), WITH fences:
              an RC11-consistent execution whose atomic accesses are all `seq_cst` and which has
              no data race is sequentially consistent (`drf_sc`), as in Lahav et al., PLDI 2017, §8.

  THE ARGUMENT WITH FENCES. With only `seq_cst` atomics every `sw` endpoint is `seq_cst`: the
  release side is a strong write or a strong (hence `seq_cst`) release fence, the acquire side a
  strong read or a strong acquire fence. A fence-free `sw` is the classic same-location shape; a
  fence on one side is a `psc` step through `pscBasis` (`[F sc]; hb?; scb; [E sc]` or the mirror),
  and fences on both sides form a `pscZaun` step. So `sw` between events that are already `seq_cst`
  is always a `psc` step, and an `hb` path from a `seq_cst` event to a `seq_cst` event is a `psc` path.

  Two orders then cover every edge of `po ∪ rf ∪ mo ∪ rb`:
  * `hb` -- every `po` edge; every edge touching a plain access, because race freedom orders such a
    conflicting pair by `hb` and coherence fixes the direction; and every `rf` edge between two
    `seq_cst` accesses, which is a classic `sw` and hence `psc`;
  * `psc⁺` -- every `mo`/`rb` edge between two `seq_cst` accesses (they are in `scb`).
  A cycle folds into a cycle of `hb` or of `psc⁺` (`Kette`), both excluded by consistency.
-/
module

public import Core.Speicher.Konsistent

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E Ort Wert : Type} {G : Graph E Ort Wert}

theorem sc_stark {a : E} (h : G.sc a) : (G.modus a).stark := by
  unfold sc at h
  rw [h]
  exact trivial

/-- With only `seq_cst` atomics, an access of at least release/acquire strength is `seq_cst`. -/
theorem NurSC.sc_von_stark (hn : G.NurSC) {a : E} (h : (G.modus a).stark) : G.sc a := by
  cases hn a with
  | inl hna =>
    unfold na at hna
    rw [hna] at h
    exact False.elim h
  | inr hsc => exact hsc

/-- With only `seq_cst` atomics, an atomic access is `seq_cst`. -/
theorem NurSC.sc_von_atomar (hn : G.NurSC) {a : E} (h : (G.modus a).atomar) : G.sc a := by
  cases hn a with
  | inl hna =>
    unfold na at hna
    rw [hna] at h
    exact False.elim h
  | inr hsc => exact hsc

/-- A synchronising fence is `seq_cst` when all atomic accesses are. -/
theorem syncZaun_sc (hn : G.NurSC) {a : E} (h : G.istSyncZaun a) : G.sc a :=
  hn.sc_von_stark h.2

theorem istSCZaun_von_sync (hn : G.NurSC) {a : E} (h : G.istSyncZaun a) : G.istSCZaun a :=
  ⟨h.1, syncZaun_sc hn h⟩

/-- An update reads. -/
theorem istRmw_liest {a : E} (h : G.istRmw a) : G.liest a := by
  unfold istRmw at h
  unfold liest
  rw [h]
  exact trivial

/-- The tail of a release sequence is atomic (the head need not be: the `po` clause carries no
    strength requirement). -/
theorem Rs.atomar_rechts (hwf : G.Wohlgeformt) {w x : E} (h : G.Rs w x) :
    (G.modus x).atomar := by
  induction h with
  | selbst _ ha => exact ha
  | po _ _ _ _ ha => exact ha
  | rmw _ _ hu _ => exact hwf.rmw_atomar hu

/-- An update reading from an atomic write synchronises with that write (the classic shape). -/
theorem sw_von_rmw (hk : G.Konsistent) (hn : G.NurSC) {x u : E}
    (hxatom : (G.modus x).atomar) (hrf : G.rf x u) (hu : G.istRmw u) : G.sw x u := by
  have hxstark : (G.modus x).stark := sc_stark (hn.sc_von_atomar hxatom)
  have hustark : (G.modus u).stark := sc_stark (hn.sc_von_atomar (hk.wf.rmw_atomar hu))
  exact sw_von_klassisch
    ⟨hk.wf.rf_schreibt _ _ hrf, hxstark, istRmw_liest hu, hustark, x,
    .selbst (hk.wf.rf_schreibt _ _ hrf) hxatom, hrf⟩

/-- A release sequence stays at its head and advances by `po` or by a synchronising update. -/
theorem Rs.hbOderGleich (hk : G.Konsistent) (hn : G.NurSC) {w x : E} (h : G.Rs w x) :
    w = x ∨ G.hb w x := by
  induction h with
  | selbst _ _ => exact Or.inl rfl
  | po _ hpo _ _ _ => exact Or.inr (G.hb_von_po hpo)
  | rmw hRs hrf hu ih =>
    have hsw := sw_von_rmw hk hn (Rs.atomar_rechts hk.wf hRs) hrf hu
    rcases ih with rfl | hbwx
    · exact Or.inr (G.hb_von_sw hsw)
    · exact Or.inr (G.hb_trans hbwx (G.hb_von_sw hsw))

/-- The middle `rs ; rf` of a synchronisation is a same-location `hb` step. The release head need
    not be strong (a release fence supplies the strength), so the step starts at the release
    sequence's strong tail; the location equality comes from `Rs.ort_gleich` and `rf_ort`. -/
theorem sw_hb_mitte (hk : G.Konsistent) (hn : G.NurSC) {w x r : E}
    (hrs : G.Rs w x) (hrf : G.rf x r) (hratom : (G.modus r).atomar) :
    G.hb w r ∧ G.ort w = G.ort r := by
  have hxstark : (G.modus x).stark := sc_stark (hn.sc_von_atomar (Rs.atomar_rechts hk.wf hrs))
  have hrstark : (G.modus r).stark := sc_stark (hn.sc_von_atomar hratom)
  have hsw : G.sw x r := sw_von_klassisch
    ⟨hk.wf.rf_schreibt _ _ hrf, hxstark, hk.wf.rf_liest _ _ hrf, hrstark, x,
    .selbst (hk.wf.rf_schreibt _ _ hrf) (Rs.atomar_rechts hk.wf hrs), hrf⟩
  have hbxr : G.hb x r := G.hb_von_sw hsw
  have hbwr : G.hb w r := by
    rcases Rs.hbOderGleich hk hn hrs with rfl | hbwx
    · exact hbxr
    · exact G.hb_trans hbwx hbxr
  exact ⟨hbwr, sw_klassisch_ort hk.wf hrs hrf⟩

/-- **Every synchronisation between `seq_cst` endpoints is a `psc` step**, with or without fences.
    A classic `sw` is `hb|loc`; one fence side goes through `pscBasis`; two fence sides through
    `pscZaun`. Under `NurSC` all four shapes have `seq_cst` endpoints. -/
theorem sw_psc (hk : G.Konsistent) (hn : G.NurSC) {a b : E} (h : G.sw a b) : G.psc a b := by
  obtain ⟨w, x, r, hkopf, hrs, hrf, hratom, _, hschwanz⟩ := h
  have hm := sw_hb_mitte hk hn hrs hrf hratom
  have hscr : G.sc r := hn.sc_von_atomar hratom
  rcases hkopf with hkopf | hkopf
  · obtain ⟨rfl, _, hma⟩ := hkopf
    have hsca : G.sc a := hn.sc_von_stark hma
    rcases hschwanz with hschwanz | hschwanz
    · obtain ⟨rfl, _, _⟩ := hschwanz
      exact psc_von_klassisch ⟨hsca, hscr, Or.inr (Or.inr (Or.inl ⟨hm.1, hm.2⟩))⟩
    · obtain ⟨_, _, hporb, hzfb⟩ := hschwanz
      refine Or.inl ⟨a, r, Or.inr (Or.inr (Or.inl ⟨hm.1, hm.2⟩)), ?_, ?_⟩
      · exact Or.inl ⟨hsca, rfl⟩
      · exact Or.inr ⟨istSCZaun_von_sync hn hzfb, Or.inr (G.hb_von_po hporb)⟩
  · obtain ⟨hzfa, hpoaw, _⟩ := hkopf
    rcases hschwanz with hschwanz | hschwanz
    · obtain ⟨rfl, _, _⟩ := hschwanz
      refine Or.inl ⟨w, r, Or.inr (Or.inr (Or.inl ⟨hm.1, hm.2⟩)), ?_, ?_⟩
      · exact Or.inr ⟨istSCZaun_von_sync hn hzfa, Or.inr (G.hb_von_po hpoaw)⟩
      · exact Or.inl ⟨hscr, rfl⟩
    · obtain ⟨_, _, hporb, hzfb⟩ := hschwanz
      exact Or.inr ⟨istSCZaun_von_sync hn hzfa, istSCZaun_von_sync hn hzfb,
        Or.inl (G.hb_trans (G.hb_trans (G.hb_von_po hpoaw) hm.1) (G.hb_von_po hporb))⟩

/-- A `po` edge between two `seq_cst` events is a `psc` step. -/
theorem po_psc {a b : E} (ha : G.sc a) (hb : G.sc b) (h : G.po a b) : G.psc a b :=
  psc_von_klassisch ⟨ha, hb, Or.inl h⟩

theorem pfad_verlaengern {r : E → E → Prop} {a c e f : E} (h1 : c = a ∨ Relation.TransGen r a c)
    (h2 : c = e ∨ r c e) (h3 : r e f) : Relation.TransGen r a f := by
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact .single h3
  · exact .tail (.single h2) h3
  · exact .tail h1 h3
  · exact .tail (.tail h1 h2) h3

/-- **The shape of an `hb` path from a `seq_cst` event** (with fences): a `psc` path to a last
    `seq_cst` event `c`, then a `po` stretch (or nothing). A `sw` step always ends at a `seq_cst`
    event, so the stretch after the last `seq_cst` event contains only `po` steps. -/
theorem hb_zerlegung (hk : G.Konsistent) (hn : G.NurSC) {a e : E} (ha : G.sc a)
    (h : G.hb a e) :
    ∃ c, G.sc c ∧ (c = a ∨ Relation.TransGen G.psc a c) ∧ (c = e ∨ G.po c e) := by
  unfold Graph.hb at h
  induction h with
  | single h1 =>
    cases h1 with
    | inl hpo => exact ⟨a, ha, Or.inl rfl, Or.inr hpo⟩
    | inr hsw =>
      have hp := sw_psc hk hn hsw
      exact ⟨_, psc_sc_rechts hp, Or.inr (.single hp), Or.inl rfl⟩
  | @tail e f _ h2 ih =>
    obtain ⟨c, hc, hac, hce⟩ := ih
    cases h2 with
    | inl hpo =>
      refine ⟨c, hc, hac, Or.inr ?_⟩
      rcases hce with rfl | hce
      · exact hpo
      · exact hk.wf.po_trans _ _ _ hce hpo
    | inr hsw =>
      have hp := sw_psc hk hn hsw
      have hce' : c = e ∨ G.psc c e := by
        rcases hce with rfl | hce
        · exact Or.inl rfl
        · exact Or.inr (po_psc hc (psc_sc_links hp) hce)
      exact ⟨f, psc_sc_rechts hp, Or.inr (pfad_verlaengern hac hce' hp), Or.inl rfl⟩

/-- **Between `seq_cst` events `hb` is inside `psc⁺`** (only `seq_cst` atomics, with fences). -/
theorem hb_sc_psc (hk : G.Konsistent) (hn : G.NurSC) {a b : E} (ha : G.sc a)
    (hb : G.sc b) (h : G.hb a b) : Relation.TransGen G.psc a b := by
  obtain ⟨c, hc, hac, hcb⟩ := hb_zerlegung hk hn ha h
  rcases hcb with rfl | hcb
  · rcases hac with rfl | hac
    · exact absurd h (hk.hb_irrefl _)
    · exact hac
  · have hp := po_psc hc hb hcb
    rcases hac with rfl | hac
    · exact .single hp
    · exact .tail hac hp

/-- **Every edge of `po ∪ rf ∪ mo ∪ rb` is in `hb` or in `psc⁺`** (consistent, only `seq_cst`
    atomics, race-free, with fences). -/
theorem scSchritt_einbetten (hk : G.Konsistent) (hn : G.NurSC) (hr : G.Rennfrei)
    {a b : E} (h : G.scSchritt a b) : G.hb a b ∨ Relation.TransGen G.psc a b := by
  have wf := hk.wf
  rcases h with hpo | hrf | hmo | hrb
  · exact Or.inl (G.hb_von_po hpo)
  · have hne : a ≠ b := by
      intro e
      subst e
      exact hk.rf_irrefl a hrf
    have hkf : G.Konflikt a b := ⟨hne, wf.rf_ort _ _ hrf, Or.inl (wf.rf_schreibt _ _ hrf)⟩
    rcases hn a with ha | ha <;> rcases hn b with hb | hb
    · exact Or.inl (hk.hb_richtung (G.eco_von_rf hrf) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rf hrf) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rf hrf) (hr a b hkf (Or.inr hb)))
    · exact Or.inr (.single (sw_psc hk hn (sw_von_klassisch
        ⟨wf.rf_schreibt _ _ hrf, sc_stark ha, wf.rf_liest _ _ hrf, sc_stark hb, a,
        .selbst (wf.rf_schreibt _ _ hrf) (Modus.stark_atomar (sc_stark ha)), hrf⟩)))
  · have hne : a ≠ b := by
      intro e
      subst e
      exact wf.mo_irrefl a hmo
    have hkf : G.Konflikt a b := ⟨hne, wf.mo_ort _ _ hmo, Or.inl (wf.mo_schreibt _ _ hmo).1⟩
    rcases hn a with ha | ha <;> rcases hn b with hb | hb
    · exact Or.inl (hk.hb_richtung (G.eco_von_mo hmo) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_mo hmo) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_mo hmo) (hr a b hkf (Or.inr hb)))
    · exact Or.inr (.single (psc_von_klassisch ⟨ha, hb, Or.inr (Or.inr (Or.inr (Or.inl hmo)))⟩))
  · have hne : a ≠ b := by
      obtain ⟨_, _, _, h⟩ := hrb
      exact h
    have hkf : G.Konflikt a b := ⟨hne, rb_ort wf hrb, Or.inr (rb_schreibt wf hrb)⟩
    rcases hn a with ha | ha <;> rcases hn b with hb | hb
    · exact Or.inl (hk.hb_richtung (G.eco_von_rb hrb) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rb hrb) (hr a b hkf (Or.inl ha)))
    · exact Or.inl (hk.hb_richtung (G.eco_von_rb hrb) (hr a b hkf (Or.inr hb)))
    · exact Or.inr (.single (psc_von_klassisch ⟨ha, hb, Or.inr (Or.inr (Or.inr (Or.inr hrb)))⟩))

variable (G) in
/-- The folded order: `hb`, or `hb? ; psc⁺ ; hb?`. -/
def Kette (a b : E) : Prop :=
  G.hb a b ∨ ∃ c d, (c = a ∨ G.hb a c) ∧ Relation.TransGen G.psc c d ∧ (d = b ∨ G.hb d b)

theorem verbinde {x y b : E} (hx : x = b ∨ G.hb x b) (hy : y = b ∨ G.hb b y) :
    x = y ∨ G.hb x y := by
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact Or.inl rfl
  · exact Or.inr hy
  · exact Or.inr hx
  · exact Or.inr (G.hb_trans hx hy)

/-- Two `psc⁺` stretches joined by `hb?` form one (only `seq_cst` atomics, with fences). -/
theorem psc_kleben (hk : G.Konsistent) (hn : G.NurSC) {c d c' d' : E}
    (h1 : Relation.TransGen G.psc c d) (hm : d = c' ∨ G.hb d c')
    (h2 : Relation.TransGen G.psc c' d') : Relation.TransGen G.psc c d' := by
  rcases hm with rfl | hm
  · exact h1.trans h2
  · exact h1.trans ((hb_sc_psc hk hn (psc_pfad_sc h1).2 (psc_pfad_sc h2).1 hm).trans h2)

theorem Kette_trans (hk : G.Konsistent) (hn : G.NurSC) {a b e : E}
    (h1 : G.Kette a b) (h2 : G.Kette b e) : G.Kette a e := by
  rcases h1 with h1 | ⟨c, d, hc, hcd, hd⟩ <;> rcases h2 with h2 | ⟨c', d', hc', hcd', hd'⟩
  · exact Or.inl (G.hb_trans h1 h2)
  · refine Or.inr ⟨c', d', Or.inr ?_, hcd', hd'⟩
    rcases hc' with rfl | hc'
    · exact h1
    · exact G.hb_trans h1 hc'
  · refine Or.inr ⟨c, d, hc, hcd, Or.inr ?_⟩
    rcases hd with rfl | hd
    · exact h2
    · exact G.hb_trans hd h2
  · exact Or.inr ⟨c, d', hc, psc_kleben hk hn hcd (verbinde hd hc') hcd', hd'⟩

theorem Kette_irrefl (hk : G.Konsistent) (hn : G.NurSC) (a : E) :
    ¬ G.Kette a a := by
  rintro (h | ⟨c, d, hc, hcd, hd⟩)
  · exact hk.hb_irrefl a h
  · rcases verbinde hd hc with rfl | hdc
    · exact hk.psc _ hcd
    · exact hk.psc c (hcd.trans (hb_sc_psc hk hn (psc_pfad_sc hcd).2 (psc_pfad_sc hcd).1 hdc))

/-- **DRF-SC, with fences.** An RC11-consistent execution (with `po ∪ rf` acyclic) whose atomic
    accesses are all `seq_cst` and in which every conflicting pair with a plain access is ordered
    by happens-before is sequentially consistent: `po ∪ rf ∪ mo ∪ rb` is acyclic. Its reading as one
    interleaving on one memory is `sc_verschraenkung`. -/
theorem drf_sc (hk : G.Konsistent) (hn : G.NurSC) (hr : G.Rennfrei) :
    G.SCKonsistent := by
  intro a ha
  have hketten : Relation.TransGen G.Kette a a := by
    refine transGen_mono (fun x y hxy => ?_) ha
    rcases scSchritt_einbetten hk hn hr hxy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨x, y, Or.inl rfl, h, Or.inl rfl⟩
  exact Kette_irrefl hk hn a
    (transGen_von_trans (r := G.Kette) (fun _ _ _ h1 h2 => Kette_trans hk hn h1 h2) hketten)

end Graph

end Gabbro.Core.Speicher
