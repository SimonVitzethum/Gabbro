/-
  File:      Grammatik/Zielsatz/Eigenschaften/RwZeuge.lean
  Subject:   WITNESSES of the reader/writer lock layer (`RwSchritt.lean`, `RwRang.lean`): a
             kernel-checked run with TWO READERS and a WRITER on one lock, and the planted defect
             "a writer admitted while a reader holds".

  The fixture is the one of `KernMaskeZeuge.lean` (one lock `()`, functions `h` and `t` with the
  body `locks () { }; return`); thread 0 runs `h` and is the WRITER, threads 1, 2, 3 run `t` and are
  READERS (`lw t _ := t ≠ 0`).

  * `leser_schreiber_lauf` -- ONE kernel-checked run of twelve layer steps. Thread 1 takes the lock,
    thread 2 takes it SHARED (`RwAcq`) while thread 1 holds it: both hold at once. Machine G alone
    cannot step thread 2 there (`nicht_bereit_an_sperre`): the layer is what admits it. The writer
    (thread 0) then stands at the lock and has NO step in the layer (G refuses: another thread
    holds; the shared rule refuses: it is not a reader). Both readers leave, the writer takes the
    lock (a G step) and holds it alone, and a reader (thread 3) that arrives meanwhile is held
    back. The order through the lock is witnessed too (`sperre_ordnet_rw` at the reader-then-writer pair). `RwExkl` holds along the run (`rwExkl_lauf`, from the start).
  * PLANTED DEFECT (last conjunct): the shared-acquisition recipe WITHOUT its premises `leser` and
    `andere` -- the writer's own lock step in the blank machine, kept next to the others -- admits
    the writer next to both readers, and the exclusion invariant fails at the machine reached. So
    `andere` is what keeps a writer out; the model's exclusion is not a by-product of the fixture.
  * `leser_rekursiv_verweigert` -- PLANTED DEFECT (rank): a reader that takes the lock it already holds
    (a recursive read lock, the classic source of a reader/writer deadlock) is refused by the rank
    premise of `Stmt.locks`: `hr` is unprovable in a section that holds the lock. The typed syntax
    has no term for the violation, which is why the defect is the premise itself.
-/
import Grammatik.Zielsatz.Eigenschaften.KernMaskeZeuge
import Grammatik.Zielsatz.Eigenschaften.RwRang
import Grammatik.Zielsatz.Eigenschaften.RwInv

namespace Gabbro.Grammatik.Zielsatz.RwFix

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Zielsatz.KernMaskeFix

abbrev D0 := wD false
abbrev P0 := wP false
abbrev O0 := wO false
abbrev M00 := wM0 false

/-- Thread 0 takes locks exclusively; threads 1, 2, 3, ... are readers. -/
def lw : Lese D0 := fun t _ => t ≠ 0

theorem lw_pos {t : Faden} (h : t ≠ 0) : lw t () := h

theorem O0_gut : GutO O0 := fun a _ _ => nomatch a

theorem P0_stufen : StufenM P0 := by
  intro f
  cases f <;> rfl

theorem init_exklusiv : StartExklusiv (D := D0) (wInit false) := by
  intro t u _ L hL
  exact absurd hL (by cases t <;> exact List.not_mem_nil)

theorem init_leer : ∀ t, D0.haelt (wInit false t).1 = [] := by
  intro t
  cases t <;> rfl

theorem exkl0 : RwExkl lw M00 := rwExkl_start P0 (wSp false) (wInit false) init_exklusiv

/-- A step of the layer keeps every thread but the actor. -/
theorem fremd_w {M M' : RufMaschineG D0} {f : Faden} (h : RwSchritt P0 O0 0 lw M f M') {g : Faden}
    (hg : g ≠ f) : M'.faeden g = M.faeden g := rwSchritt_fremd h g hg

/-- **TWO READERS HOLD ONE LOCK, THE WRITER WAITS, THEN HOLDS IT ALONE.** One run of twelve layer steps:
    thread 1 takes the lock, thread 2 takes it SHARED, thread 0 (the writer) stands at the lock; both
    readers leave; the writer takes the lock; a reader (thread 3) that arrives is held back. The
    last conjunct is the planted defect: the shared-acquisition recipe WITHOUT its premises admits the
    writer at the machine of step 5, and exclusion fails there. -/
theorem leser_schreiber_lauf : ∃ (ms : Nat → RufMaschineG D0) (fs : Nat → Faden),
    RwLauf P0 O0 0 lw M00 ms fs 12 ∧
    -- machine G alone cannot admit the second reader ...
    (¬ ∃ M', RufSchrittG P0 O0 0 (ms 3) 2 M') ∧ AnSperre (ms 3) 2 () ∧
    -- ... the layer does
    (∃ M', RwAcq P0 O0 0 lw (ms 3) 2 () M' ∧ M' = ms 4) ∧
    () ∈ offen ((ms 5).faeden 1).spur ∧ () ∈ offen ((ms 5).faeden 2).spur ∧
    -- the writer stands at the lock and has no step
    AnSperre (ms 5) 0 () ∧ (¬ ∃ M', RwSchritt P0 O0 0 lw (ms 5) 0 M') ∧ ¬ lw 0 () ∧
    RwExkl lw (ms 5) ∧
    -- after the readers left, the writer holds the lock alone
    () ∈ offen ((ms 10).faeden 0).spur ∧ (∀ g, g ≠ 0 → () ∉ offen ((ms 10).faeden g).spur) ∧
    -- a reader that arrives meanwhile is held back
    AnSperre (ms 12) 3 () ∧ (¬ ∃ M', RwSchritt P0 O0 0 lw (ms 12) 3 M') ∧ RwExkl lw (ms 12) ∧
    -- the order through the lock: the reader's section (step 1) before the writer's (step 10)
    fs 1 ≠ fs 10 ∧ GeordnetRw ms fs () 1 10 ∧
    -- PLANTED DEFECT: without `andere` and `leser` the writer is admitted next to both readers
    (∃ Mh0 Mx : RufMaschineG D0, RufSchrittG P0 O0 0 (ohneFremde (ms 5) 0) 0 Mh0 ∧
      Mx = { Mh0 with faeden := rufUpdateG (ms 5).faeden 0 (Mh0.faeden 0) } ∧ ¬ RwExkl lw Mx) := by
  -- thread 1: unfold, take the lock
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := P0) (O := O0) (passes := 0) (M := M00)
    (f := 1) rfl (wLocksS false WFn.t) (wRet false WFn.t) .nil rfl rfl
  have e1 : offen (M1.faeden 1).spur = [] := by
    rw [hZ1.1]
    exact wM0_offen false 1
  have hfrei : RufFreiG M1 1 () := by
    intro g hg
    rw [rufSchrittG_fremd s1 g hg, wM0_offen]
    exact List.not_mem_nil
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := P0) (O := O0) (passes := 0) (M := M1) (f := 1)
    hZ1.1 () (fun _ h => absurd h List.not_mem_nil) .nil .nil (.ende (wRet false WFn.t)) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res D0)) ↔ L ∈ offen ((wM0 false).faeden 1).spur
      rw [wM0_offen]
      simp only [List.not_mem_nil]) hfrei
  have h2spur : (M2.faeden 1).spur = Ereignis.nimmt () (offen (M1.weltVon 1).spur) ::
      (M1.weltVon 1).spur := by
    rw [hZ2.1]
    rfl
  have hold1 : () ∈ offen (M2.faeden 1).spur := by
    rw [h2spur]
    exact List.mem_cons_self
  -- thread 2: unfold
  have f2 : M2.faeden 2 = M00.faeden 2 := by
    rw [rufSchrittG_fremd s2 2 (by decide), rufSchrittG_fremd s1 2 (by decide)]
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := P0) (O := O0) (passes := 0) (M := M2)
    (f := 2) f2 (wLocksS false WFn.t) (wRet false WFn.t) .nil rfl rfl
  have hAn2 : AnSperre M3 2 () := by
    unfold AnSperre
    rw [hZ3.1]
    exact ⟨false, [], [], [], .nil, (fun _ h => absurd h List.not_mem_nil), .nil, .nil,
      .ende (wRet false WFn.t), rfl⟩
  have hold1' : () ∈ offen (M3.faeden 1).spur := by
    rw [rufSchrittG_fremd s3 1 (by decide)]
    exact hold1
  have hblock : ¬ ∃ M', RufSchrittG P0 O0 0 M3 2 M' :=
    nicht_bereit_an_sperre hAn2 (u := 1) (by decide) hold1'
  -- thread 2: the SHARED acquisition (machine G's own step in the machine with blank foreign traces)
  have wsp2 : offen (M2.weltVon 2).spur = [] := by
    show offen (M2.faeden 2).spur = []
    rw [f2]
    exact wM0_offen false 2
  have hz2 : (ohneFremde M3 2).faeden 2 = _ := (ohneFremde_self M3 2).trans hZ3.1
  obtain ⟨Mh, sh, hZh⟩ := w_locks (P := P0) (O := O0) (passes := 0) (M := ohneFremde M3 2) (f := 2)
    hz2 () (fun _ h => absurd h List.not_mem_nil) .nil .nil (.ende (wRet false WFn.t)) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res D0)) ↔ L ∈ offen (M2.weltVon 2).spur
      rw [wsp2]
      simp only [List.not_mem_nil]) (ohneFremde_frei M3 2 ())
  have hoff3 : ∀ g, g ≠ 1 → g ≠ 2 → offen (M3.faeden g).spur = [] := by
    intro g h1 h2
    rw [rufSchrittG_fremd s3 g h2, rufSchrittG_fremd s2 g h1, rufSchrittG_fremd s1 g h1]
    exact wM0_offen false g
  have hnot2 : () ∉ offen (M3.faeden 2).spur := by
    rw [hZ3.1]
    show () ∉ offen (M2.weltVon 2).spur
    rw [wsp2]
    exact List.not_mem_nil
  have hhMh : (Mh.faeden 2).spur = Ereignis.nimmt () (offen ((ohneFremde M3 2).weltVon 2).spur) ::
      ((ohneFremde M3 2).weltVon 2).spur := by
    rw [hZh.1]
    rfl
  let M4 : RufMaschineG D0 := { Mh with faeden := rufUpdateG M3.faeden 2 (Mh.faeden 2) }
  have hM4_2 : M4.faeden 2 = Mh.faeden 2 := by
    show rufUpdateG M3.faeden 2 (Mh.faeden 2) 2 = Mh.faeden 2
    exact rufUpdateG_self _ _ _
  have hacq : RwAcq P0 O0 0 lw M3 2 () M4 :=
    { leser := lw_pos (by decide)
      andere := fun g hg hL => by
        by_cases h1 : g = 1
        · subst h1; exact lw_pos (by decide)
        · rw [hoff3 g h1 hg] at hL
          exact absurd hL List.not_mem_nil
      neu := ⟨hnot2, by
        rw [hM4_2, hhMh]
        exact List.mem_cons_self⟩
      schritt := ⟨Mh, sh, rfl⟩ }
  have s4 : RwSchritt P0 O0 0 lw M3 2 M4 := Or.inr ⟨(), hacq⟩
  -- thread 0 (the writer): unfold
  have f0 : M4.faeden 0 = M00.faeden 0 := by
    rw [fremd_w s4 (by decide)]
    rw [rufSchrittG_fremd s3 0 (by decide), rufSchrittG_fremd s2 0 (by decide),
      rufSchrittG_fremd s1 0 (by decide)]
  obtain ⟨M5, s5, hZ5⟩ := w_endeEntf (P := P0) (O := O0) (passes := 0) (M := M4)
    (f := 0) f0 (wLocksS false WFn.h) (wRet false WFn.h) .nil rfl rfl
  have hAn0 : AnSperre M5 0 () := by
    unfold AnSperre
    rw [hZ5.1]
    exact ⟨false, [], [], [], .nil, (fun _ h => absurd h List.not_mem_nil), .nil, .nil,
      .ende (wRet false WFn.h), rfl⟩
  have hold1'' : () ∈ offen (M5.faeden 1).spur := by
    rw [rufSchrittG_fremd s5 1 (by decide), fremd_w s4 (by decide)]
    exact hold1'
  have hold2'' : () ∈ offen (M5.faeden 2).spur := by
    rw [rufSchrittG_fremd s5 2 (by decide), hM4_2, hhMh]
    exact List.mem_cons_self
  -- the planted defect: the writer's lock step in the blank machine, kept next to both readers
  have wsp4 : offen (M4.weltVon 0).spur = [] := by
    show offen (M4.faeden 0).spur = []
    rw [f0]
    exact wM0_offen false 0
  have hz0 : (ohneFremde M5 0).faeden 0 = _ := (ohneFremde_self M5 0).trans hZ5.1
  obtain ⟨Mw, sw, hZw⟩ := w_locks (P := P0) (O := O0) (passes := 0) (M := ohneFremde M5 0) (f := 0)
    hz0 () (fun _ h => absurd h List.not_mem_nil) .nil .nil (.ende (wRet false WFn.h)) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res D0)) ↔ L ∈ offen (M4.weltVon 0).spur
      rw [wsp4]
      simp only [List.not_mem_nil]) (ohneFremde_frei M5 0 ())
  have hwspur : (Mw.faeden 0).spur =
      Ereignis.nimmt () (offen ((ohneFremde M5 0).weltVon 0).spur) :: ((ohneFremde M5 0).weltVon 0).spur := by
    rw [hZw.1]
    rfl
  let Mx : RufMaschineG D0 := { Mw with faeden := rufUpdateG M5.faeden 0 (Mw.faeden 0) }
  have hMx0 : Mx.faeden 0 = Mw.faeden 0 := by
    show rufUpdateG M5.faeden 0 (Mw.faeden 0) 0 = Mw.faeden 0
    exact rufUpdateG_self _ _ _
  have hMx1 : Mx.faeden 1 = M5.faeden 1 := by
    show rufUpdateG M5.faeden 0 (Mw.faeden 0) 1 = M5.faeden 1
    exact rufUpdateG_noteq _ _ _ (by decide) _
  have hmx : ¬ RwExkl lw Mx := by
    intro h
    have h0 : () ∈ offen (Mx.faeden 0).spur := by
      rw [hMx0, hwspur]
      exact List.mem_cons_self
    have h1 : () ∈ offen (Mx.faeden 1).spur := by
      rw [hMx1]
      exact hold1''
    exact (h 0 1 () (by decide) h0 h1).1 rfl
  -- thread 1: dannLeer, release
  have f1_5 : M5.faeden 1 = M2.faeden 1 := by
    rw [rufSchrittG_fremd s5 1 (by decide), fremd_w s4 (by decide), rufSchrittG_fremd s3 1 (by decide)]
  obtain ⟨M6, s6, hZ6⟩ := w_dannLeer (P := P0) (O := O0) (passes := 0) (M := M5) (f := 1)
    (f1_5.trans hZ2.1) (.frei () (.dann .nil (.ende (wRet false WFn.t)))) .nil rfl
  obtain ⟨M7, s7, hZ7⟩ := w_freiGib (P := P0) (O := O0) (passes := 0) (M := M6) (f := 1)
    hZ6.1 () (.dann .nil (.ende (wRet false WFn.t))) .nil rfl
  have e6 : (M6.faeden 1).spur = (M2.faeden 1).spur := by
    rw [hZ6.1]
    show (M5.faeden 1).spur = (M2.faeden 1).spur
    rw [f1_5]
  have e7 : (M7.faeden 1).spur = Ereignis.gibt () :: (M6.faeden 1).spur := by
    rw [hZ7.1]
    rfl
  have h7 : offen (M7.faeden 1).spur = [] := by
    rw [e7, e6, h2spur]
    have e1' : offen (M1.weltVon 1).spur = [] := e1
    simp only [offen, e1']
    first | rfl | decide
  -- thread 2: dannLeer, release
  have f2_7 : M7.faeden 2 = Mh.faeden 2 := by
    rw [rufSchrittG_fremd s7 2 (by decide), rufSchrittG_fremd s6 2 (by decide),
      rufSchrittG_fremd s5 2 (by decide), hM4_2]
  obtain ⟨M8, s8, hZ8⟩ := w_dannLeer (P := P0) (O := O0) (passes := 0) (M := M7) (f := 2)
    (f2_7.trans hZh.1) (.frei () (.dann .nil (.ende (wRet false WFn.t)))) .nil rfl
  obtain ⟨M9, s9, hZ9⟩ := w_freiGib (P := P0) (O := O0) (passes := 0) (M := M8) (f := 2)
    hZ8.1 () (.dann .nil (.ende (wRet false WFn.t))) .nil rfl
  have wsp3 : offen ((ohneFremde M3 2).weltVon 2).spur = [] := by
    show offen ((ohneFremde M3 2).faeden 2).spur = []
    rw [hz2]
    exact wsp2
  have e8 : (M8.faeden 2).spur = (Mh.faeden 2).spur := by
    rw [hZ8.1]
    show (M7.faeden 2).spur = (Mh.faeden 2).spur
    rw [f2_7]
  have e9 : (M9.faeden 2).spur = Ereignis.gibt () :: (M8.faeden 2).spur := by
    rw [hZ9.1]
    rfl
  have h9 : offen (M9.faeden 2).spur = [] := by
    rw [e9, e8, hhMh]
    simp only [offen, wsp3]
    first | rfl | decide
  -- the writer takes the lock, alone
  have f0_9 : M9.faeden 0 = M5.faeden 0 := by
    rw [rufSchrittG_fremd s9 0 (by decide), rufSchrittG_fremd s8 0 (by decide),
      rufSchrittG_fremd s7 0 (by decide), rufSchrittG_fremd s6 0 (by decide)]
  have hfrei10 : RufFreiG M9 0 () := by
    intro g hg
    by_cases h1 : g = 1
    · subst h1
      rw [rufSchrittG_fremd s9 1 (by decide), rufSchrittG_fremd s8 1 (by decide)]
      rw [h7]
      exact List.not_mem_nil
    · by_cases h2 : g = 2
      · subst h2
        rw [h9]
        exact List.not_mem_nil
      · rw [rufSchrittG_fremd s9 g h2, rufSchrittG_fremd s8 g h2, rufSchrittG_fremd s7 g h1,
          rufSchrittG_fremd s6 g h1, rufSchrittG_fremd s5 g hg, fremd_w s4 h2,
          rufSchrittG_fremd s3 g h2, rufSchrittG_fremd s2 g h1, rufSchrittG_fremd s1 g h1,
          wM0_offen]
        exact List.not_mem_nil
  obtain ⟨M10, s10, hZ10⟩ := w_locks (P := P0) (O := O0) (passes := 0) (M := M9) (f := 0)
    (f0_9.trans hZ5.1) () (fun _ h => absurd h List.not_mem_nil) .nil .nil
    (.ende (wRet false WFn.h)) .nil rfl
    (fun L => by
      show Res.held L ∈ ([] : List (Res D0)) ↔ L ∈ offen (M4.weltVon 0).spur
      rw [wsp4]
      simp only [List.not_mem_nil]) hfrei10
  have h10spur : (M10.faeden 0).spur =
      Ereignis.nimmt () (offen (M9.weltVon 0).spur) :: (M9.weltVon 0).spur := by
    rw [hZ10.1]
    rfl
  have hold10 : () ∈ offen (M10.faeden 0).spur := by
    rw [h10spur]
    exact List.mem_cons_self
  have hfree10 : ∀ g, g ≠ 0 → () ∉ offen (M10.faeden g).spur := by
    intro g hg
    rw [rufSchrittG_fremd s10 g hg]
    exact hfrei10 g hg
  -- the writer leaves its (empty) section but still holds the lock
  obtain ⟨N10, s10b, hZ10b⟩ := w_dannLeer (P := P0) (O := O0) (passes := 0) (M := M10) (f := 0)
    hZ10.1 (.frei () (.dann .nil (.ende (wRet false WFn.h)))) .nil rfl
  have hold10b : () ∈ offen (N10.faeden 0).spur := by
    rw [hZ10b.1]
    exact hold10
  -- thread 3 (a reader) arrives
  have f3 : N10.faeden 3 = M00.faeden 3 := by
    rw [rufSchrittG_fremd s10b 3 (by decide), rufSchrittG_fremd s10 3 (by decide), rufSchrittG_fremd s9 3 (by decide),
      rufSchrittG_fremd s8 3 (by decide), rufSchrittG_fremd s7 3 (by decide),
      rufSchrittG_fremd s6 3 (by decide), rufSchrittG_fremd s5 3 (by decide), fremd_w s4 (by decide),
      rufSchrittG_fremd s3 3 (by decide), rufSchrittG_fremd s2 3 (by decide),
      rufSchrittG_fremd s1 3 (by decide)]
  obtain ⟨M11, s11, hZ11⟩ := w_endeEntf (P := P0) (O := O0) (passes := 0) (M := N10)
    (f := 3) f3 (wLocksS false WFn.t) (wRet false WFn.t) .nil rfl rfl
  have hAn3 : AnSperre M11 3 () := by
    unfold AnSperre
    rw [hZ11.1]
    exact ⟨false, [], [], [], .nil, (fun _ h => absurd h List.not_mem_nil), .nil, .nil,
      .ende (wRet false WFn.t), rfl⟩
  have hold11 : () ∈ offen (M11.faeden 0).spur := by
    rw [rufSchrittG_fremd s11 0 (by decide)]
    exact hold10b
  -- the run
  obtain ⟨ms1, fs1, l1, m1, k1, n1, p1⟩ := rwLauf_schritt (rwLauf_nil (P := P0) (O := O0) (passes := 0)
    (lese := lw) M00) rfl (rwSchritt_of_G s1)
  obtain ⟨ms2, fs2, l2, m2, k2, n2, p2⟩ := rwLauf_schritt l1 m1 (rwSchritt_of_G s2)
  obtain ⟨ms3, fs3, l3, m3, k3, n3, p3⟩ := rwLauf_schritt l2 m2 (rwSchritt_of_G s3)
  obtain ⟨ms4, fs4, l4, m4, k4, n4, p4⟩ := rwLauf_schritt l3 m3 s4
  obtain ⟨ms5, fs5, l5, m5, k5, n5, p5⟩ := rwLauf_schritt l4 m4 (rwSchritt_of_G s5)
  obtain ⟨ms6, fs6, l6, m6, k6, n6, p6⟩ := rwLauf_schritt l5 m5 (rwSchritt_of_G s6)
  obtain ⟨ms7, fs7, l7, m7, k7, n7, p7⟩ := rwLauf_schritt l6 m6 (rwSchritt_of_G s7)
  obtain ⟨ms8, fs8, l8, m8, k8, n8, p8⟩ := rwLauf_schritt l7 m7 (rwSchritt_of_G s8)
  obtain ⟨ms9, fs9, l9, m9, k9, n9, p9⟩ := rwLauf_schritt l8 m8 (rwSchritt_of_G s9)
  obtain ⟨ms10, fs10, l10, m10, k10, n10, p10⟩ := rwLauf_schritt l9 m9 (rwSchritt_of_G s10)
  obtain ⟨ms11, fs11, l11, m11, k11, n11, p11⟩ := rwLauf_schritt l10 m10 (rwSchritt_of_G s10b)
  obtain ⟨ms12, fs12, l12, m12, k12, n12, p12⟩ := rwLauf_schritt l11 m11 (rwSchritt_of_G s11)
  have back : ∀ j, j ≤ 5 → ms12 j = ms5 j := by
    intro j hj
    rw [k12 j (by omega), k11 j (by omega), k10 j (by omega), k9 j (by omega), k8 j (by omega),
      k7 j (by omega), k6 j (by omega)]
  have hm2 : ms12 2 = M2 := by
    rw [back 2 (by omega), k5 2 (by omega), k4 2 (by omega), k3 2 (by omega), m2]
  have hm3 : ms12 3 = M3 := by rw [back 3 (by omega), k5 3 (by omega), k4 3 (by omega), m3]
  have hm4 : ms12 4 = M4 := by rw [back 4 (by omega), k5 4 (by omega), m4]
  have hm5 : ms12 5 = M5 := by rw [back 5 (by omega), m5]
  have hm10 : ms12 10 = M10 := by rw [k12 10 (by omega), k11 10 (by omega), m10]
  have hf1 : fs12 1 = 1 := by
    rw [p12 1 (by omega), p11 1 (by omega), p10 1 (by omega), p9 1 (by omega), p8 1 (by omega),
      p7 1 (by omega), p6 1 (by omega), p5 1 (by omega), p4 1 (by omega), p3 1 (by omega), n2]
  have hf10 : fs12 10 = 0 := by rw [p12 10 (by omega), n11]
  have hfg : fs12 1 ≠ fs12 10 := by rw [hf1, hf10]; decide
  have hordn : GeordnetRw ms12 fs12 () 1 10 := by
    refine sperre_ordnet_rw O0_gut l12 exkl0 1 10 (by omega) (by omega) hfg () ?_ ?_ ?_
    · rw [hf1, hm2]; exact hold1
    · rw [hf10, hm10]; exact hold10
    · refine Or.inr ?_
      rw [hf10]
      intro h
      exact h rfl
  refine ⟨ms12, fs12, l12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfg, hordn, ?_⟩
  · rw [hm3]; exact hblock
  · rw [hm3]; exact hAn2
  · rw [hm3]; exact ⟨M4, hacq, hm4.symm⟩
  · rw [hm5]; exact hold1''
  · rw [hm5]; exact hold2''
  · rw [hm5]; exact hAn0
  · rw [hm5]
    rintro ⟨M', hM' | ⟨L, hL⟩⟩
    · exact nicht_bereit_an_sperre hAn0 (u := 1) (by decide) hold1'' ⟨M', hM'⟩
    · exact hL.leser rfl
  · intro h; exact h rfl
  · exact rwExkl_lauf O0_gut l12 exkl0 5 (by omega)
  · rw [hm10]; exact hold10
  · rw [hm10]; exact hfree10
  · rw [m12]; exact hAn3
  · rw [m12]
    rintro ⟨M', hM' | ⟨L, hL⟩⟩
    · exact nicht_bereit_an_sperre hAn3 (u := 0) (by decide) hold11 ⟨M', hM'⟩
    · exact hL.andere 0 (by decide) hold11 rfl
  · exact rwExkl_lauf O0_gut l12 exkl0 12 (Nat.le_refl 12)
  · rw [hm5]; exact ⟨Mw, Mx, sw, rfl, hmx⟩

/-- **A reader cannot take the lock it already holds**: in a section that holds `()`, the premise `hr` of
    `Stmt.locks ()` (every held lock ranks strictly below) is false. -/
theorem leser_rekursiv_verweigert :
    ¬ ∀ K, Res.held K ∈ [Res.held (D := D0) ()] → D0.rang K < D0.rang () := by
  intro h
  have := h () List.mem_cons_self
  exact absurd this (by decide)

end Gabbro.Grammatik.Zielsatz.RwFix

#print axioms Gabbro.Grammatik.Zielsatz.RwFix.leser_schreiber_lauf
#print axioms Gabbro.Grammatik.Zielsatz.RwFix.leser_rekursiv_verweigert
