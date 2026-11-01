module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- **The run.** Eighteen steps of the repaired G from the start machine of
    `zP` (every thread in `haupt`, `konto` all zero): thread 1 takes the lock,
    enters `wrap`, calls `lies` (reads 0) and `einzahlen` (writes 100),
    returns to `haupt` and releases the lock (twelve steps, the machine `M9`
    after the ninth: the write done, both calls logged and returned); then
    thread 0 takes the lock, enters `wrap` and `lies`, reads `konto[0]` --
    the 100 thread 1 wrote -- and returns it. -/
theorem zLauf : ∃ M9 M17 M18 : RufMaschineG zD,
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M9 ∧
    RufErreichbarG zP zO 0 M9 M17 ∧ RufErreichbarG zP zO 0 M17 M18 ∧
    -- after the ninth step: memory moved, `lies` and `einzahlen` called and returned
    (M9.speicher.slots () 0 ()).n = 100 ∧
    (∃ rho s0, RufEreignisF.eintritt zEin rho s0 ∈ (M9.faeden 1).log) ∧
    (∃ rho v s0 s1, RufEreignisF.rueck zEin rho v s0 s1 ∈ (M9.faeden 1).log) ∧
    (∃ rho v s0 s1, RufEreignisF.rueck zLies rho v s0 s1 ∈ (M9.faeden 1).log) ∧
    -- thread 0 inside `lies` holds the lock, thread 1 does not
    (M17.faeden 0).kopf.f = zLies ∧ (() : zD.Lock) ∈ offen (M17.faeden 0).spur ∧
    (() : zD.Lock) ∉ offen (M17.faeden 1).spur ∧
    -- thread 0's `lies` returns 100, the value thread 1 wrote under the lock
    (∃ (rho : Env zD (zD.params zLies)) (v : ErgVal zD (zD.erg zLies)) (s0 s1 : World zD),
      RufEreignisF.rueck zLies rho v s0 s1 ∈ (M18.faeden 0).log ∧
      (show Zahl 0 100 from v).n = 100 ∧ (s1.slots () 0 ()).n = 100) ∧
    -- thread 0 has not moved before thread 1's write
    M9.faeden 0 = (RufStartG zP zSp zInit).faeden 0 ∧
    -- thread 0's head frame names the lock statically
    Res.held (() : zD.Lock) ∈ (M17.faeden 0).kopf.rest.2.2.1 := by
  have h01 := zM0_faden (1 : Faden)
  have hoff0 : offen ((RufStartG zP zSp zInit).faeden 1).spur = [] := rfl
  -- thread 1: `endeEntf`, `locks`, call `wrap`, call `lies`, bind
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := zP) (O := zO) (passes := 0) h01 zLocks zHauptRet
    .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := zP) (O := zO) (passes := 0) hZ1.1 ()
    _ _ _ _ .nil rfl (hg0 hoff0)
    (fun u hu h => by rw [rufSchrittG_fremd s1 u hu, zM0_faden] at h; exact List.not_mem_nil h)
  have hoff2 : offen (M2.faeden 1).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon 1).spur) :: (M1.weltVon 1).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ1.spur]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := zP) (O := zO) (passes := 0) hZ2.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 1).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hZ3.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .empty (by rfl))) .nil rfl
    (hgL (hoff_z hZ3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := zP) (O := zO) (passes := 0) hZ4.1
    (.slot () () zIdx zDarf) (.ret (.val (.var .here)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff4
  -- return from `lies`, call `einzahlen`, write, return
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hG6.1 zEin .nil zHpEin rfl
    (.ret .empty (by rfl)) .nil rfl
    (hgL (hoff_g hG6 hoff6)).heldIn
  have hoff7 : offen (M7.faeden 1).spur = [()] := by
    rw [hZ7.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff6
  obtain ⟨M8, s8, hZ8⟩ := w_blatt (P := zP) (O := zO) (passes := 0) hZ7.1
    _ _ _ rfl rfl
    (hgL (hoff_z hZ7 hoff7)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff8 : offen (M8.faeden 1).spur = [()] := by
    rw [hZ8.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff7
  obtain ⟨M9, s9, hG9⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ8.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ8 hoff8)).heldIn
  have hoff9 : offen (M9.faeden 1).spur = [()] := by
    rw [hG9.1]
    exact ((Erw.lese _ _ _).offen).trans hoff8
  have hr9 : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M9 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7) s8) s9
  have hsp9 : (M9.speicher.slots () 0 ()).n = 100 := by
    rw [hG9.2]
    show (M8.speicher.slots () 0 ()).n = 100
    rw [hZ8.2]
    rfl
  -- return from `wrap`, leave the `locks`
  obtain ⟨M10, s10, hG10⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hG9.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_g hG9 hoff9)).heldIn
  have hoff10 : offen (M10.faeden 1).spur = [()] := by
    rw [hG10.1]
    exact ((Erw.lese _ _ _).offen).trans hoff9
  obtain ⟨M11, s11, hZ11⟩ := w_dannLeer (P := zP) (O := zO) (passes := 0) hG10.1 _ .nil rfl
  obtain ⟨M12, s12, hZ12⟩ := w_freiGib (P := zP) (O := zO) (passes := 0) hZ11.1 () _ .nil rfl
  have hoff12 : offen (M12.faeden 1).spur = [] := by
    rw [hZ12.spur]
    show (offen (M11.weltVon 1).spur).erase () = []
    rw [offen_weltVon, hZ11.spur, offen_weltVon, hoff10]
    rfl
  -- thread 0: the same prefix, reading what thread 1 wrote
  have hfremd12 : ∀ u, u ≠ 1 → M12.faeden u = zZ0 := by
    intro u hu
    rw [rufSchrittG_fremd s12 u hu, rufSchrittG_fremd s11 u hu, rufSchrittG_fremd s10 u hu,
      rufSchrittG_fremd s9 u hu, rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu,
      rufSchrittG_fremd s6 u hu, rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu,
      rufSchrittG_fremd s3 u hu, rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu, zM0_faden]
  have h00 : M12.faeden 0 = zZ0 := hfremd12 0 (by decide)
  obtain ⟨M13, s13, hZ13⟩ := w_endeEntf (P := zP) (O := zO) (passes := 0) h00 zLocks zHauptRet
    .nil rfl rfl
  have hfrei13 : RufFreiG M13 0 () := by
    intro u hu
    rw [rufSchrittG_fremd s13 u hu]
    by_cases hu1 : u = 1
    · subst hu1; rw [hoff12]; exact List.not_mem_nil
    · rw [hfremd12 u hu1]; exact List.not_mem_nil
  obtain ⟨M14, s14, hZ14⟩ := w_locks (P := zP) (O := zO) (passes := 0) hZ13.1 ()
    _ _ _ _ .nil rfl (hg0 (by show offen (M12.faeden 0).spur = []; rw [h00]; rfl)) hfrei13
  have hoff14 : offen (M14.faeden 0).spur = [()] := by
    rw [hZ14.spur]
    show offen (Ereignis.nimmt () (offen (M13.weltVon 0).spur) :: (M13.weltVon 0).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ13.spur]
    show () :: offen (M12.faeden 0).spur = [()]
    rw [h00]
    rfl
  obtain ⟨M15, s15, hZ15⟩ := w_rufDann (P := zP) (O := zO) (passes := 0) hZ14.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ14 hoff14)).heldIn
  have hoff15 : offen (M15.faeden 0).spur = [()] := by
    rw [hZ15.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff14
  obtain ⟨M16, s16, hZ16⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hZ15.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .empty (by rfl))) .nil rfl
    (hgL (hoff_z hZ15 hoff15)).heldIn
  have hoff16 : offen (M16.faeden 0).spur = [()] := by
    rw [hZ16.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff15
  obtain ⟨M17, s17, hZ17⟩ := w_endeBind (P := zP) (O := zO) (passes := 0) hZ16.1
    (.slot () () zIdx zDarf) (.ret (.val (.var .here)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ16 hoff16)).heldIn
  have hoff17 : offen (M17.faeden 0).spur = [()] := by
    rw [hZ17.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff16
  obtain ⟨M18, s18, hG18⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ17.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl
    (hgL (hoff_z hZ17 hoff17)).heldIn
  have e9 : M9.speicher = M8.speicher := by rw [hG9.2]; rfl
  have e10 : M10.speicher = M9.speicher := by rw [hG10.2]; rfl
  have e11 : M11.speicher = M10.speicher := by rw [hZ11.2]; rfl
  have e12 : M12.speicher = M11.speicher := by rw [hZ12.2]; rfl
  have e13 : M13.speicher = M12.speicher := by rw [hZ13.2]; rfl
  have e14 : M14.speicher = M13.speicher := by rw [hZ14.2]; rfl
  have e15 : M15.speicher = M14.speicher := by rw [hZ15.2]; rfl
  have e16 : M16.speicher = M15.speicher := by rw [hZ16.2]; rfl
  have e17 : M17.speicher = M16.speicher := by rw [hZ17.2]; rfl
  have hsp16 : M16.speicher = M8.speicher := by
    rw [e16, e15, e14, e13, e12, e11, e10, e9]
  have h90 : M9.faeden 0 = (RufStartG zP zSp zInit).faeden 0 := by
    rw [rufSchrittG_fremd s9 0 (by decide), rufSchrittG_fremd s8 0 (by decide),
      rufSchrittG_fremd s7 0 (by decide), rufSchrittG_fremd s6 0 (by decide),
      rufSchrittG_fremd s5 0 (by decide), rufSchrittG_fremd s4 0 (by decide),
      rufSchrittG_fremd s3 0 (by decide), rufSchrittG_fremd s2 0 (by decide),
      rufSchrittG_fremd s1 0 (by decide)]
  have h17_1 : M17.faeden 1 = M12.faeden 1 := by
    rw [rufSchrittG_fremd s17 1 (by decide), rufSchrittG_fremd s16 1 (by decide),
      rufSchrittG_fremd s15 1 (by decide), rufSchrittG_fremd s14 1 (by decide),
      rufSchrittG_fremd s13 1 (by decide)]
  refine ⟨M9, M17, M18, hr9,
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ .start s10) s11) s12) s13) s14) s15) s16) s17,
    .schritt _ _ _ .start s18, hsp9, ?_, ?_, ?_, by rw [hZ17.1], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hG9.1]
    exact ⟨_, _, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · rw [hG9.1]
    exact ⟨_, _, _, _, List.mem_cons_self⟩
  · rw [hG9.1]
    exact ⟨_, _, _, _, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · rw [hoff17]; exact List.mem_cons_self
  · rw [h17_1, hoff12]; exact List.not_mem_nil
  · refine ⟨_, _, _, _, by rw [hG18.1]; exact List.mem_cons_self, ?_, ?_⟩
    · show (M16.speicher.slots () 0 ()).n = 100
      rw [hsp16, hZ8.2]
      rfl
    · show (M17.speicher.slots () 0 ()).n = 100
      rw [e17, hsp16, hZ8.2]
      rfl
  · exact h90
  · rw [hZ17.1]; exact List.mem_cons_self


/-! ## 4. The witnesses -/

/-- **`ziel_ort_zeuge`.** Every premise of `ziel_ort` holds jointly on the
    non-degenerate program `zP` (user obligations for all four functions,
    start, exclusive start, good oracle, the two decidable checks on the
    complete function list), and on a reached run of nine steps, in which
    memory moved from `0` to `100` (thread 1's `einzahlen` wrote `konto[0]`
    under its signature lock) and `einzahlen` and `lies` were entered and
    returned, the contract holds at every logged entry and return. -/
theorem ziel_ort_zeuge :
    GutO zO ∧ (∀ g : zD.Fn, g ∈ zFs) ∧ programmImFragment zP zFs = true ∧
    fussOrtB zP zFs = true ∧ (∀ f : zD.Fn, KoerperGut zP zO 0 f) ∧ StartGut zP zSp zInit ∧
    StartExklusiv (D := zD) zInit ∧
    ∃ M : RufMaschineG zD, RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
      (zSp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ rho s0, RufEreignisF.eintritt zEin rho s0 ∈ (M.faeden 1).log) ∧
      (∃ rho v s0 s1, RufEreignisF.rueck zEin rho v s0 s1 ∈ (M.faeden 1).log) ∧
      (∃ rho v s0 s1, RufEreignisF.rueck zLies rho v s0 s1 ∈ (M.faeden 1).log) ∧
      VertragAmOrtG zP M := by
  obtain ⟨M9, _, _, h9, _, _, hsp, he, hr, hl, _⟩ := zLauf
  exact ⟨zO_gut, zFs_voll, zP_fragment, zP_fuss, zP_koerper, zP_start, zInit_exklusiv,
    M9, h9, rfl, hsp, he, hr, hl, zP_vertragAmOrt M9 h9⟩

/-- **The interference witness.** Thread 1 writes `konto[0] := 100`
    (the carrier of `lies`' contract) in `einzahlen`, which holds the
    common lock by signature, while thread 0 has logged nothing but its own
    start; afterwards thread 0 enters `lies` and holds the lock
    throughout (at the step before its return it holds it and thread 1 does
    not). Thread 0's `lies` returns `100` -- a value no step of its own
    wrote -- in a return world whose `konto[0]` is `100`, and its contract
    `result = konto[0]` holds there: at the logged return, by `ziel_ort`. -/
theorem ziel_ort_zeuge_interferenz :
    ∃ M9 M17 M18 : RufMaschineG zD,
      RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M9 ∧
      RufErreichbarG zP zO 0 M9 M17 ∧ RufErreichbarG zP zO 0 M17 M18 ∧
      (zSp.slots () 0 ()).n = 0 ∧ (M9.speicher.slots () 0 ()).n = 100 ∧
      (∃ rho v s0 s1, RufEreignisF.rueck zEin rho v s0 s1 ∈ (M9.faeden 1).log) ∧
      (M9.faeden 0).log = [RufEreignisF.eintritt zHaupt .nil (zSp.welt [])] ∧
      (M17.faeden 0).kopf.f = zLies ∧ (() : zD.Lock) ∈ offen (M17.faeden 0).spur ∧
      (() : zD.Lock) ∉ offen (M17.faeden 1).spur ∧
      (∃ (rho : Env zD (zD.params zLies)) (v : ErgVal zD (zD.erg zLies)) (s0 s1 : World zD),
        RufEreignisF.rueck zLies rho v s0 s1 ∈ (M18.faeden 0).log ∧
        (show Zahl 0 100 from v).n = 100 ∧ (s1.slots () 0 ()).n = 100 ∧
        EnsAmRueck zP zLies s0 s1 rho v) := by
  obtain ⟨M9, M17, M18, h9, h17, h18, hsp, _, hr, _, hf, hin, hout,
    ⟨rho, v, s0, s1, hm, hv, hs⟩, h90, _⟩ := zLauf
  have h18' : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M18 :=
    rufErreichbarG_trans (rufErreichbarG_trans h9 h17) h18
  exact ⟨M9, M17, M18, h9, h17, h18, rfl, hsp, hr, by rw [h90]; rfl, hf, hin, hout, rho, v, s0, s1,
    hm, hv, hs, (zP_vertragAmOrt M18 h18' 0 _ hm).2 _ _ _ _ _ rfl⟩

/-- **`rufG_haelt_statisch_zeuge`** (and the signature companion): on a
    reached machine of `zP` with two running threads, thread 0's head
    frame (in `lies`) names the lock statically and by signature, and the
    theorems give that thread 0 holds it -- while thread 1, whose `locks`
    block has ended, does not. -/
theorem rufG_haelt_statisch_zeuge :
    ∃ M : RufMaschineG zD, RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
      Res.held (() : zD.Lock) ∈ (M.faeden 0).kopf.rest.2.2.1 ∧
      (() : zD.Lock) ∈ zD.haelt (M.faeden 0).kopf.f ∧
      (() : zD.Lock) ∈ offen (M.faeden 0).spur ∧ (() : zD.Lock) ∉ offen (M.faeden 1).spur := by
  obtain ⟨M9, M17, _, h9, h17, _, _, _, _, _, hf, _, hout, _, _, hheld⟩ := zLauf
  have h : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M17 := rufErreichbarG_trans h9 h17
  have hsig : (() : zD.Lock) ∈ zD.haelt (M17.faeden 0).kopf.f := by
    rw [hf]; exact List.mem_cons_self
  exact ⟨M17, h, hheld, hsig,
    rufG_haelt_statisch zO_gut zSp zInit h 0 _ List.mem_cons_self () hheld, hout⟩

theorem rufG_haelt_signatur_zeuge :
    ∃ M : RufMaschineG zD, RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
      (M.faeden 0).kopf.f = zLies ∧ (() : zD.Lock) ∈ offen (M.faeden 0).spur ∧
      (() : zD.Lock) ∉ offen (M.faeden 1).spur := by
  obtain ⟨M9, M17, _, h9, h17, _, _, _, _, _, hf, _, hout, _, _, _⟩ := zLauf
  have h : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M17 := rufErreichbarG_trans h9 h17
  have hsig : (() : zD.Lock) ∈ zD.haelt (M17.faeden 0).kopf.f := by
    rw [hf]; exact List.mem_cons_self
  exact ⟨M17, h, hf, rufG_haelt_signatur zO_gut zSp zInit h 0 _ List.mem_cons_self () hsig, hout⟩

/-! ## CUTS:

  What is proved: all premises of `ziel_ort` hold jointly on `zP`
  (`zP_vertragAmOrt` is the instance), and two reached runs of the
  machine: `ziel_ort_zeuge` (nine steps of thread 1: memory `0 -> 100`,
  `einzahlen` and `lies` entered and returned, contracts at every logged
  event) and `ziel_ort_zeuge_interferenz` (thread 1 writes the carrier of
  `lies`' contract, thread 0 then runs `lies` holding the lock and returns
  the other thread's value `100`, and `EnsAmRueck` holds at that return).
  The same run witnesses `rufG_haelt_statisch` and `rufG_haelt_signatur`
  (`rufG_haelt_statisch_zeuge`, `rufG_haelt_signatur_zeuge`: a frame naming
  the lock on a two-thread machine where the other thread does not hold
  it).

  What is NOT covered: runs with interleaving INSIDE a critical section
  (the lock forbids them; the rely of `ziel_ort` is what makes that
  exclusion usable), loops, the error channel, costs.
-/

#print axioms Gabbro.Grammatik.zP_vertragAmOrt
#print axioms Gabbro.Grammatik.zLauf
#print axioms Gabbro.Grammatik.ziel_ort_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_zeuge_interferenz
#print axioms Gabbro.Grammatik.rufG_haelt_statisch_zeuge
#print axioms Gabbro.Grammatik.rufG_haelt_signatur_zeuge

end Gabbro.Grammatik
