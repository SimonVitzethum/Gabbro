/-
  File:      Grammatik/MehrfadenLauf.lean
  Subject:   THE RUNS of the two-writer witness with private tables
             (`MehrfadenZeuge.lean`, SATZKARTE §16): the conclusions of the
             new theorems on reached machines, not only their premises.

  * `ziel_ort_mehrfaden_zeuge` (items 1 and 2): thread 0 writes its
    unguarded `privA`, both ACTIVE threads run their critical sections on
    the shared `konto`, then thread 0's `pruefeA` finds `privA[0] == 7` at
    its logged entry BY THE THEOREM; thread 0 finishes and `hauptA`'s
    `ensures` and owed invariant hold at its final state BY THE THEOREM.
  * `keine_verklemmungG_zeuge` (item 3): `schritt_an_sperre` gives a step at
    a `locks` head; a reached machine where thread 1 WAITS for the lock
    thread 0 holds, and the deadlock theorem there.
-/
import Grammatik.MehrfadenZeuge
namespace Gabbro.Grammatik

theorem mhgL {s : List (Ereignis mD)} (h : offen s = [()]) : HeldGenau mL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem mhg0 {s : List (Ereignis mD)} (h : offen s = []) :
    HeldGenau ([] : List (Res mD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem moff_z {M : RufMaschineG mD} {f : Faden} {stapel : List (RufRahmenG mD)} {fn : mD.Fn}
    {rho : Env mD (mD.params fn)} {s0 : World mD} {log : List (RufEreignisF mD)} {l : Bool}
    {Γ : Ctx} {Λ : List (Res mD)} {ρ : Env mD Γ} {r : GRest mD (vertragVon mD fn) l Γ Λ}
    {σ : World mD} {x : List mD.Lock} (h : ZustandG M f stapel fn rho s0 log ρ r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [← h.spur]; exact ho

theorem moff_g {M : RufMaschineG mD} {f : Faden} {caller : RufRahmenG mD}
    {rst : List (RufRahmenG mD)} {fn : mD.Fn} {rho : Env mD (mD.params fn)} {s0 : World mD}
    {log : List (RufEreignisF mD)} {v : ErgVal mD (mD.erg fn)} {σ : World mD} {x : List mD.Lock}
    (h : GepopptG M f caller rst fn rho s0 log v σ) (ho : offen (M.faeden f).spur = x) :
    offen σ.spur = x := by
  rw [h.1] at ho; exact ho

/-- **One critical section of a thread standing at `locks { setze(e) }`**:
    eight steps -- take the lock, call `setze`, both writes, return, the
    empty rest, release, the empty rest -- end at the continuation `k`
    with no lock held. Nothing else moves. -/
theorem mAbschnitt {M : RufMaschineG mD} (hr : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M)
    (t : Faden) (fn : mD.Fn) (rho : Env mD (mD.params fn)) (s0 : World mD)
    (log : List (RufEreignisF mD)) (e : Expr mD [] mL (.int 0 100))
    (hp : RufPasst mD (vertragVon mD fn) (mD.signatur mSetze) mL)
    (h : ∀ K, Res.held K ∈ ([] : List (Res mD)) → mD.rang K < mD.rang ())
    (k : GRest mD (vertragVon mD fn) false [] []) (σ : World mD)
    (hz : ZustandG M t [] fn rho s0 log .nil
      (.dann (.cons (.locks () h (.cons (.call mSetze (.cons e .nil) hp rfl) .nil)) .nil) k) σ)
    (hoff : offen σ.spur = []) (hfrei : RufFreiG M t ()) :
    ∃ M' : RufMaschineG mD, RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M' ∧
      (∀ u, u ≠ t → M'.faeden u = M.faeden u) ∧
      ∃ (σ' : World mD) (log' : List (RufEreignisF mD)),
        ZustandG M' t [] fn rho s0 log' .nil k σ' ∧ offen σ'.spur = [] ∧
        (∀ ev, ev ∈ log → ev ∈ log') ∧
        ∃ (r : Env mD (mD.params mSetze)) (v : ErgVal mD (mD.erg mSetze)) (a b : World mD),
          RufEreignisF.rueck mSetze r v a b ∈ log' := by
  have hoff0 : offen (M.faeden t).spur = [] := by rw [hz.spur]; exact hoff
  obtain ⟨M1, s1, hZ1⟩ := w_locks (P := mP) (O := mO) (passes := 0) hz.1 ()
    _ _ _ _ _ rfl (mhg0 hoff) hfrei
  have hoff1 : offen (M1.faeden t).spur = [()] := by
    rw [hZ1.spur]
    exact congrArg (List.cons ()) hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_rufDann (P := mP) (O := mO) (passes := 0) hZ1.1 mSetze
    (.cons e .nil) hp rfl .nil _ _ rfl (mhgL (moff_z hZ1 hoff1)).heldIn
  have hoff2 : offen (M2.faeden t).spur = [()] := by
    rw [hZ2.spur, (Erw.lese _ _ _).offen]; exact hoff1
  obtain ⟨M3, s3, hZ3⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ2.1
    _ _ _ rfl rfl (mhgL (moff_z hZ2 hoff2)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff3 : offen (M3.faeden t).spur = [()] := by
    rw [hZ3.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ3.1
    _ _ _ rfl rfl (mhgL (moff_z hZ3 hoff3)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden t).spur = [()] := by
    rw [hZ4.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff3
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := mP) (O := mO) (passes := 0) hZ4.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (mhgL (moff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden t).spur = [()] := by
    rw [hG5.1]
    exact ((Erw.lese _ _ _).offen).trans hoff4
  obtain ⟨M6, s6, hZ6⟩ := w_dannLeer (P := mP) (O := mO) (passes := 0) hG5.1 _ _ rfl
  obtain ⟨M7, s7, hZ7⟩ := w_freiGib (P := mP) (O := mO) (passes := 0) hZ6.1 () _ _ rfl
  obtain ⟨M8, s8, hZ8⟩ := w_dannLeer (P := mP) (O := mO) (passes := 0) hZ7.1 _ _ rfl
  have hr8 : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M8 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ hr s1) s2) s3) s4) s5) s6) s7) s8
  have hfremd : ∀ u, u ≠ t → M8.faeden u = M.faeden u := by
    intro u hu
    rw [rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu, rufSchrittG_fremd s6 u hu,
      rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu, rufSchrittG_fremd s3 u hu,
      rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu]
  refine ⟨M8, hr8, hfremd, _, _, hZ8, ?_, fun ev hev => ?_, _, _, _, _, List.mem_cons_self⟩
  · show offen (M7.faeden t).spur = []
    rw [hZ7.spur]
    show (offen (M6.faeden t).spur).erase () = []
    rw [hZ6.spur]
    show (offen (M5.faeden t).spur).erase () = []
    rw [hoff5]
    rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hev)

theorem mStart_offen (t : Faden) : offen ((RufStartG mP mSp mInit).faeden t).spur = [] := by
  rw [start_faden]
  show offen (startSpur (mInit t).1) = []
  rw [startSpur, mInit_leer t]
  rfl

theorem mStart0 : (RufStartG mP mSp mInit).faeden 0 = ⟨[], ⟨mHauptA, .nil, mSp.welt [],
    ⟨false, [], [], .nil, .ende mRumpfA⟩⟩, [], [RufEreignisF.eintritt mHauptA .nil (mSp.welt [])]⟩ :=
  rfl

theorem mStart1 : (RufStartG mP mSp mInit).faeden 1 = ⟨[], ⟨mHauptB, .nil, mSp.welt [],
    ⟨false, [], [], .nil, .ende mRumpfB⟩⟩, [], [RufEreignisF.eintritt mHauptB .nil (mSp.welt [])]⟩ :=
  rfl

theorem mBlattOffen {σ : World mD} {Λ Λ' : List (Res mD)} {os : List (mD.Tab ⊕ mD.Glob)}
    {t : mD.Tab} {k : Int} {f : mD.Feld t} {v : Wert mD (mD.typ t f)} :
    offen ((σ.lese Λ os).schreibSlot t Λ' k f v).spur = offen σ.spur :=
  ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen

theorem mHeld0 (o : List mD.Lock) : HeldIn ([] : List (Res mD)) o := fun _ h => nomatch h

/-- **The prefix of the run**: thread 0 writes `privA` twice and stands at
    its `locks`; thread 1 writes `privB` and stands at its `locks`. -/
theorem mVorlauf : ∃ (M : RufMaschineG mD) (σ0 σ1 : World mD) (log0 log1 : List (RufEreignisF mD)),
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M ∧
    ZustandG M 0 [] mHauptA .nil (mSp.welt []) log0 .nil
      (.dann (.cons mLocksA .nil) (.ende mRestA)) σ0 ∧ offen σ0.spur = [] ∧
    ZustandG M 1 [] mHauptB .nil (mSp.welt []) log1 .nil
      (.dann (.cons mLocksB .nil) (.ende (.ret .keine List.Perm.nil))) σ1 ∧ offen σ1.spur = [] ∧
    ∀ u, u ≠ 0 → u ≠ 1 → M.faeden u = (RufStartG mP mSp mInit).faeden u := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP) (O := mO) (passes := 0) mStart0
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := mP) (O := mO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M3, s3, hZ3⟩ := w_endeEntf (P := mP) (O := mO) (passes := 0) hZ2.1 mLocksA mRestA
    .nil rfl rfl
  have h1 : M3.faeden 1 = (RufStartG mP mSp mInit).faeden 1 := by
    rw [rufSchrittG_fremd s3 1 (by decide), rufSchrittG_fremd s2 1 (by decide),
      rufSchrittG_fremd s1 1 (by decide)]
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := mP) (O := mO) (passes := 0) (h1.trans mStart1)
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  obtain ⟨M5, s5, hZ5⟩ := w_endeEntf (P := mP) (O := mO) (passes := 0) hZ4.1 mLocksB
    (.ret .keine List.Perm.nil) .nil rfl rfl
  have hr5 : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M5 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3)
      s4) s5
  have h0 : M5.faeden 0 = M3.faeden 0 := by
    rw [rufSchrittG_fremd s5 0 (by decide), rufSchrittG_fremd s4 0 (by decide)]
  refine ⟨M5, M5.speicher.welt (M2.weltVon 0).spur, _, _, _, hr5, ⟨h0.trans hZ3.1, rfl⟩, ?_,
    hZ5, ?_, fun u hu0 hu1 => ?_⟩
  · show offen (M2.faeden 0).spur = []
    rw [hZ2.spur]; refine mBlattOffen.trans ?_
    show offen (M1.faeden 0).spur = []
    rw [hZ1.spur]; refine mBlattOffen.trans ?_
    exact mStart_offen 0
  · show offen (M4.faeden 1).spur = []
    rw [hZ4.spur]; refine mBlattOffen.trans ?_
    show offen (M3.faeden 1).spur = []
    rw [h1]
    exact mStart_offen 1
  · rw [rufSchrittG_fremd s5 u hu1, rufSchrittG_fremd s4 u hu1, rufSchrittG_fremd s3 u hu0,
      rufSchrittG_fremd s2 u hu0, rufSchrittG_fremd s1 u hu0]

/-- A thread standing at `locks`, read off its state. -/
theorem anSperre_von {D : Deklaration} {M : RufMaschineG D} {t : Faden} {S : List (RufRahmenG D)}
    {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {l : Bool} {Γ : Ctx}
    {Λ Λ'' : List (Res D)} {ρ : Env D Γ} {L : D.Lock} {hr : ∀ K, Res.held K ∈ Λ → D.rang K < D.rang L}
    {body : Block D (vertragVon D f) l Γ (Res.held L :: Λ) (Res.held L :: Λ)}
    {rest : Block D (vertragVon D f) l Γ Λ Λ''} {k : GRest D (vertragVon D f) l Γ Λ''}
    {sp : List (Ereignis D)} {log : List (RufEreignisF D)}
    (h : M.faeden t = ⟨S, ⟨f, rho, s0, ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩⟩, sp, log⟩) :
    AnSperre M t L := by
  unfold AnSperre
  rw [h]
  exact ⟨l, Γ, Λ, Λ'', ρ, hr, body, rest, k, rfl⟩

/-- The residue stands at a `locks` statement. -/
def GRest.istLocks {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .dann (.cons (.locks ..) _) _ => true
  | _ => false

theorem mFrei {M : RufMaschineG mD} {t : Faden} (h : ∀ g, g ≠ t → offen (M.faeden g).spur = []) :
    RufFreiG M t () := fun g hg hL => by rw [h g hg] at hL; exact List.not_mem_nil hL

/-- **`ziel_ort_mehrfaden_zeuge` -- two ACTIVE threads, private tables
    unguarded, one shared table under a lock with a non-trivial invariant.**
    On a reached run: thread 0 writes `privA` (unguarded), thread 1 writes
    `privB` (unguarded), thread 0 runs its critical section (`setze(30)`),
    then thread 1 runs its critical section (`setze(70)`, its return logged:
    `Mb`); then thread 0 calls `pruefeA` (`Mc`, one step of thread 0 after
    `Mb`) and `pruefeA`'s `requires privA[0] == 7` holds at the logged
    entry, BY THE THEOREM -- with a whole critical section of the other
    ACTIVE thread between the write and the check, and no guard on
    `privA`. Then `pruefeA` returns and thread 0 is finished (`Md`, item 2):
    at its final state `hauptA`'s `ensures privA[0] == 7` and its owed
    invariant `privA[0] == privA[1]` hold at the world its return reads, BY
    THE THEOREM (`StartEndeG`); thread 1 is finished too. -/
theorem ziel_ort_mehrfaden_zeuge : ∃ Mb Mc Md : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Mb ∧ RufSchrittG mP mO 0 Mb 0 Mc ∧
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Mc ∧
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Md ∧
    (∃ (r : Env mD (mD.params mSetze)) (v : ErgVal mD (mD.erg mSetze)) (a b : World mD),
      RufEreignisF.rueck mSetze r v a b ∈ (Mb.faeden 1).log) ∧
    (∃ (rho : Env mD (mD.params mPruefeA)) (s0 : World mD),
      RufEreignisF.eintritt mPruefeA rho s0 ∈ (Mc.faeden 0).log ∧
      ReqAmEintritt mP mPruefeA s0 rho ∧ (s0.slots MTab.privA 0 ()).n = 7) ∧
    FertigG Md 0 ∧ FertigG Md 1 ∧
    (∃ W : World mD, EnsAmRueck mP mHauptA (mSp.welt []) W .nil () ∧ InvAmRueck mP mHauptA W ∧
      (W.slots MTab.privA 0 ()).n = 7 ∧ (W.slots MTab.privA 0 ()).n = (W.slots MTab.privA 1 ()).n) := by
  obtain ⟨M, σ0, σ1, log0, log1, hr, hz0, hoff0, hz1, hoff1, hidle⟩ := mVorlauf
  have hfrei0 : RufFreiG M 0 () := mFrei fun g hg => by
    by_cases hg1 : g = 1
    · subst hg1; rw [hz1.spur]; exact hoff1
    · rw [hidle g hg hg1]; exact mStart_offen g
  obtain ⟨Ma, hra, hfremdA, σa, loga, hza, hoffa, _, _⟩ := mAbschnitt hr 0 mHauptA .nil
    (mSp.welt []) log0 m30 mHpSetzeA (fun _ h => nomatch h) (.ende mRestA) σ0 hz0 hoff0 hfrei0
  have hz1' : ZustandG Ma 1 [] mHauptB .nil (mSp.welt []) log1 .nil
      (.dann (.cons mLocksB .nil) (.ende (.ret .keine List.Perm.nil))) (Ma.speicher.welt σ1.spur) :=
    ⟨(hfremdA 1 (by decide)).trans hz1.1, rfl⟩
  have hfrei1 : RufFreiG Ma 1 () := mFrei fun g hg => by
    by_cases hg0 : g = 0
    · subst hg0; rw [hza.spur]; exact hoffa
    · rw [hfremdA g hg0, hidle g hg0 hg]; exact mStart_offen g
  obtain ⟨Mb, hrb, hfremdB, σb, logb, hzb, _, _, hrueck⟩ := mAbschnitt hra 1 mHauptB .nil
    (mSp.welt []) log1 m70 mHpSetzeB (fun _ h => nomatch h) (.ende (.ret .keine List.Perm.nil)) _
    hz1' hoff1 hfrei1
  have hza' : Mb.faeden 0 = ⟨[], ⟨mHauptA, .nil, mSp.welt [], ⟨false, [], [], .nil, .ende mRestA⟩⟩,
      σa.spur, loga⟩ := (hfremdB 0 (by decide)).trans hza.1
  obtain ⟨Mc, sc, hZc⟩ := w_rufEnde (P := mP) (O := mO) (passes := 0) hza' mPruefeA .nil
    mHpPruefe rfl (.ret .keine List.Perm.nil) .nil rfl (mHeld0 _)
  have hrc : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Mc := .schritt _ _ _ hrb sc
  obtain ⟨rho, w0, hm⟩ : ∃ (rho : Env mD (mD.params mPruefeA)) (w0 : World mD),
      RufEreignisF.eintritt mPruefeA rho w0 ∈ (Mc.faeden 0).log := by
    rw [hZc.1]
    exact ⟨_, _, List.mem_cons_self⟩
  have hreq := ((mP_zertifiziert 0 Mc hrc).1.1.1 0 _ hm).1 _ _ _ rfl
  obtain ⟨Md, sd, hGd⟩ := w_rueckP (P := mP) (O := mO) (passes := 0) hZc.1 _ [] rfl
    (PopArt.wie rfl) .keine List.Perm.nil .nil rfl (mHeld0 _)
  have hrd : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Md := .schritt _ _ _ hrc sd
  have h1d : Md.faeden 1 = Mb.faeden 1 := by
    rw [rufSchrittG_fremd sd 1 (by decide), rufSchrittG_fremd sc 1 (by decide)]
  have hSE := (mP_zertifiziert 0 Md hrd).2.1 0
  rw [hGd.1] at hSE
  obtain ⟨hE, hI⟩ := hSE rfl false [] [] .nil (.ende (.ret .keine List.Perm.nil)) .keine rfl
    ⟨_, Or.inl rfl⟩
  have hI' := hI () (List.mem_singleton_self _) rfl
  refine ⟨Mb, Mc, Md, hrb, sc, hrc, hrd, by rw [hzb.1]; exact hrueck, ⟨rho, w0, hm, hreq, of_decide_eq_true hreq⟩,
    ⟨by rw [hGd.1], by rw [hGd.1]; rfl⟩, ⟨by rw [h1d, hzb.1], by rw [h1d, hzb.1]; rfl⟩,
    _, hE, hI, of_decide_eq_true hE, of_decide_eq_true hI'⟩

/-- **`keine_verklemmungG_zeuge` -- the deadlock theorem on the two-writer
    program is not vacuous.** On a reached machine both threads stand at
    their `locks`; the rank invariant gives thread 1's step there BY THE
    THEOREM (`schritt_an_sperre`: only another holder could stop it). One
    step later thread 0 holds the lock and thread 1 WAITS for it
    (`WartetG`, unfinished); the theorem says that not every unfinished
    thread waits -- thread 0 does not. -/
theorem keine_verklemmungG_zeuge :
    (∃ M : RufMaschineG mD, RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M ∧
      AnSperre M 1 () ∧ ∃ M', RufSchrittG mP mO 0 M 1 M') ∧
    ∃ M : RufMaschineG mD, RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M ∧
      WartetG M 1 ∧ ¬ FertigG M 1 ∧ ¬ FertigG M 0 ∧ ¬ WartetG M 0 ∧
      ¬ ((∃ t, ¬ FertigG M t) ∧ ∀ t, ¬ FertigG M t → WartetG M t) := by
  obtain ⟨M, σ0, σ1, log0, log1, hr, hz0, hoff0, hz1, hoff1, hidle⟩ := mVorlauf
  have hA1 : AnSperre M 1 () := anSperre_von hz1.1
  have hfrei1 : RufFreiG M 1 () := mFrei fun g hg => by
    by_cases hg0 : g = 0
    · subst hg0; rw [hz0.spur]; exact hoff0
    · rw [hidle g hg0 hg]; exact mStart_offen g
  have hfrei0 : RufFreiG M 0 () := mFrei fun g hg => by
    by_cases hg1 : g = 1
    · subst hg1; rw [hz1.spur]; exact hoff1
    · rw [hidle g hg hg1]; exact mStart_offen g
  refine ⟨⟨M, hr, hA1, schritt_an_sperre (mP_rang M hr 1) hA1 hfrei1⟩, ?_⟩
  obtain ⟨Ms, ss, hZs⟩ := w_locks (P := mP) (O := mO) (passes := 0) hz0.1 ()
    _ _ _ _ _ rfl (mhg0 hoff0) hfrei0
  have hrs : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Ms := .schritt _ _ _ hr ss
  have hs1 : Ms.faeden 1 = M.faeden 1 := rufSchrittG_fremd ss 1 (by decide)
  have hoff0' : offen (M.faeden 0).spur = [] := by rw [hz0.spur]; exact hoff0
  have hoffs : offen (Ms.faeden 0).spur = [()] := by
    rw [hZs.spur]
    exact congrArg (List.cons ()) hoff0'
  have hW : WartetG Ms 1 :=
    ⟨⟨(), anSperre_von (hs1.trans hz1.1)⟩, fun L _ => ⟨0, by decide, by
      cases L; rw [hoffs]; exact List.mem_cons_self⟩⟩
  have hF1 : ¬ FertigG Ms 1 := fun h => by
    have := h.2
    rw [hs1, hz1.1] at this
    exact Bool.false_ne_true this
  have hF0 : ¬ FertigG Ms 0 := fun h => by
    have := h.2
    rw [hZs.1] at this
    exact Bool.false_ne_true this
  have hW0 : ¬ WartetG Ms 0 := fun h => by
    obtain ⟨L, l, Γ, Λ, Λ'', ρ, hr', body, rest, k, hk⟩ := h.1
    have := congrArg (fun x => x.2.2.2.2.istLocks) hk
    simp only [GRest.istLocks] at this
    rw [hZs.1] at this
    exact Bool.false_ne_true this
  exact ⟨Ms, hrs, hW, hF1, hF0, hW0, keine_verklemmungG' mO_gut mP_stufen mSp mInit mInit_leer [()]
    (fun L => by cases L; exact List.mem_singleton_self _) hrs⟩

#print axioms Gabbro.Grammatik.mAbschnitt
#print axioms Gabbro.Grammatik.ziel_ort_mehrfaden_zeuge
#print axioms Gabbro.Grammatik.keine_verklemmungG_zeuge

end Gabbro.Grammatik
