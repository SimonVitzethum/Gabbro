/- Part 2 of 2 of `ZielOrtSperreZeuge` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtSperreZeuge.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1

namespace Gabbro.Grammatik

theorem sHp : RufPasst sD (vertragVon sD sHaupt) (sD.signatur sSetze) sL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (by
    intro L
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)
  hx := RufPasst.hx_von (by
    intro L
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)

/-- The call `setze(x)` inside the lock. -/
def sRuf : Stmt sD (vertragVon sD sHaupt) false [.int 0 100] sL sL :=
  .call sSetze (.cons (.var .here) .nil) sHp rfl

/-- `haupt(x)`: `locks { setze(x) }; return`. -/
def sRumpfHaupt : Endblock sD (vertragVon sD sHaupt) false [.int 0 100] [] :=
  .cons (.locks () (fun _ h => nomatch h) (.cons sRuf .nil)) (.ret .empty List.Perm.nil)

/-- The two-writer program. -/
def sP : Programm sD where
  invariante := fun i => nomatch i
  requires
    | .setze => sReqSetze
    | .haupt => .tru
  ensures
    | .setze => sEnsSetze
    | .haupt => .tru
  rumpf
    | .setze => sRumpfSetze
    | .haupt => sRumpfHaupt

def sFs : List sD.Fn := [sSetze, sHaupt]

theorem sFs_voll : ∀ g : sD.Fn, g ∈ sFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **The lock invariant `konto[0] == konto[1]`**, protecting `konto`. -/
def sS : SperrInv sD :=
  ⟨fun _ => [.inl ()], fun _ s => decide ((s.slots () 0 ()).n = (s.slots () 1 ()).n)⟩

theorem sS_ok : SperrInvOk sS := by
  refine ⟨fun L c hc => ?_, fun L s s' h => ?_⟩
  · cases L
    rw [List.mem_singleton.mp hc]
    exact List.mem_singleton.mpr rfl
  · have e : s.slots () = s'.slots () := h (.inl ()) List.mem_cons_self
    show decide ((s.slots () 0 ()).n = (s.slots () 1 ()).n) =
      decide ((s'.slots () 0 ()).n = (s'.slots () 1 ()).n)
    rw [e]

theorem sP_fussS : fussSperreB sP sS sFs = true := by decide

/-- The old check refuses the program: `haupt`'s callee contract reads the
    protected table outside any signature lock. -/
theorem sP_fussG_falsch : fussOrtGB sP sFs = false := by decide

theorem sP_fragmentG : programmImFragmentG sP sFs = true := by decide

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def sO : Orakel sD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem sO_gut : GutO sO := fun a => nomatch a

theorem sO_lokal : RegLokal sO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

/-- The start memory: `konto` all zero. -/
def sSp : Speicher sD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

def sWert (n : Int) (h0 : 0 ≤ n) (h1 : n ≤ 100) : Env sD [.int 0 100] := .cons ⟨n, h0, h1⟩ .nil

/-- The argument of thread `t`: `30` for thread `0`, `70` for every other. -/
def sArg (t : Faden) : Env sD [.int 0 100] :=
  if t = 0 then sWert 30 (by decide) (by decide) else sWert 70 (by decide) (by decide)

/-- Thread `0` runs `haupt(30)`, every other thread `haupt(70)`: at least
    two threads write the same table under the same lock. -/
def sInit : Faden → Σ f : sD.Fn, Env sD (sD.params f) :=
  fun t => ⟨sHaupt, sArg t⟩

theorem sP_start : StartGut sP sSp sInit := fun _ => rfl

/-- `haupt` holds no lock by signature: the start is exclusive although
    every thread runs the same routine. -/
theorem sInit_exklusiv : StartExklusiv (D := sD) sInit :=
  fun _ _ _ _ h => nomatch h

theorem sS_start : ∀ L, sS.inv L sSp = true := fun _ => rfl

/-- `setze` meets its obligation: after the two writes both slots are `x`. -/
theorem sP_koerper_setze : KoerperGutS sP 0 (axWahr sD) sS sSetze := by
  have hr : sP.rumpf sSetze = sRumpfSetze := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [sRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      show wahr? (eval σ sEnsSetze _ (ergEnv (sD.erg sSetze) () (Env.cons x Env.nil))) = true
      simp only [wahr?, sEnsSetze, sGleich, sIdx0, sIdx1, World.lese, World.merke, World.schreibSlot,
  World.storeSlot, List.map_append, List.append_assoc, eval, Zahl.weiter, dite_eq_ite, List.cons_append,
  List.nil_append, ergEnv, Int.reduceEq, ↓reduceIte, ite_self, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, rfl⟩
  · rw [hr] at hrun
    simp only [sRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [sRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun

/-- The `requires` of `setze` IS the lock invariant at the call world. -/
theorem sReq_iff_inv (κ : World sD) (ρk : Env sD (sD.params sSetze)) :
    ReqAmEintritt sP sSetze κ ρk ↔ sS.inv () κ.speicher = true := Iff.rfl

/-- The `ensures` of `setze` gives the lock invariant back. -/
theorem sInv_of_ens {κ σ2 : World sD} {ρk : Env sD (sD.params sSetze)}
    {v : ErgVal sD (sD.erg sSetze)} (h : EnsAmRueck sP sSetze κ σ2 ρk v) :
    sS.inv () σ2.speicher = true := by
  have h' : (decide ((σ2.slots () 0 ()).n = (σ2.slots () 1 ()).n) &&
      decide ((σ2.slots () 0 ()).n = (ρk.get .here).n)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1

/-- **`haupt` meets its obligation -- using the lock invariant twice.** At
    the acquire the environment's move leaves `konto[0] == konto[1]`, which
    IS `setze`'s `requires` (the caller duty); at the release `setze`'s
    `ensures` gives the invariant back (the release check). -/
theorem sP_koerper_haupt : KoerperGutS sP 0 (axWahr sD) sS sHaupt := by
  have hr : sP.rumpf sHaupt = sRumpfHaupt := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [sRumpfHaupt, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := sS) (O := O') (U := U) (passes := 0) (R := torRuf sP R)
      (l := false) (Γ := [.int 0 100]) sSetze (.cons (.var .here) .nil) sHp rfl
      ((U () σ).nimmt ()) ρ with ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · cases hi : sS.inv () σ1.speicher with
      | true =>
          simp only [freiH, hi, if_true] at hrun
          cases hrun
      | false =>
          simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun
          cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have hreq : ReqAmEintritt sP sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .here) .nil) := (hU () σ).2.2
      have htor : torRuf sP R sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .here) .nil) =
          R sSetze (((U () σ).nimmt ()).lese sL []) (Env.cons (ρ.get .here) .nil) := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun
      cases hrun
  · rw [hr] at hrun
    simp only [sRumpfHaupt, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := sS) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := [.int 0 100]) sSetze (.cons (.var .here) .nil) sHp rfl
      ((U () σ).nimmt ()) ρ with ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hreq : ReqAmEintritt sP sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .here) .nil) := (hU () σ).2.2
      have hinv := sInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun
      cases hrun

theorem sP_koerper : ∀ f : sD.Fn, KoerperGutS sP 0 (axWahr sD) sS f := by
  intro f
  cases f
  · exact sP_koerper_setze
  · exact sP_koerper_haupt

/-- **All premises of `ziel_ort_sperre` hold jointly on the two-writer
    program**, hence its conclusion on every reachable machine. -/
theorem sP_zertifiziert : ∀ M : RufMaschineG sD,
    RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M →
      VertragAmOrtG sP M ∧ SperrInvG sS M ∧ KeinLogikHaltG sO 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG sP sO 0 M t M' :=
  ziel_ort_sperre sP sO 0 (axWahr sD) sS sFs sSp sInit sO_gut sO_lokal (axVertragO_wahr sO)
    axEnsLokal_wahr sS_ok sFs_voll sP_fragmentG sP_fussS sP_koerper sP_start sS_start sInit_exklusiv

/-! ### The run: two critical sections on one table -/

/-- The start thread state of a thread running `haupt(x)`. -/
def sZ0 (ρ : Env sD [.int 0 100]) : RufFadenG sD :=
  ⟨[], ⟨sHaupt, ρ, sSp.welt [], ⟨false, [.int 0 100], [], ρ, .ende sRumpfHaupt⟩⟩, [],
    [RufEreignisF.eintritt sHaupt ρ (sSp.welt [])]⟩

theorem sM0_faden0 :
    (RufStartG sP sSp sInit).faeden 0 = sZ0 (sWert 30 (by decide) (by decide)) := rfl

theorem sM0_faden (t : Faden) (ht : t ≠ 0) :
    (RufStartG sP sSp sInit).faeden t = sZ0 (sWert 70 (by decide) (by decide)) := by
  have e : sArg t = sWert 70 (by decide) (by decide) := if_neg ht
  show (⟨[], ⟨sHaupt, sArg t, sSp.welt [], ⟨false, sD.params sHaupt,
      Signatur.anfang sD (sD.signatur sHaupt), sArg t, .ende (sP.rumpf sHaupt)⟩⟩, startSpur sHaupt,
      [RufEreignisF.eintritt sHaupt (sArg t) (sSp.welt [])]⟩ : RufFadenG sD) = _
  rw [e]
  rfl

theorem sOffen_weltVon (M : RufMaschineG sD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := rfl

theorem sM0_offen (t : Faden) : offen ((RufStartG sP sSp sInit).faeden t).spur = [] := by
  by_cases ht : t = 0
  · subst ht; rfl
  · rw [sM0_faden t ht]; rfl

theorem shgL {s : List (Ereignis sD)} (h : offen s = [()]) : HeldGenau sL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem shg0 {s : List (Ereignis sD)} (h : offen s = []) :
    HeldGenau ([] : List (Res sD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem soff_z {M : RufMaschineG sD} {f : Faden} {stapel : List (RufRahmenG sD)} {fn : sD.Fn}
    {rho : Env sD (sD.params fn)} {s0 : World sD} {log : List (RufEreignisF sD)} {l : Bool}
    {Γ : Ctx} {Λ : List (Res sD)} {ρ : Env sD Γ} {r : GRest sD (vertragVon sD fn) l Γ Λ}
    {σ : World sD} {x : List sD.Lock} (h : ZustandG M f stapel fn rho s0 log ρ r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [← h.spur]; exact ho

theorem soff_g {M : RufMaschineG sD} {f : Faden} {caller : RufRahmenG sD}
    {rst : List (RufRahmenG sD)} {fn : sD.Fn} {rho : Env sD (sD.params fn)} {s0 : World sD}
    {log : List (RufEreignisF sD)} {v : ErgVal sD (sD.erg fn)} {σ : World sD} {x : List sD.Lock}
    (h : GepopptG M f caller rst fn rho s0 log v σ) (ho : offen (M.faeden f).spur = x) :
    offen σ.spur = x := by
  rw [h.1] at ho; exact ho

/-- The `locks` statement of `haupt`. -/
def sLocks : Stmt sD (vertragVon sD sHaupt) false [.int 0 100] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons sRuf .nil)

def sHauptRet : Endblock sD (vertragVon sD sHaupt) false [.int 0 100] [] := .ret .empty List.Perm.nil

/-- **One critical section of a thread `t` running `haupt(x)`**: eight
    steps from its start state -- take the lock, call `setze(x)`, both
    writes, return, release. Nothing else moves. -/
theorem sAbschnitt {M : RufMaschineG sD} (hr : RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M)
    (t : Faden) (x : Env sD [.int 0 100]) (hz : M.faeden t = sZ0 x)
    (hfrei : RufFreiG M t ()) :
    ∃ M' : RufMaschineG sD, RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M' ∧
      (∀ u, u ≠ t → M'.faeden u = M.faeden u) ∧ offen (M'.faeden t).spur = [] ∧
      (M'.speicher.slots () 0 ()).n = (x.get .here).n ∧
      (M'.speicher.slots () 1 ()).n = (x.get .here).n ∧
      (∃ s0 : World sD, RufEreignisF.eintritt sSetze (Env.cons (x.get .here) .nil) s0 ∈
          (M'.faeden t).log ∧ s0.speicher = M.speicher) ∧
      (∃ (v : ErgVal sD (sD.erg sSetze)) (s0 s1 : World sD),
          RufEreignisF.rueck sSetze (Env.cons (x.get .here) .nil) v s0 s1 ∈ (M'.faeden t).log ∧
          (s1.slots () 0 ()).n = (x.get .here).n) := by
  have hoff0 : offen (M.faeden t).spur = [] := by rw [hz]; rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := sP) (O := sO) (passes := 0) hz sLocks sHauptRet
    x rfl rfl
  have hfrei1 : RufFreiG M1 t () := by
    intro u hu
    rw [rufSchrittG_fremd s1 u hu]
    exact hfrei u hu
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := sP) (O := sO) (passes := 0) hZ1.1 ()
    _ _ _ _ x rfl (shg0 (by show offen (M.faeden t).spur = []; exact hoff0)) hfrei1
  have hoff2 : offen (M2.faeden t).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon t).spur) :: (M1.weltVon t).spur) = [()]
    simp only [offen]
    rw [sOffen_weltVon, hZ1.spur, sOffen_weltVon, hoff0]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := sP) (O := sO) (passes := 0) hZ2.1 sSetze
    (.cons (.var .here) .nil) sHp rfl .nil _ x rfl (shgL (soff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden t).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := sP) (O := sO) (passes := 0) hZ3.1
    _ _ _ rfl rfl (shgL (soff_z hZ3 hoff3)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden t).spur = [()] := by
    rw [hZ4.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_blatt (P := sP) (O := sO) (passes := 0) hZ4.1
    _ _ _ rfl rfl (shgL (soff_z hZ4 hoff4)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff5 : offen (M5.faeden t).spur = [()] := by
    rw [hZ5.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := sP) (O := sO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (shgL (soff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden t).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_dannLeer (P := sP) (O := sO) (passes := 0) hG6.1 _ _ rfl
  obtain ⟨M8, s8, hZ8⟩ := w_freiGib (P := sP) (O := sO) (passes := 0) hZ7.1 () _ _ rfl
  have hr8 : RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M8 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ hr s1) s2) s3) s4) s5) s6) s7) s8
  have hfremd : ∀ u, u ≠ t → M8.faeden u = M.faeden u := by
    intro u hu
    rw [rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu, rufSchrittG_fremd s6 u hu,
      rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu, rufSchrittG_fremd s3 u hu,
      rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu]
  have e8 : M8.speicher = M6.speicher := by
    rw [hZ8.2]
    show M7.speicher = M6.speicher
    rw [hZ7.2]
    rfl
  have e6 : M6.speicher = M5.speicher := by rw [hG6.2]; rfl
  have e3 : M3.speicher = M.speicher := by
    rw [hZ3.2]
    show M2.speicher = M.speicher
    rw [hZ2.2]
    show M1.speicher = M.speicher
    rw [hZ1.2]
    rfl
  refine ⟨M8, hr8, hfremd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hZ8.spur]
    show (offen (M7.weltVon t).spur).erase () = []
    show (offen (M7.faeden t).spur).erase () = []
    rw [hZ7.spur]
    show (offen (M6.faeden t).spur).erase () = []
    rw [hoff6]
    rfl
  · rw [e8, e6]
    have e54 : M5.speicher.slots () 0 () = M4.speicher.slots () 0 () := by rw [hZ5.2]; rfl
    rw [e54, hZ4.2]
    rfl
  · rw [e8, e6, hZ5.2]
    rfl
  · refine ⟨(M2.weltVon t).lese sL [], ?_, ?_⟩
    · rw [hZ8.1]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · show M2.speicher = M.speicher
      rw [hZ2.2]
      show M1.speicher = M.speicher
      rw [hZ1.2]
      rfl
  · refine ⟨(), (M2.weltVon t).lese sL [], (M5.weltVon t).lese sL [], ?_, ?_⟩
    · rw [hZ8.1]
      exact List.mem_cons_self
    · show (M5.speicher.slots () 0 ()).n = _
      have e54 : M5.speicher.slots () 0 () = M4.speicher.slots () 0 () := by rw [hZ5.2]; rfl
      rw [e54, hZ4.2]
      rfl

/-- **`ziel_ort_sperre_zeuge` -- TWO THREADS WRITE THE SAME TABLE UNDER ONE
    LOCK, and the contracts that depend on the lock invariant hold where
    they are claimed.** Every premise of `ziel_ort_sperre` holds on `sP`
    (`sP_zertifiziert`). On a reached run of sixteen steps thread 0
    (`haupt(30)`) takes the lock, `setze(30)` writes both slots, releases;
    then thread 1 (`haupt(70)`, the SAME routine) takes the lock and enters
    `setze(70)` at a world holding what thread 0 wrote (`30`, `30`) -- and
    `setze`'s `requires konto[0] == konto[1]` holds there, BY THE THEOREM
    (thread 1's own proof of it came from the invariant at the acquire);
    `setze(70)` returns with its `ensures` (`70`, `70`), BY THE THEOREM; at
    the end no thread holds the lock and its invariant holds in memory, BY
    THE THEOREM. -/
theorem ziel_ort_sperre_zeuge : ∃ M M' : RufMaschineG sD,
    RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M ∧
    RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M' ∧
    (sSp.slots () 0 ()).n = 0 ∧
    (M.speicher.slots () 0 ()).n = 30 ∧ (M.speicher.slots () 1 ()).n = 30 ∧
    (∃ (v : ErgVal sD (sD.erg sSetze)) (s0 s1 : World sD),
      RufEreignisF.rueck sSetze (sWert 30 (by decide) (by decide)) v s0 s1 ∈ (M'.faeden 0).log) ∧
    (∃ s0 : World sD,
      RufEreignisF.eintritt sSetze (sWert 70 (by decide) (by decide)) s0 ∈ (M'.faeden 1).log ∧
      (s0.slots () 0 ()).n = 30 ∧ (s0.slots () 1 ()).n = 30 ∧
      ReqAmEintritt sP sSetze s0 (sWert 70 (by decide) (by decide))) ∧
    (∃ (v : ErgVal sD (sD.erg sSetze)) (s0 s1 : World sD),
      RufEreignisF.rueck sSetze (sWert 70 (by decide) (by decide)) v s0 s1 ∈ (M'.faeden 1).log ∧
      EnsAmRueck sP sSetze s0 s1 (sWert 70 (by decide) (by decide)) v ∧ (s1.slots () 0 ()).n = 70) ∧
    (∀ t : Faden, (() : sD.Lock) ∉ offen (M'.faeden t).spur) ∧ sS.inv () M'.speicher = true := by
  have hfrei0 : RufFreiG (RufStartG sP sSp sInit) 0 () := fun u _ h => by
    rw [sM0_offen u] at h
    exact List.not_mem_nil h
  obtain ⟨M, hrM, hfremdM, hoffM, h0M, h1M, _, ⟨v0, a0, b0, hr0, _⟩⟩ :=
    sAbschnitt .start 0 _ sM0_faden0 hfrei0
  have hz1 : M.faeden 1 = sZ0 (sWert 70 (by decide) (by decide)) := by
    rw [hfremdM 1 (by decide)]
    exact sM0_faden 1 (by decide)
  have hfrei1 : RufFreiG M 1 () := by
    intro u hu h
    by_cases hu0 : u = 0
    · subst hu0
      rw [hoffM] at h
      exact List.not_mem_nil h
    · rw [hfremdM u hu0, sM0_offen u] at h
      exact List.not_mem_nil h
  obtain ⟨M', hrM', hfremdM', hoffM', _, _, ⟨s0, hent, hs0⟩, ⟨v1, c0, c1, hr1, hc1⟩⟩ :=
    sAbschnitt hrM 1 _ hz1 hfrei1
  have hZ := sP_zertifiziert M' hrM'
  have hreq := (hZ.1 1 _ hent).1 _ _ _ rfl
  have hens := (hZ.1 1 _ hr1).2 _ _ _ _ _ rfl
  have hfreiE : ∀ t : Faden, (() : sD.Lock) ∉ offen (M'.faeden t).spur := by
    intro t h
    by_cases ht1 : t = 1
    · subst ht1
      rw [hoffM'] at h
      exact List.not_mem_nil h
    · rw [hfremdM' t ht1] at h
      by_cases ht0 : t = 0
      · subst ht0
        rw [hoffM] at h
        exact List.not_mem_nil h
      · rw [hfremdM t ht0, sM0_offen t] at h
        exact List.not_mem_nil h
  refine ⟨M, M', hrM, hrM', rfl, h0M, h1M, ⟨v0, a0, b0, ?_⟩, ⟨s0, hent, ?_, ?_, hreq⟩,
    ⟨v1, c0, c1, hr1, hens, hc1⟩, hfreiE, hZ.2.1 () hfreiE⟩
  · rw [hfremdM' 0 (by decide)]
    exact hr0
  · show (s0.speicher.slots () 0 ()).n = 30
    rw [hs0]
    exact h0M
  · show (s0.speicher.slots () 1 ()).n = 30
    rw [hs0]
    exact h1M

/-! ## 5. Corpus 104 through the new theorem; probe A -/

/-- **`ziel_ort_sperre_ref104` -- `beispiele/104-referenz.gab` certified by
    the goal theorem with lock invariants** (the empty family: 104 takes its
    lock by signature): all premises jointly, the conclusion on every
    reachable machine, and on the reached run of `r4Lauf` the `ensures` of
    `einzahlen` at its logged return. -/
theorem ziel_ort_sperre_ref104 :
    fussSperreB r4P (SperrInv.leer r4D) r4Fs = true ∧
    (∀ f : r4D.Fn, KoerperGutS r4P 0 (axWahr r4D) (SperrInv.leer r4D) f) ∧
    (∀ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M →
      VertragAmOrtG r4P M ∧ SperrInvG (SperrInv.leer r4D) M ∧ KeinLogikHaltG r4O 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG r4P r4O 0 M t M') ∧
    ∃ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
      (r4Sp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
        RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck r4P r4Ein s0 s1 rho ()) := by
  have hF := fussSperreB_of_G r4P (SperrInv.leer r4D) r4Fs r4P_fussG
  have hK : ∀ f : r4D.Fn, KoerperGutS r4P 0 (axWahr r4D) (SperrInv.leer r4D) f :=
    fun f => koerperGutS_leer (r4P_koerperZ f)
  have hZ := ziel_ort_sperre r4P r4O 0 (axWahr r4D) (SperrInv.leer r4D) r4Fs r4Sp r4Init
    r4O_gut r4O_lokal (axVertragO_wahr r4O) axEnsLokal_wahr sperrInvOk_leer r4Fs_voll
    r4P_fragmentG hF hK r4P_start (fun _ => rfl) r4Init_exklusiv
  obtain ⟨M, hr, hsp, ⟨rho, s0, s1, hlog⟩, _⟩ := r4Lauf
  exact ⟨hF, hK, hZ, M, hr, rfl, hsp, ⟨rho, s0, s1, hlog, ((hZ M hr).1 0 _ hlog).2 r4Ein rho () s0 s1 rfl⟩⟩

/-- **Probe A fails the new obligation too**, for every well-formed family
    whose invariants are satisfiable: the bodies of `paP` contain no
    `locks`, so the semantics with lock invariants runs them as `execEnd`
    does -- into `logik schleife`. -/
theorem paP_nicht_sperre (Q : AxEns zD) (S : SperrInv zD)
    (hS : ∀ L (s s' : Speicher zD), (∀ c ∈ S.orte L, TraegerGleich s s' c) →
      S.inv L s = S.inv L s') (s : Speicher zD)
    (hs : ∀ L, S.inv L s = true) (f : zD.Fn) : ¬ KoerperGutS paP 0 Q S f := by
  intro h
  have hl : (paP.rumpf f).ohneLocks = true := by cases f <;> rfl
  refine h.2 zO zO_rahmen zO_lokal (zO_vertrag Q) (fun L σ => mischU S L σ s)
    (havocOk_misch_lokal hS (fun _ _ => s) (fun L _ => hs L)) hwRuf (hwRuf_rahmen paP) hwRuf_ohneLogik
    (zSp.welt []) (by cases f <;> exact .nil) rfl .schleife ?_
  rw [Endblock.execH_ohne S zO _ 0 hwRuf _ hl]
  exact paP_lauf zO hwRuf f _ _

/-- **Probe A: the premise of the new goal theorem is refuted** (for the
    empty family, and for `zS`). -/
theorem paP_nicht_sperre_leer (Q : AxEns zD) :
    ¬ ∀ f : zD.Fn, KoerperGutS paP 0 Q (SperrInv.leer zD) f :=
  fun h => paP_nicht_sperre Q _ sperrInvOk_leer.2 zSp (fun _ => rfl) zHaupt (h zHaupt)

#print axioms Gabbro.Grammatik.zPB_zertifiziert
#print axioms Gabbro.Grammatik.zPB_lauf
#print axioms Gabbro.Grammatik.zPC_zertifiziert
#print axioms Gabbro.Grammatik.sP_zertifiziert
#print axioms Gabbro.Grammatik.ziel_ort_sperre_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_sperre_ref104
#print axioms Gabbro.Grammatik.paP_nicht_sperre
#print axioms Gabbro.Grammatik.paP_nicht_sperre_leer


end Gabbro.Grammatik
