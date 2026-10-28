/-
  File:      Grammatik/ZielOrtSperreZeuge.lean
  Subject:   WITNESSES AND PROBES for the goal theorem with lock invariants,
             `ziel_ort_sperre` (`ZielOrtSperre.lean`).

  1. Verdict probe B, reconstructed and CERTIFIED: `zP` (`ZielOrtZeuge.lean`)
     with `wrap`'s `ensures true` replaced by `konto[0] == 100` -- a contract
     over the lock-protected table at the lock boundary of `haupt`
     (`locks { wrap() }`). `fussOrtGB` is false (`zPB_fussG_falsch`, the
     finding); the new check passes with the lock `()` protecting `konto`
     (invariant `true`), every premise of `ziel_ort_sperre` holds, and on a
     reached run the `ensures` of `wrap` holds at its logged return, from the
     theorem.
  2. Verdict probe C, reconstructed and CERTIFIED: `haupt` reads the
     protected carrier inside its `locks` block
     (`locks { konto[0] = konto[0] }`).
  3. TWO THREADS WRITING THE SAME CARRIER UNDER ONE LOCK with a
     NON-TRIVIAL lock invariant (`konto[0] == konto[1]`) and a contract that
     depends on it: every thread runs `haupt(x) = locks { setze(x) }` (the
     same routine, no signature lock -- the start is exclusive); `setze`
     requires `konto[0] == konto[1]` (the caller can only prove it from the
     invariant it gets at the acquire) and ensures
     `konto[0] == konto[1] && konto[0] == x` (which re-establishes the
     invariant at the release). On a reached run thread 1 enters `setze` in
     the state thread 0 left: the `requires` holds there, from the theorem,
     over values thread 0 wrote.
  4. Corpus 104 through the new theorem (`ziel_ort_sperre_ref104`), and
     probe A refuted for the new obligation (`paP_nicht_sperre`).
-/
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge

namespace Gabbro.Grammatik

/-! ## 0. Helpers for concrete bodies -/

/-- A call statement, unfolded (the same in both semantics). -/
theorem execStmtH_call {D : Deklaration} {S : SperrInv D} {O : Orakel D} {U : Umwelt D}
    {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (σ : World D) (ρ : Env D Γ) :
    execStmtH S O U passes R (Stmt.call (l := l) g args hp hr) σ ρ =
      execStmt O passes R (Stmt.call (l := l) g args hp hr) σ ρ := rfl

/-- A call answered normally continues normally. -/
theorem execStmt_call_ok {D : Deklaration} {O : Orakel D} {passes : Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (v : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ' v) :
    execStmt O passes R (Stmt.call (l := l) g args hp hr) σ ρ = .ok σ' ρ := by
  simp only [execStmt, h]

/-- The outcomes of a call statement: a normal answer, or the handler's
    `logik`/`hardware` outcome passed through. -/
theorem execStmtH_call_fall {D : Deklaration} {S : SperrInv D} {O : Orakel D} {U : Umwelt D}
    {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (σ : World D) (ρ : Env D Γ) :
    (∃ σ' v, R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .ok σ' v ∧ execStmtH S O U passes R (Stmt.call (l := l) g args hp hr) σ ρ = .ok σ' ρ) ∨
    (∃ e, R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .logik e ∧ execStmtH S O U passes R (Stmt.call (l := l) g args hp hr) σ ρ = .logik e) ∨
    (∃ e, execStmtH S O U passes R (Stmt.call (l := l) g args hp hr) σ ρ = .hardware e) := by
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    with
  | ok σ' v => exact Or.inl ⟨σ', v, rfl, by simp only [execStmtH, hR]⟩
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => exact Or.inr (Or.inl ⟨e, rfl, by simp only [execStmtH, hR]⟩)
  | hardware e => exact Or.inr (Or.inr ⟨e, by simp only [execStmtH, hR]⟩)

/-- A `locks` block of one statement, unfolded: the statement runs from the
    environment's move of the acquire world, then the release check. -/
theorem execStmtH_locks_eins {D : Deklaration} {S : SperrInv D} {O : Orakel D} {U : Umwelt D}
    {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (s : Stmt D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) (σ : World D) (ρ : Env D Γ) :
    execStmtH S O U passes R (Stmt.locks L hr (.cons s .nil)) σ ρ =
      freiH S L (execStmtH S O U passes R s ((U L σ).nimmt L) ρ) := by
  show freiH S L (execBlockH S O U passes R (.cons s .nil) ((U L σ).nimmt L) ρ) = _
  rw [execBlockH_cons_laufA, laufAH_nil]

/-- The release check of an invariant `true`. -/
theorem freiH_wahr {D : Deklaration} {S : SperrInv D} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (L : D.Lock) (hS : ∀ s, S.inv L s = true) (o : Ausgang V l Γ) (e : Logik D)
    (h : freiH S L o = .logik e) : o = .logik e := by
  cases o <;> simp_all [freiH]

/-! ## 1. The family of lock invariants on `zD` -/

/-- The lock `()` protects `konto`; its invariant is `true`. -/
def zS : SperrInv zD := ⟨fun _ => [.inl ()], fun _ _ => true⟩

theorem zS_ok : SperrInvOk zS := by
  refine ⟨fun L c hc => ?_, fun _ _ _ _ => rfl⟩
  cases L
  rw [List.mem_singleton.mp hc]
  exact List.mem_singleton.mpr rfl

/-! ## 2. Probe B: a contract over the protected table at a lock boundary -/

/-- `einzahlen` ensures `konto[0] == 100` (it writes the cap). -/
def zEnsHundert : Expr zD (ErgCtx (zD.params zEin) (zD.erg zEin)) (vertragVon zD zEin).ende .bool :=
  .eq (.slot () () zIdx zDarf) zHundert

/-- **Probe B**: `wrap` ensures `konto[0] == 100`. -/
def zEnsWrapB :
    Expr zD (ErgCtx (zD.params zWrap) (zD.erg zWrap)) (vertragVon zD zWrap).ende .bool :=
  .eq (.slot () () zIdx zDarf) zHundert

/-- **The program of probe B**: the bodies of `zP`, `wrap` ensures
    `konto[0] == 100` (and `einzahlen` promises it). -/
def zPB : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures
    | .ein => zEnsHundert
    | .lies => zEnsLies
    | .wrap => zEnsWrapB
    | .haupt => .tru
  rumpf
    | .ein => zRumpfEin
    | .lies => zRumpfLies
    | .wrap => zRumpfWrap
    | .haupt => zRumpfHaupt

/-- **The finding of probe B**: the footprint check of `ziel_ort_ganz`
    fails (`haupt` holds no lock by signature, `wrap`'s contract reads
    `konto`, `einzahlen` writes it). -/
theorem zPB_fussG_falsch : fussOrtGB zPB zFs = false := by decide

/-- **The new check passes**: `konto` is protected by the invariant of its
    guard `()`. -/
theorem zPB_fussS : fussSperreB zPB zS zFs = true := by decide

theorem zPB_fragmentG : programmImFragmentG zPB zFs = true := by decide

theorem zPB_start : StartGut zPB zSp zInit := fun _ => rfl

theorem zPB_koerper_lies : KoerperGutS zPB 0 (axWahr zD) zS zLies := by
  have hr : zPB.rumpf zLies = zRumpfLies := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [zRumpfLies, execEndH, EndAusgang.schrumpf] at hrun
    cases hrun
    exact (decide_eq_true_eq).mpr rfl
  · rw [hr] at hrun
    simp only [zRumpfLies, execEndH, EndAusgang.schrumpf] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [zRumpfLies, execEndH, EndAusgang.schrumpf] at hrun
    cases hrun

theorem zPB_koerper_ein : KoerperGutS zPB 0 (axWahr zD) zS zEin := by
  have hr : zPB.rumpf zEin = zRumpfEin := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [zRumpfEin, execEndH, execStmtH] at hrun
    cases hrun
    rfl
  · rw [hr] at hrun
    simp only [zRumpfEin, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [zRumpfEin, execEndH, execStmtH] at hrun
    cases hrun

theorem zPB_koerper_wrap : KoerperGutS zPB 0 (axWahr zD) zS zWrap := by
  have hr : zPB.rumpf zWrap = zRumpfWrap := rfl
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [zRumpfWrap, execEndH] at hrun
    rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := R) (l := false) (Γ := [])
      zLies .nil zHpLies rfl σ ρ with ⟨σ1, v1, _, h1⟩ | ⟨e1, _, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only at hrun
      rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := R) (l := false) (Γ := [])
        zEin .nil zHpEin rfl σ1 ρ with ⟨σ2, v2, hR2, h2⟩ | ⟨e2, _, h2⟩ | ⟨e2, h2⟩ <;> erw [h2] at hrun
      · simp only at hrun
        cases hrun
        have hE := hR.1 _ _ _ (by rfl) _ _ hR2
        exact hE
      · cases hrun
      · cases hrun
    · cases hrun
    · cases hrun
  · rw [hr] at hrun
    simp only [zRumpfWrap, execEndH] at hrun
    rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := torRuf zPB R)
      (l := false) (Γ := []) zLies .nil zHpLies rfl σ ρ with ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;>
      erw [h1] at hrun
    · simp only at hrun
      rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := torRuf zPB R)
        (l := false) (Γ := []) zEin .nil zHpEin rfl σ1 ρ with ⟨σ2, v2, _, h2⟩ | ⟨e2, he2, h2⟩ | ⟨e2, h2⟩ <;>
        erw [h2] at hrun
      · cases hrun
      · cases hrun
        exact hOV _ _ _ _ he2 g rfl
      · cases hrun
    · cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · cases hrun
  · rw [hr] at hrun
    simp only [zRumpfWrap, execEndH] at hrun
    rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := R) (l := false) (Γ := [])
      zLies .nil zHpLies rfl σ ρ with ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only at hrun
      rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := R) (l := false) (Γ := [])
        zEin .nil zHpEin rfl σ1 ρ with ⟨σ2, v2, _, h2⟩ | ⟨e2, he2, h2⟩ | ⟨e2, h2⟩ <;> erw [h2] at hrun
      · cases hrun
      · cases hrun
        exact hOL _ _ _ _ he2
      · cases hrun
    · cases hrun
      exact hOL _ _ _ _ he1
    · cases hrun

/-- `haupt`: `locks () { wrap() }; return`. With the invariant `true` the
    release check never fails; the one call meets `requires true`. -/
theorem zPB_koerper_haupt : KoerperGutS zPB 0 (axWahr zD) zS zHaupt := by
  have hr : zPB.rumpf zHaupt = zRumpfHaupt := rfl
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [zRumpfHaupt, zLocksBody, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := torRuf zPB R)
      (l := false) (Γ := []) zWrap .nil zHpWrap rfl ((U () σ).nimmt ()) ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [freiH, zS, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · simp only [freiH] at hrun
      cases hrun
  · rw [hr] at hrun
    simp only [zRumpfHaupt, zLocksBody, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := zS) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) zWrap .nil zHpWrap rfl ((U () σ).nimmt ()) ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [freiH, zS, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun
      cases hrun

theorem zPB_koerper : ∀ f : zD.Fn, KoerperGutS zPB 0 (axWahr zD) zS f := by
  intro f
  cases f
  · exact zPB_koerper_ein
  · exact zPB_koerper_lies
  · exact zPB_koerper_wrap
  · exact zPB_koerper_haupt

/-- **Probe B is certified**: every premise of `ziel_ort_sperre` holds on
    `zPB`, so on every reachable machine `ensures konto[0] == 100` holds at
    every logged return of `wrap` (and every other contract at its place),
    the invariant of the free lock holds, and no `logik` check stops a
    thread. -/
theorem zPB_zertifiziert : ∀ M : RufMaschineG zD,
    RufErreichbarG zPB zO 0 (RufStartG zPB zSp zInit) M →
      VertragAmOrtG zPB M ∧ SperrInvG zS M ∧ KeinLogikHaltG zO 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG zPB zO 0 M t M' :=
  ziel_ort_sperre zPB zO 0 (axWahr zD) zS zFs zSp zInit zO_gut zO_lokal (axVertragO_wahr zO)
    axEnsLokal_wahr zS_ok zFs_voll zPB_fragmentG zPB_fussS zPB_koerper zPB_start (fun _ => rfl)
    zInit_exklusiv

theorem zPB_M0_faden (t : Faden) : (RufStartG zPB zSp zInit).faeden t = zZ0 := rfl

/-- **The run of probe B.** Ten steps of thread 1 from the start machine of
    `zPB`: take the lock, enter `wrap`, call `lies` and `einzahlen` (which
    writes `100`), return from both and from `wrap`. At `wrap`'s logged
    return its contract `konto[0] == 100` -- a contract over the protected
    table, at the lock boundary of `haupt` -- holds, BY THE THEOREM. -/
theorem zPB_lauf : ∃ M : RufMaschineG zD,
    RufErreichbarG zPB zO 0 (RufStartG zPB zSp zInit) M ∧
    ∃ (rho : Env zD (zD.params zWrap)) (v : ErgVal zD (zD.erg zWrap)) (s0 s1 : World zD),
      RufEreignisF.rueck zWrap rho v s0 s1 ∈ (M.faeden 1).log ∧
      EnsAmRueck zPB zWrap s0 s1 rho v ∧ (s1.slots () 0 ()).n = 100 := by
  have h01 := zPB_M0_faden (1 : Faden)
  have hoff0 : offen ((RufStartG zPB zSp zInit).faeden 1).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := zPB) (O := zO) (passes := 0) h01 zLocks zHauptRet
    .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := zPB) (O := zO) (passes := 0) hZ1.1 ()
    _ _ _ _ .nil rfl (hg0 hoff0)
    (fun u hu h => by rw [rufSchrittG_fremd s1 u hu, zPB_M0_faden] at h; exact List.not_mem_nil h)
  have hoff2 : offen (M2.faeden 1).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon 1).spur) :: (M1.weltVon 1).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ1.spur]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := zPB) (O := zO) (passes := 0) hZ2.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 1).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := zPB) (O := zO) (passes := 0) hZ3.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .empty (by rfl))) .nil rfl
    (hgL (hoff_z hZ3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := zPB) (O := zO) (passes := 0) hZ4.1
    (.slot () () zIdx zDarf) (.ret (.val (.var .here)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := zPB) (O := zO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_rufEnde (P := zPB) (O := zO) (passes := 0) hG6.1 zEin .nil zHpEin rfl
    (.ret .empty (by rfl)) .nil rfl
    (hgL (hoff_g hG6 hoff6)).heldIn
  have hoff7 : offen (M7.faeden 1).spur = [()] := by
    rw [hZ7.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff6
  obtain ⟨M8, s8, hZ8⟩ := w_blatt (P := zPB) (O := zO) (passes := 0) hZ7.1
    _ _ _ rfl rfl
    (hgL (hoff_z hZ7 hoff7)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff8 : offen (M8.faeden 1).spur = [()] := by
    rw [hZ8.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff7
  obtain ⟨M9, s9, hG9⟩ := w_rueckP (P := zPB) (O := zO) (passes := 0) hZ8.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ8 hoff8)).heldIn
  have hoff9 : offen (M9.faeden 1).spur = [()] := by
    rw [hG9.1]
    exact ((Erw.lese _ _ _).offen).trans hoff8
  obtain ⟨M10, s10, hG10⟩ := w_rueckP (P := zPB) (O := zO) (passes := 0) hG9.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_g hG9 hoff9)).heldIn
  have hr10 : RufErreichbarG zPB zO 0 (RufStartG zPB zSp zInit) M10 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5)
        s6) s7) s8) s9) s10
  obtain ⟨rho, v, w0, w1, hm⟩ : ∃ (rho : Env zD (zD.params zWrap)) (v : ErgVal zD (zD.erg zWrap))
      (w0 w1 : World zD), RufEreignisF.rueck zWrap rho v w0 w1 ∈ (M10.faeden 1).log := by
    rw [hG10.1]
    exact ⟨_, _, _, _, List.mem_cons_self⟩
  have hE := ((zPB_zertifiziert M10 hr10).1 1 _ hm).2 _ _ _ _ _ rfl
  exact ⟨M10, hr10, rho, v, w0, w1, hm, hE, of_decide_eq_true hE⟩

/-! ## 3. Probe C: a reader inside the `locks` block -/

/-- `konto[0] = konto[0]` under the lock: a read (and write) of the
    protected table, guarded by the enclosing `locks` block only. -/
def zLeseSchreib : Stmt zD (vertragVon zD zHaupt) false [] zL zL :=
  .assignSlot () () zIdx (.slot () () zIdx zDarf) rfl zDarf

/-- **Probe C**: `haupt` = `locks { konto[0] = konto[0] }; return`. -/
def zRumpfHauptC : Endblock zD (vertragVon zD zHaupt) false [] [] :=
  .cons (.locks () (fun _ h => nomatch h) (.cons zLeseSchreib .nil)) (.ret .empty List.Perm.nil)

/-- The program of probe C: `zP` with the reading `haupt`. -/
def zPC : Programm zD :=
  { zP with rumpf := fun f => match f with
      | .haupt => zRumpfHauptC
      | f => zP.rumpf f }

/-- **The finding of probe C**: the old footprint check fails. -/
theorem zPC_fussG_falsch : fussOrtGB zPC zFs = false := by decide

theorem zPC_fussS : fussSperreB zPC zS zFs = true := by decide

theorem zPC_fragmentG : programmImFragmentG zPC zFs = true := by decide

theorem zPC_start : StartGut zPC zSp zInit := fun _ => rfl

theorem zPC_koerper_haupt : KoerperGutS zPC 0 (axWahr zD) zS zHaupt := by
  have hr : zPC.rumpf zHaupt = zRumpfHauptC := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [zRumpfHauptC, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    simp only [zLeseSchreib, execStmtH, freiH, zS, if_true] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [zRumpfHauptC, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    simp only [zLeseSchreib, execStmtH, freiH, zS, if_true] at hrun
    cases hrun

theorem zPC_koerper : ∀ f : zD.Fn, KoerperGutS zPC 0 (axWahr zD) zS f := by
  intro f
  cases f
  · exact koerperGutS_ohne zS rfl (zP_koerperZ zEin)
  · exact koerperGutS_ohne zS rfl (zP_koerperZ zLies)
  · exact koerperGutS_ohne zS rfl (zP_koerperZ zWrap)
  · exact zPC_koerper_haupt

/-- **Probe C is certified**: every premise of `ziel_ort_sperre` holds on
    `zPC` -- a program the old footprint check refuses. -/
theorem zPC_zertifiziert : ∀ M : RufMaschineG zD,
    RufErreichbarG zPC zO 0 (RufStartG zPC zSp zInit) M →
      VertragAmOrtG zPC M ∧ SperrInvG zS M ∧ KeinLogikHaltG zO 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG zPC zO 0 M t M' :=
  ziel_ort_sperre zPC zO 0 (axWahr zD) zS zFs zSp zInit zO_gut zO_lokal (axVertragO_wahr zO)
    axEnsLokal_wahr zS_ok zFs_voll zPC_fragmentG zPC_fussS zPC_koerper zPC_start (fun _ => rfl)
    zInit_exklusiv

/-! ## 4. Two threads writing one carrier under one lock, a non-trivial invariant

  The declaration `sD`: `zD`'s table `konto` (two slots, values `0 .. 100`)
  and lock, two functions. `setze(x)` holds the lock by signature, requires
  `konto[0] == konto[1]`, ensures `konto[0] == konto[1] && konto[0] == x`,
  and writes `x` into both slots. `haupt(x)` is every thread's root:
  `locks { setze(x) }; return`, no signature lock. The lock invariant is
  `konto[0] == konto[1]`: `haupt` needs it at the acquire to meet
  `setze`'s `requires` (its caller duty), and gets it back at the release
  from `setze`'s `ensures`. -/

inductive SFn where
  | setze
  | haupt
  deriving DecidableEq

def sSigSetze : Signatur Unit Empty Unit Empty where
  params := [.int 0 100]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def sSigHaupt : Signatur Unit Empty Unit Empty where
  params := [.int 0 100]
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The declaration of the two-writer witness. -/
def sD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := SFn
  sig := fun | .setze => 0 | .haupt => 1
  sigNr := fun | 0 => sSigSetze | _ => sSigHaupt
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def sSetze : sD.Fn := SFn.setze
def sHaupt : sD.Fn := SFn.haupt

abbrev sL : List (Res sD) := [Res.held (D := sD) ()]

theorem sDarf : darf sD () sL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

def sIdx0 {Γ : Ctx} {Λ : List (Res sD)} : Expr sD Γ Λ (.index (sD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

def sIdx1 {Γ : Ctx} {Λ : List (Res sD)} : Expr sD Γ Λ (.index (sD.count ())) :=
  .widen (by decide) (by decide) (.lit 1)

/-- `konto[0] == konto[1]`, at the holdings `sL`. -/
def sGleich {Γ : Ctx} : Expr sD Γ sL .bool :=
  .eq (.slot () () sIdx0 sDarf) (.slot () () sIdx1 sDarf)

/-- `setze` requires `konto[0] == konto[1]`. -/
def sReqSetze : Expr sD (sD.params sSetze) (Signatur.anfang sD (sD.signatur sSetze)) .bool :=
  sGleich

/-- `setze` ensures `konto[0] == konto[1] && konto[0] == x`. -/
def sEnsSetze : Expr sD (ErgCtx (sD.params sSetze) (sD.erg sSetze)) (vertragVon sD sSetze).ende .bool :=
  .and sGleich (.eq (.slot () () sIdx0 sDarf) (.var .here))

/-- `setze(x)`: `konto[0] = x; konto[1] = x; return`. -/
def sRumpfSetze : Endblock sD (vertragVon sD sSetze) false [.int 0 100] sL :=
  .cons (.assignSlot () () sIdx0 (.var .here) rfl sDarf)
    (.cons (.assignSlot () () sIdx1 (.var .here) rfl sDarf) (.ret .empty (by rfl)))


end Gabbro.Grammatik
