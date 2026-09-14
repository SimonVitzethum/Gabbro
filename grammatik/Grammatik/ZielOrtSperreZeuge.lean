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
import Grammatik.ZielOrtSperre
import Grammatik.ZielOrtGanzZeuge

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
  | grund σ' r => exact (Fin.cast hr r).elim0
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
  requires := fun _ => .wahr
  ensures
    | .ein => zEnsHundert
    | .lies => zEnsLies
    | .wrap => zEnsWrapB
    | .haupt => .wahr
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
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .keine (by rfl))) .nil rfl
    (hgL (hoff_z hZ3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := zPB) (O := zO) (passes := 0) hZ4.1
    (.slot () () zIdx zDarf) (.ret (.wert (.var .hier)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := zPB) (O := zO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_rufEnde (P := zPB) (O := zO) (passes := 0) hG6.1 zEin .nil zHpEin rfl
    (.ret .keine (by rfl)) .nil rfl
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
  .cons (.locks () (fun _ h => nomatch h) (.cons zLeseSchreib .nil)) (.ret .keine List.Perm.nil)

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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
  .weiter (by decide) (by decide) (.lit 0)

def sIdx1 {Γ : Ctx} {Λ : List (Res sD)} : Expr sD Γ Λ (.index (sD.count ())) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- `konto[0] == konto[1]`, at the holdings `sL`. -/
def sGleich {Γ : Ctx} : Expr sD Γ sL .bool :=
  .eq (.slot () () sIdx0 sDarf) (.slot () () sIdx1 sDarf)

/-- `setze` requires `konto[0] == konto[1]`. -/
def sReqSetze : Expr sD (sD.params sSetze) (Signatur.anfang sD (sD.signatur sSetze)) .bool :=
  sGleich

/-- `setze` ensures `konto[0] == konto[1] && konto[0] == x`. -/
def sEnsSetze : Expr sD (ErgCtx (sD.params sSetze) (sD.erg sSetze)) (vertragVon sD sSetze).ende .bool :=
  .und sGleich (.eq (.slot () () sIdx0 sDarf) (.var .hier))

/-- `setze(x)`: `konto[0] = x; konto[1] = x; return`. -/
def sRumpfSetze : Endblock sD (vertragVon sD sSetze) false [.int 0 100] sL :=
  .cons (.assignSlot () () sIdx0 (.var .hier) rfl sDarf)
    (.cons (.assignSlot () () sIdx1 (.var .hier) rfl sDarf) (.ret .keine (by rfl)))

theorem sHp : RufPasst sD (vertragVon sD sHaupt) (sD.signatur sSetze) sL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
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
  .call sSetze (.cons (.var .hier) .nil) sHp rfl

/-- `haupt(x)`: `locks { setze(x) }; return`. -/
def sRumpfHaupt : Endblock sD (vertragVon sD sHaupt) false [.int 0 100] [] :=
  .cons (.locks () (fun _ h => nomatch h) (.cons sRuf .nil)) (.ret .keine List.Perm.nil)

/-- The two-writer program. -/
def sP : Programm sD where
  invariante := fun i => nomatch i
  requires
    | .setze => sReqSetze
    | .haupt => .wahr
  ensures
    | .setze => sEnsSetze
    | .haupt => .wahr
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
      simp [sEnsSetze, sGleich, eval, World.lese, World.merke, World.schreibSlot,
        World.storeSlot, sIdx0, sIdx1, Zahl.weiter, wahr?, ergEnv]
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
      decide ((σ2.slots () 0 ()).n = (ρk.get .hier).n)) = true := h
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
      (l := false) (Γ := [.int 0 100]) sSetze (.cons (.var .hier) .nil) sHp rfl
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
          (Env.cons (ρ.get .hier) .nil) := (hU () σ).2.2
      have htor : torRuf sP R sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .hier) .nil) =
          R sSetze (((U () σ).nimmt ()).lese sL []) (Env.cons (ρ.get .hier) .nil) := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun
      cases hrun
  · rw [hr] at hrun
    simp only [sRumpfHaupt, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := sS) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := [.int 0 100]) sSetze (.cons (.var .hier) .nil) sHp rfl
      ((U () σ).nimmt ()) ρ with ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hreq : ReqAmEintritt sP sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .hier) .nil) := (hU () σ).2.2
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

def sHauptRet : Endblock sD (vertragVon sD sHaupt) false [.int 0 100] [] := .ret .keine List.Perm.nil

/-- **One critical section of a thread `t` running `haupt(x)`**: eight
    steps from its start state -- take the lock, call `setze(x)`, both
    writes, return, release. Nothing else moves. -/
theorem sAbschnitt {M : RufMaschineG sD} (hr : RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M)
    (t : Faden) (x : Env sD [.int 0 100]) (hz : M.faeden t = sZ0 x)
    (hfrei : RufFreiG M t ()) :
    ∃ M' : RufMaschineG sD, RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M' ∧
      (∀ u, u ≠ t → M'.faeden u = M.faeden u) ∧ offen (M'.faeden t).spur = [] ∧
      (M'.speicher.slots () 0 ()).n = (x.get .hier).n ∧
      (M'.speicher.slots () 1 ()).n = (x.get .hier).n ∧
      (∃ s0 : World sD, RufEreignisF.eintritt sSetze (Env.cons (x.get .hier) .nil) s0 ∈
          (M'.faeden t).log ∧ s0.speicher = M.speicher) ∧
      (∃ (v : ErgVal sD (sD.erg sSetze)) (s0 s1 : World sD),
          RufEreignisF.rueck sSetze (Env.cons (x.get .hier) .nil) v s0 s1 ∈ (M'.faeden t).log ∧
          (s1.slots () 0 ()).n = (x.get .hier).n) := by
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
    (.cons (.var .hier) .nil) sHp rfl .nil _ x rfl (shgL (soff_z hZ2 hoff2)).heldIn
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
