module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanzZeuge

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 0. Helpers for concrete bodies -/

/-- A call statement, unfolded (the same in both semantics). -/
theorem execStmtH_call {D : Deklaration} {S : SperrInv D} {O : Orakel D} {U : Umwelt D}
    {passes : Nat} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (σ : World D) (ρ : Env D Γ) :
    execStmtH S O U passes R (Stmt.call (l := l) g args hp hr) σ ρ =
      execStmt O passes R (Stmt.call (l := l) g args hp hr) σ ρ := by rfl

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


end Gabbro.Grammatik
