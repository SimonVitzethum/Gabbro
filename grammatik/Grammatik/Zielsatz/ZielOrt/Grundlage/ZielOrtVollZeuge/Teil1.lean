module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge.Teil1Basis

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll

@[expose] public section



namespace Gabbro.Grammatik
/-! ## 2. Oracle, start, and the user obligations -/

/-- The oracle: sets the slot to `true`, records the write. -/
def vO : Orakel vD where
  wirkt := fun _ σ _ =>
    ({ slots := fun _ _ _ => true, globs := (fun g => (nomatch g)), spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem vO_gut : GutO vO := by
  intro a σ ρ
  cases a
  have hW : vO.wirkt () σ ρ =
      ({ slots := fun _ _ _ => true, globs := (fun g => (nomatch g)), spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0) := rfl
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro t ht
      cases t
      exact absurd ht (by decide)
    · intro g
      exact nomatch g
  · rw [hW]
    show offen (axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur) = offen σ.spur
    exact offen_nurZugriff _ _ (fun e he => by
      simp only [axiomSpur, List.mem_append, List.mem_map, List.mem_filter] at he
      rcases he with ⟨t, _, rfl⟩ | ⟨g, _, _⟩
      · rfl
      · exact nomatch g)
  · intro hgt _
    refine ⟨[()], [], [Res.held ()], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t _
      cases t
      exact List.Mem.head _
    · intro g
      exact nomatch g
    · intro t _
      cases t
      exact vDarf
    · intro g
      exact nomatch g
    · intro m st hm
      simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
    · intro L hL
      have eL : L = () := rfl
      rw [eL]
      exact hgt () rfl () (List.Mem.head _)
    · rw [hW]

/-- The start memory: the slot `false`. -/
def vSp : Speicher vD := ⟨fun _ _ _ => false, fun g => nomatch g⟩

/-- Every thread starts in `haupt`. -/
def vInit : Faden → Σ f : vD.Fn, Env vD (vD.params f) :=
  fun _ => ⟨vHaupt, .nil⟩

theorem vP_start : StartGut vP vSp vInit := fun _ => rfl

theorem vInit_exklusiv : StartExklusiv (D := vD) vInit :=
  fun _ _ _ _ h => nomatch h

/-- An `end` block that starts with a statement ends in a logic outcome only
    through that statement or its rest. -/
theorem execEnd_cons_logikV {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (e : Logik D) (h : execEnd O passes R (.cons s rest) σ ρ = .logik e) :
    execStmt O passes R s σ ρ = .logik e ∨
      ∃ σ' ρ', execStmt O passes R s σ ρ = .ok σ' ρ' ∧ execEnd O passes R rest σ' ρ' = .logik e := by
  simp only [execEnd] at h
  revert h
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => intro h; exact Or.inr ⟨σ', ρ', rfl, h⟩
  | logik e' => intro h; cases h; exact Or.inl rfl
  | _ => intro h; cases h

/-- The gate of a `requires true` callee lets every call through. -/
theorem vTor (R : ∀ f : vD.Fn, World vD → Env vD (vD.params f) → RufAusgang f) (g : vD.Fn)
    (σ : World vD) (ρ : Env vD (vD.params g)) : torRuf vP R g σ ρ = R g σ ρ := if_pos rfl

theorem vP_koerper_err : KoerperGutV vP 0 vErr := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : vP.rumpf vErr = vRumpfErr := rfl
  rw [hr] at hrun
  simp only [vRumpfErr, execEnd] at hrun
  cases hrun

theorem mapWelt_logikV {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {o : Ausgang V l Γ} {f : World D → World D} {e : Logik D} (h : o.mapWelt f = .logik e) :
    o = .logik e := by
  cases o <;> simp_all [Ausgang.mapWelt]

theorem execBlock_eins_logikV {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) {e : Logik D}
    (h : execBlock O passes R (.cons s .nil) σ ρ = .logik e) :
    execStmt O passes R s σ ρ = .logik e := by
  simp only [execBlock] at h
  revert h
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => intro h; simp only [reduceCtorEq] at h
  | _ => intro h; exact h

/-- An axiom call never ends in a logic failure (only in `ok` or in the
    hardware outcome of an answer outside its type). -/
theorem execStmt_axiomCall_logik {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (σ : World D) (ρ : Env D Γ)
    (e : Logik D) :
    execStmt O passes R (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ ≠
      .logik e := by
  simp only [execStmt]
  split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem vP_koerper_mid : KoerperGutV vP 0 vMid := by
  intro O' _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : vP.rumpf vMid = vRumpfMid := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [vIte, vLetElse, vErrBlock, execStmt, execBlock, vTor] at h1
    split at h1
    · split at h1
      · simp only [Ausgang.schrumpf, reduceCtorEq] at h1
      · simp only [EndAusgang.zuAusgang, EndAusgang.schrumpf, execEnd, reduceCtorEq] at h1
      · rename_i e hR
        cases h1
        exact hOV _ _ _ _ hR g rfl
      · cases h1
    · cases h1
  · simp only [execEnd] at h1
    cases h1

theorem vP_koerper_haupt : KoerperGutV vP 0 vHaupt := by
  intro O' _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : vP.rumpf vHaupt = vRumpfHaupt := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [vRufMid, vZeigerMid, execStmt, eval, vTor] at h1
    split at h1
    · cases h1
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h1
      exact hOV _ _ _ _ hR g rfl
    · cases h1
  · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
    · simp only [vRetry, vLeave, execStmt, retryLauf, wahr?, eval, Bool.false_eq_true, ↓reduceIte, execBlock,
  reduceCtorEq] at h2
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h2 with h3 | ⟨σ3, ρ3, _, h3⟩
      · simp only [vLocks] at h3
        simp only [execStmt] at h3
        exact execStmt_axiomCall_logik _ _ _ _ _ _ _ _ _ _ _ _ _
          (execBlock_eins_logikV _ _ _ vAx _ _ (mapWelt_logikV h3))
      · simp only [execEnd] at h3
        cases h3

theorem vP_koerper : ∀ f, KoerperGutV vP 0 f := by
  intro f
  cases f
  · exact vP_koerper_haupt
  · exact vP_koerper_mid
  · exact vP_koerper_err

/-- An event of the declaration (a release of the lock). -/
def vE0 : Ereignis vD := .gibt ()

/-- **All premises of `ziel_ort_voll` hold jointly on `vP`.** -/
theorem vP_vertragAmOrt : ∀ M : RufMaschineG vD,
    RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M → VertragAmOrtG vP M :=
  ziel_ort_voll vP vO 0 vFs vSp vInit vE0 vO_gut vFs_voll vP_fragment vP_fuss vP_koerper
    vP_start vInit_exklusiv

/-! ## 3. The run -/

/-- The start thread state (every thread): `haupt`, no lock held. -/
def vZ0 : RufFadenG vD :=
  ⟨[], ⟨vHaupt, .nil, vSp.welt [], ⟨false, [], [], .nil, .ende vRumpfHaupt⟩⟩, [],
    [RufEreignisF.eintritt vHaupt .nil (vSp.welt [])]⟩

theorem vM0_faden (t : Faden) : (RufStartG vP vSp vInit).faeden t = vZ0 := by rfl

theorem vHg0 {s : List (Ereignis vD)} (h : offen s = []) :
    HeldGenau ([] : List (Res vD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem vHgL {s : List (Ereignis vD)} (h : offen s = [()]) : HeldGenau vL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem vOffen_weltVon (M : RufMaschineG vD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := by rfl

theorem vHoff_z {M : RufMaschineG vD} {f : Faden} {stapel : List (RufRahmenG vD)} {fn : vD.Fn}
    {rho : Env vD (vD.params fn)} {s0 : World vD} {log : List (RufEreignisF vD)} {l : Bool}
    {Γ : Ctx} {Λ : List (Res vD)} {ρ : Env vD Γ} {r : GRest vD (vertragVon vD fn) l Γ Λ}
    {σ : World vD} {x : List vD.Lock} (h : ZustandG M f stapel fn rho s0 log ρ r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [← h.spur]; exact ho

theorem vHoff_g {M : RufMaschineG vD} {f : Faden} {caller : RufRahmenG vD}
    {rst : List (RufRahmenG vD)} {fn : vD.Fn} {rho : Env vD (vD.params fn)} {s0 : World vD}
    {log : List (RufEreignisF vD)} {v : ErgVal vD (vD.erg fn)} {σ : World vD}
    {x : List vD.Lock} (h : GepopptG M f caller rst fn rho s0 log v σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [h.1] at ho; exact ho

end Gabbro.Grammatik
