/- Part 11 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T10
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T11a
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **A `traverse` whose invariant reads false is stuck.** At a head
    `trav t inv body (i :: is) k` whose invariant, read at the thread's
    current world, is false, no step of `f` changes frame, stack or log
    (only the bare lock steps, removed from G on 2026-09-13, fired there). The machine never runs the next iteration and never
    returns from the frame -- where `traverseLauf` ends in
    `logik .schleife`. -/
theorem trav_falsch_steht {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .trav t inv body (i :: is) k⟩)
    (hw0 : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = false) :
    ∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩ := by
  subst hz
  cases hs with
  | g1 hs =>
    cases hs with
    | endeBindAxiomOpt => kopfwegH
    | blatt => kopfwegH
    | ruf => kopfwegH
    | rueck => kopfwegH
    | endeEntf => kopfwegH
    | endeForm => kopfwegH
    | dannBlatt => kopfwegH
    | dannLeer => kopfwegH
    | dannIteWahr => kopfwegH
    | dannIteFalsch => kopfwegH
    | dannOnOptionSome => kopfwegH
    | dannOnOptionNone => kopfwegH
    | dannOnTagSome => kopfwegH
    | dannOnTagNone => kopfwegH
    | dannOnGrund => kopfwegH
    | endeBind => kopfwegH
    | dannBind => kopfwegH
    | dannNarrowOk => kopfwegH
    | endeBindAxiom => kopfwegH
  | g2 hs =>
    cases hs with
    | dannNarrowElse => kopfwegH
    | dannPruefWahr => kopfwegH
    | dannPruefFalsch => kopfwegH
    | dannBreaking => kopfwegH
    | dannLocks => kopfwegH
    | freiGib => kopfwegH
    | schrumpfVergiss => kopfwegH
    | dannTrav => kopfwegH
    | travNext _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => (rw [hR] at hhead; cases hhead; subst hs₁; rw [hw0] at hw; cases hw)
    | travFort => kopfwegH
    | travDone => kopfwegH
    | dannRetry => kopfwegH
    | wiederUeber => kopfwegH
    | wiederWeiter => kopfwegH
    | wiederSchritt => kopfwegH
    | wiederFort => kopfwegH
    | dannForever => kopfwegH
    | ewigWeiter => kopfwegH
    | ewigFort => kopfwegH
    | rufDann => kopfwegH
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk => kopfwegH
    | dannAxiomCallElseGrund => kopfwegH
    | dannCallInd => kopfwegH
    | rufCallInd => kopfwegH
    | dannBindCall => kopfwegH
    | dannBindCallInd => kopfwegH
    | dannBindCallElse => kopfwegH
    | dannBindCallIndElse => kopfwegH
    | dannCallIndElse => kopfwegH
    | rueckBind => kopfwegH
    | dannLeaveTrav => kopfwegH
    | dannNextTrav => kopfwegH
    | dannLeaveWieder => kopfwegH
    | dannNextWieder => kopfwegH
    | dannLeaveEwig => kopfwegH
  | g4 hs =>
    cases hs with
    | dannNextEwig => kopfwegH
    | peelDannLeave => kopfwegH
    | peelDannNext => kopfwegH
    | peelSchrumpfLeave => kopfwegH
    | peelSchrumpfNext => kopfwegH
    | peelFreiLeave => kopfwegH
    | peelFreiNext => kopfwegH
    | peelAbbruchLeave => kopfwegH
    | peelAbbruchNext => kopfwegH
    | dannRet => kopfwegH
    | rueckCons => kopfwegH
    | dannRetBind => kopfwegH
    | rueckConsBind => kopfwegH
    | rueckGrund => kopfwegH
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt => kopfwegH
    | dannBindAxiomOptElseOk => kopfwegH
    | dannBindAxiomOptElseGrund => kopfwegH
    | dannRegLies => kopfwegH
    | dannRegLiesElseWahr => kopfwegH
    | dannRegLiesElseFalsch => kopfwegH
    | dannAwaits => kopfwegH
    | dannExchange => kopfwegH
    | dannGleit => kopfwegH
    | dannGleitLit => kopfwegH
    | dannGleitVon => kopfwegH
    | dannGleitNarrowOk => kopfwegH
    | dannGleitNarrowElse => kopfwegH
    | dannBindAxiom => kopfwegH
    | dannBindAxiomElseOk => kopfwegH
    | dannBindAxiomElseGrund => kopfwegH
    | rueckConsGrund => kopfwegH
    | dannRetGrund => kopfwegH
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk => kopfwegH
    | endeBindAxiomOptElseGrund => kopfwegH
    | endeBindAxiomElseOk => kopfwegH
    | endeBindAxiomElseGrund => kopfwegH
  | g7 hs =>
    cases hs with
    | dannVerbrauch => kopfwegH
    | verbrauchWeiter => kopfwegH
    | verbrauchLeer => kopfwegH
    | verbrauchFort => kopfwegH
    | dannLeaveVerbrauch => kopfwegH
    | dannNextVerbrauch => kopfwegH

/-- `traverse konto invariant false { }` in the witness function. -/
def adTrav : Stmt adD (vertragVon adD adFn) false [] [] [] :=
  .traverse () .fls .nil

/-- The old counterexample body: `traverse konto invariant false { }; return 7`. -/
def adTravRumpf : Endblock adD (vertragVon adD adFn) false [] [] :=
  .cons adTrav (.ret (.val adSieben) List.Perm.nil)

def adTravFaden : RufFadenG adD :=
  ⟨[adCaller], ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adTravRumpf⟩⟩,
    [], []⟩

def adTravM : RufMaschineG adD := ⟨adSp0, fun _ => adTravFaden, [], adSp0.welt []⟩

/-- The three frames the witness thread can be in: at the body, after the
    unfold of the `traverse` statement, at the loop. -/
def adTravK0 : RufRahmenG adD :=
  ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende adTravRumpf⟩⟩

def adTravK1 : RufRahmenG adD :=
  ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil,
    .dann (.cons adTrav .nil) (.ende (.ret (.val adSieben) List.Perm.nil))⟩⟩

def adTravK2 : RufRahmenG adD :=
  ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil,
    .trav () .fls .nil (alleIndizes (adD.count ()))
      (.dann .nil (.ende (.ret (.val adSieben) List.Perm.nil)))⟩⟩

/-- The run invariant of the witness thread: one of the three frames, the
    caller below, NOTHING logged. -/
def AdTravZ (M : RufMaschineG adD) : Prop :=
  ∃ sp, M.faeden 0 = ⟨[adCaller], adTravK0, sp, []⟩ ∨
    M.faeden 0 = ⟨[adCaller], adTravK1, sp, []⟩ ∨
    M.faeden 0 = ⟨[adCaller], adTravK2, sp, []⟩

theorem adTravZ_schritt {M M' : RufMaschineG adD} (hs : RufSchrittG adP adO 0 M 0 M')
    (h : AdTravZ M) : AdTravZ M' := by
  obtain ⟨sp, h | h | h⟩ := h
  · rcases trav_ende_schritt hs _ h () .fls .nil (.ret (.val adSieben) List.Perm.nil)
      Env.nil rfl with ⟨sp', e⟩ | ⟨sp', e⟩
    · exact ⟨sp', Or.inl e⟩
    · exact ⟨sp', Or.inr (Or.inl e)⟩
  · rcases trav_dann_schritt hs _ h () .fls .nil .nil
      (.ende (.ret (.val adSieben) List.Perm.nil)) Env.nil rfl with ⟨sp', e⟩ | ⟨sp', e⟩
    · exact ⟨sp', Or.inr (Or.inl e)⟩
    · exact ⟨sp', Or.inr (Or.inr e)⟩
  · obtain ⟨sp', e⟩ := trav_falsch_steht hs _ h () .fls .nil
      ⟨0, by decide, by decide⟩ [⟨1, by decide, by decide⟩]
      (.dann .nil (.ende (.ret (.val adSieben) List.Perm.nil))) Env.nil rfl rfl
    exact ⟨sp', Or.inr (Or.inr e)⟩

theorem adTravZ_lauf {M M' : RufMaschineG adD} (hl : RufLaufG adP adO 0 0 M M')
    (h : AdTravZ M) : AdTravZ M' := by
  induction hl with
  | refl => exact h
  | schritt hs _ ih => exact ih (adTravZ_schritt hs h)

/-- **The old counterexample now AGREES.** The sequential semantics of
    `traverse konto invariant false { }; return 7` ends in `logik .schleife`;
    and NO run of thread 0 of the machine logs anything at all -- in
    particular no return of `7`, which the old rule `dannTravFertig`
    produced. -/
theorem trav_einig :
    execEnd adO 0 keinRuf adTravRumpf (adTravM.weltVon 0) Env.nil =
      .logik .schleife ∧
    ∀ M' : RufMaschineG adD, RufLaufG adP adO 0 0 adTravM M' → (M'.faeden 0).log = [] := by
  refine ⟨rfl, ?_⟩
  intro M' hl
  obtain ⟨sp, h | h | h⟩ := adTravZ_lauf hl ⟨[], Or.inl rfl⟩ <;> rw [h]

/-! ## 19. AGREEMENT (formerly a finding): `ruf` continues after the call

    The old `ruf`/`rufCallInd` pushed the caller frame UNCHANGED, so after
    `rueck` the caller executed the same call again. The repaired rules push
    the caller with its residue advanced to `.ende rest` at holdings
    `nach D g Λ` (resp. `nachSig`), exactly like `rufDann`. In the machine's
    own witness run (`M0G` … `M7G`) the restored caller is now the frame
    after the call, whose residue is the parameter return, and no further
    step of thread 0 logs anything: the callee is entered exactly once, as
    in the sequential semantics. Bodies with calls are adequate in general
    (`RufAdaequatRufG.lean`). -/


end Gabbro.Grammatik
