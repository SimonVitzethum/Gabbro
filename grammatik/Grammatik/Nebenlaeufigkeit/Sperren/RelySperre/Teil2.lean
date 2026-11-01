module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Nebenlaeufigkeit.Sperren.Ressourceninvariante.Teil2
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Nebenlaeufigkeit.Allgemein.WacheGlobal
public import Grammatik.Nebenlaeufigkeit.Sperren.RelySperre.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- Step 2 (witness): thread 1 fires the writing leaf at position 1. -/
theorem wit_leaf :
    PCSchritt refP refO 0 witProg refPC1pre refB_pc1 1 refPC2 refB_pc2 := by
  have hpc : (witProg 1)[refB_pc1 1]? =
      some (PCAtom.leaf [Res.held (D := refD) ()] [Sum.inl (())]) := rfl
  have hneu : (((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
      [Res.held (D := refD) ()] refK0 () refV100).spur =
      [Ereignis.zugriff () true [Res.held (D := refD) ()]
        (refPC1pre.weltVon 1).haelt] ++ refPC1pre.spuren 1 := rfl
  have hkn : ∀ (L : refD.Lock) (h : List refD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := refD) ()] (refPC1pre.weltVon 1).haelt] := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  have hmark : ∀ e ∈ [Ereignis.zugriff () true [Res.held (D := refD) ()]
      (refPC1pre.weltVon 1).haelt], ∀ (m : refD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf [Res.held (D := refD) ()]
          [Sum.inl (())]) := by
    intro e hm m st hlam
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.lambda, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hlam
  have hcar : ∀ e ∈ [Ereignis.zugriff () true [Res.held (D := refD) ()]
      (refPC1pre.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf [Res.held (D := refD) ()]
          [Sum.inl (())]) := by
    intro e hm o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.traeger, Option.some.injEq] at ho
    subst ho
    have hc : PCAtom.carriers (D := refD)
        (PCAtom.leaf [Res.held (D := refD) ()] [Sum.inl (())]) =
        [Sum.inl (())] := rfl
    rw [hc]
    exact List.mem_singleton.mpr rfl
  exact PCSchritt.leaf refPC1pre refB_pc1 1
    (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    refWriteStAt refRho7 rfl refPC1haelt _ _ refPCwrite hneu hkn
    [Res.held (D := refD) ()] [Sum.inl (())] hpc rfl hmark hcar

/-- The witness reachability: lock, then the writing leaf. -/
theorem wit_reach :
    PCReach refP refO 0 witProg (GenStart refSp0) refPC2 refB_pc2 := by
  have h1 : PCReach refP refO 0 witProg (GenStart refSp0) refPC1pre
      refB_pc1 :=
    PCReach.step _ _ _ _ _ PCReach.start wit_take
  exact PCReach.step _ _ _ _ _ h1 wit_leaf

/-- The thread-0 step statement: a local assignment, touching no
    memory and recording no events. -/
def witStmt0 : Stmt refD (vertragVon refD refEin) false [.bool] [] [] :=
  .assignVar (τ := .bool) Var.here
    (.fls : Expr refD [.bool] [] .bool)

/-- Its environment: the local starts `false`. -/
def witRho0 : Env refD [.bool] := .cons false .nil

/-- The outcome world of the thread-0 step: the read world. -/
def witW0' : World refD :=
  (refPC2.weltVon 0).lese ([] : List (Res refD))
    ([] : List (refD.Tab ⊕ refD.Glob))

/-- The machine after the thread-0 step. -/
def witM' : GenMaschine refD :=
  ⟨witW0'.speicher, genUpdate refPC2.spuren 0 witW0'.spur,
    refPC2.lauf ++ genEigen 0 [], refPC2.start,
    refPC2.welten ++ [witW0'], refPC2.tiefe + 1⟩

/-- Step 3 (witness): thread 0 fires the local assignment. -/
theorem wit_step0 :
    PCSchritt refP refO 0 witProg refPC2 refB_pc2 0 witM'
      (pcAdvance refB_pc2 0) := by
  have hΛ : HeldGenau ([] : List (Res refD)) (offen (refPC2.spuren 0)) := by
    have e : refPC2.spuren 0 = [] := rfl
    rw [e]
    intro L
    simp only [List.not_mem_nil, offen]
  have hstep : (execStmt (D := refD) (V := vertragVon refD refEin) refO 0
      keinRuf witStmt0 (refPC2.weltVon 0) witRho0).welt = some witW0' := rfl
  have hneu : witW0'.spur = [] ++ refPC2.spuren 0 := rfl
  have hkn : ∀ (L : refD.Lock) (h : List refD.Lock),
      Ereignis.nimmt L h ∉ ([] : List (Ereignis refD)) := by
    intro L h hm
    simp only [List.not_mem_nil] at hm
  have hpc : (witProg 0)[refB_pc2 0]? =
      some (PCAtom.leaf (D := refD) [] []) := rfl
  refine PCSchritt.leaf refPC2 refB_pc2 0 (V := vertragVon refD refEin)
    (l := false) (Γ := [.bool]) (Λ := []) (Λ' := []) (s := witStmt0)
    (ρ := witRho0) (σ' := witW0') (neu := []) (Λa := []) (cs := [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact hΛ
  · exact hstep
  · exact hneu
  · exact hkn
  · exact hpc
  · rfl
  · intro e he m st hm
    simp only [List.not_mem_nil] at he
  · intro e he o ho
    simp only [List.not_mem_nil] at he

/-- Thread 1 holds the lock after the writing leaf. -/
theorem wit_haelt1 : (() : refD.Lock) ∈ offen (refPC2.spuren 1) := by
  have e : offen (refPC2.spuren 1) = [()] := rfl
  rw [e]
  exact List.mem_singleton.mpr rfl

/-- The lock guards the table. -/
theorem wit_guard : Sum.inl (() : refD.Lock) ∈ refD.braucht () :=
  List.mem_singleton.mpr rfl

/-- **Inhabitation for `rely_aus_sperre`.** All premises hold jointly on
    the reference fixture: the PC run reaches `refPC2` (lock, then the
    writing leaf) with thread 1 holding the lock of `konto`, and a step
    of thread 0 (a local assignment) keeps every slot. Non-degenerate:
    `einzahlen` writes `konto` and the run moves slot `0` from `0` to
    `100`. -/
theorem rely_aus_sperre_zeuge :
    (∀ (k : Int) (fld : refD.Feld ()),
      witM'.speicher.slots () k fld = refPC2.speicher.slots () k fld) ∧
    refPC2.speicher.slots () 0 () ≠ refSp0.slots () 0 () ∧
    (vertragVon refD refEin).schreibt () = true := by
  refine ⟨?_, refB_pc_schreibt, refEin_schreibt _⟩
  intro k fld
  exact rely_aus_sperre refP refO 0 refO_gut witProg refSp0 refPC2 refB_pc2
    wit_reach 1 0 (by decide) () wit_haelt1 witM' _ wit_step0 () wit_guard
    k fld

/-! ## 6. Witness on a global fixture: global rely -/

/-- Start memory for the global witness: slots `0`, global `0`. -/
def gSp0 : Speicher gD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun _ => ⟨0, by decide, by decide⟩⟩

/-- The witness oracle: no axioms, no registers, always visible. -/
def gO : Orakel gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => true

/-- The oracle is good: every conjunct closes on its empty axiom domain. -/
theorem gO_gut : GutO gO := by
  intro a σ ρ
  exact nomatch a

/-- Thread program for the global witness: thread 1 takes the lock and
    fires the global-writing leaf; thread 0 rests on an empty-holdings
    leaf atom. -/
def gProg : PCProg gD
  | 1 => [.take (), .leaf [Res.held (D := gD) ()] [Sum.inr (())]]
  | _ => [.leaf ([] : List (Res gD)) []]

/-- The single-function program: trivial contracts, a returning body. -/
def gPr : Programm gD where
  invariante := fun i => nomatch i
  requires
    | () => .tru
  ensures
    | () => .tru
  rumpf
    | () => .ret (Γ := []) (Λ := [Res.held (D := gD) ()])
        .empty (List.Perm.refl _)

/-- The written value `5` in range. -/
def gWriteE : Expr gD [] [Res.held (D := gD) ()] (.int 0 10) :=
  .widen (by decide) (by decide) (.lit 5)

/-- The global write holds its guard statically. -/
theorem gDarfHeld : gdarf gD () [Res.held (D := gD) ()] := by
  intro w hw
  have hmem : w ∈ ([Sum.inl ()] : List (gD.Lock ⊕ (gD.Marke × Nat))) := hw
  have e : w = Sum.inl () := List.mem_singleton.mp hmem
  subst e
  exact List.mem_singleton.mpr rfl

/-- The thread-1 write statement: global `()` gets `5`. -/
def gWriteSt : Stmt gD (Vertrag.vonSig gD (gD.signatur ())) false []
    [Res.held (D := gD) ()] [Res.held (D := gD) ()] :=
  .assignGlob () gWriteE rfl gDarfHeld

/-- Counter after the lock step on thread 1. -/
def gPc1 : PCStand := pcAdvance (fun _ => 0) 1

/-- The machine after thread 1 takes the lock. -/
def gM1 : GenMaschine gD :=
  ⟨gSp0,
    genUpdate (GenStart gSp0).spuren 1 [Ereignis.nimmt (D := gD) () []],
    (GenStart gSp0).lauf ++ genEigen 1 [Ereignis.nimmt (D := gD) () []],
    (GenStart gSp0).start,
    (GenStart gSp0).welten ++ [gSp0.welt [Ereignis.nimmt (D := gD) () []]],
    (GenStart gSp0).tiefe + 1⟩

/-- Step 1 (global witness): thread 1 takes the lock. -/
theorem gTake :
    PCSchritt gPr gO 0 gProg (GenStart gSp0) (fun _ => 0) 1 gM1 gPc1 := by
  have hself : (() : gD.Lock) ∉ offen ((GenStart gSp0).spuren 1) := by
    intro hmem
    have e : ((GenStart gSp0).spuren 1) = [] := rfl
    have hnil : offen ((GenStart gSp0).spuren 1) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List gD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hrang : ∀ K ∈ offen ((GenStart gSp0).spuren 1),
      gD.rang K < gD.rang (()) := by
    intro K hK
    have e : ((GenStart gSp0).spuren 1) = [] := rfl
    have hnil : offen ([] : List (Ereignis gD)) = [] := rfl
    rw [e, hnil, List.mem_nil_iff] at hK
    exact absurd hK (by decide)
  have hfrei : GenFrei (GenStart gSp0) 1 (()) := by
    intro g hne hmem
    have e : ((GenStart gSp0).spuren g) = [] := rfl
    have hnil : offen ((GenStart gSp0).spuren g) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List gD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hpc : (gProg 1)[(fun _ => 0) 1]? =
      some (PCAtom.take (D := gD) ()) := rfl
  exact PCSchritt.take (GenStart gSp0) (fun _ => 0) 1 ()
    hself hrang hfrei hpc

/-- The outcome world of the global write. -/
def gW1w : World gD :=
  (((gM1.weltVon 1).lese [Res.held (D := gD) ()] (gWriteE.orte)).schreibGlob ()
    [Res.held (D := gD) ()]
    (eval ((gM1.weltVon 1).lese [Res.held (D := gD) ()] (gWriteE.orte))
      gWriteE
      ((gM1.weltVon 1).lese [Res.held (D := gD) ()] (gWriteE.orte))
      Env.nil))

/-- Thread 1 holds the lock after taking it. -/
theorem gM1haelt :
    HeldGenau [Res.held (D := gD) ()]
      (offen (gM1.spuren 1)) := by
  have e : offen (gM1.spuren 1) = [()] := rfl
  have h : HeldGenau [Res.held (D := gD) ()] [()] := by
    intro L
    constructor
    · intro hL
      have he : Res.held (D := gD) L = Res.held (D := gD) () :=
        (List.mem_singleton.mp hL)
      have eL : L = () := by cases he; rfl
      have hmem : L ∈ ([()] : List gD.Lock) :=
        eL ▸ List.mem_singleton.mpr rfl
      exact hmem
    · intro hL
      have he : L = () := (List.mem_singleton.mp hL)
      have hmem : Res.held (D := gD) L ∈
          ([Res.held (D := gD) ()] : List (Res gD)) :=
        he ▸ List.mem_singleton.mpr rfl
      exact hmem
  rw [e]
  exact h

/-- Counter after the leaf step on thread 1. -/
def gPc2 : PCStand := pcAdvance gPc1 1

/-- The machine after thread 1 writes the global. -/
def gM2 : GenMaschine gD :=
  ⟨gW1w.speicher, genUpdate gM1.spuren 1 gW1w.spur,
    gM1.lauf ++ genEigen 1
      [Ereignis.gzugriff () true [Res.held (D := gD) ()]
        (gM1.weltVon 1).haelt],
    gM1.start, gM1.welten ++ [gW1w], gM1.tiefe + 1⟩

/-- Step 2 (global witness): thread 1 fires the global-writing leaf. -/
theorem gLeaf :
    PCSchritt gPr gO 0 gProg gM1 gPc1 1 gM2 gPc2 := by
  have hpc : (gProg 1)[gPc1 1]? =
      some (PCAtom.leaf [Res.held (D := gD) ()] [Sum.inr (())]) := rfl
  have hstep : (execStmt (D := gD) (V := Vertrag.vonSig gD (gD.signatur ()))
      gO 0 keinRuf gWriteSt (gM1.weltVon 1) Env.nil).welt = some gW1w := rfl
  have hneu : gW1w.spur =
      [Ereignis.gzugriff () true [Res.held (D := gD) ()]
        (gM1.weltVon 1).haelt] ++ gM1.spuren 1 := rfl
  have hkn : ∀ (L : gD.Lock) (h : List gD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.gzugriff () true
        [Res.held (D := gD) ()] (gM1.weltVon 1).haelt] := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  have hmark : ∀ e ∈ [Ereignis.gzugriff () true [Res.held (D := gD) ()]
      (gM1.weltVon 1).haelt], ∀ (m : gD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf [Res.held (D := gD) ()]
          [Sum.inr (())]) := by
    intro e hm m st hlam
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.lambda, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hlam
  have hcar : ∀ e ∈ [Ereignis.gzugriff () true [Res.held (D := gD) ()]
      (gM1.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf [Res.held (D := gD) ()]
          [Sum.inr (())]) := by
    intro e hm o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.traeger, Option.some.injEq] at ho
    subst ho
    have hc : PCAtom.carriers (D := gD)
        (PCAtom.leaf [Res.held (D := gD) ()] [Sum.inr (())]) =
        [Sum.inr (())] := rfl
    rw [hc]
    exact List.mem_singleton.mpr rfl
  exact PCSchritt.leaf gM1 gPc1 1 (Vertrag.vonSig gD (gD.signatur ()))
    false [] [Res.held (D := gD) ()] [Res.held (D := gD) ()]
    gWriteSt Env.nil rfl gM1haelt _ _ hstep hneu hkn
    [Res.held (D := gD) ()] [Sum.inr (())] hpc rfl hmark hcar

/-- The global-witness reachability: lock, then the global write. -/
theorem gReach :
    PCReach gPr gO 0 gProg (GenStart gSp0) gM2 gPc2 := by
  have h1 : PCReach gPr gO 0 gProg (GenStart gSp0) gM1 gPc1 :=
    PCReach.step _ _ _ _ _ PCReach.start gTake
  exact PCReach.step _ _ _ _ _ h1 gLeaf

/-- The thread-0 step statement: a local assignment, touching no memory. -/
def gStmt0 : Stmt gD (Vertrag.vonSig gD (gD.signatur ())) false [.bool]
    [] [] :=
  .assignVar (τ := .bool) Var.here
    (.fls : Expr gD [.bool] [] .bool)

/-- Its environment: the local starts `false`. -/
def gRho0 : Env gD [.bool] := .cons false .nil

/-- The outcome world of the thread-0 step: the read world. -/
def gW0' : World gD :=
  (gM2.weltVon 0).lese ([] : List (Res gD))
    ([] : List (gD.Tab ⊕ gD.Glob))

/-- The machine after the thread-0 step. -/
def gM3 : GenMaschine gD :=
  ⟨gW0'.speicher, genUpdate gM2.spuren 0 gW0'.spur,
    gM2.lauf ++ genEigen 0 [], gM2.start,
    gM2.welten ++ [gW0'], gM2.tiefe + 1⟩

/-- Step 3 (global witness): thread 0 fires the local assignment. -/
theorem gStep0 :
    PCSchritt gPr gO 0 gProg gM2 gPc2 0 gM3
      (pcAdvance gPc2 0) := by
  have hΛ : HeldGenau ([] : List (Res gD)) (offen (gM2.spuren 0)) := by
    have e : gM2.spuren 0 = [] := rfl
    rw [e]
    intro L
    simp only [List.not_mem_nil, offen]
  have hstep : (execStmt (D := gD)
      (V := Vertrag.vonSig gD (gD.signatur ())) gO 0
      keinRuf gStmt0 (gM2.weltVon 0) gRho0).welt = some gW0' := rfl
  have hneu : gW0'.spur = [] ++ gM2.spuren 0 := rfl
  have hkn : ∀ (L : gD.Lock) (h : List gD.Lock),
      Ereignis.nimmt L h ∉ ([] : List (Ereignis gD)) := by
    intro L h hm
    simp only [List.not_mem_nil] at hm
  have hpc : (gProg 0)[gPc2 0]? =
      some (PCAtom.leaf (D := gD) [] []) := rfl
  refine PCSchritt.leaf gM2 gPc2 0 (Vertrag.vonSig gD (gD.signatur ()))
    (l := false) (Γ := [.bool]) (Λ := []) (Λ' := []) (s := gStmt0)
    (ρ := gRho0) (σ' := gW0') (neu := []) (Λa := []) (cs := [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact hΛ
  · exact hstep
  · exact hneu
  · exact hkn
  · exact hpc
  · rfl
  · intro e he m st hm
    simp only [List.not_mem_nil] at he
  · intro e he o ho
    simp only [List.not_mem_nil] at he

/-- Thread 1 holds the lock after the global write. -/
theorem gHaelt1 : (() : gD.Lock) ∈ offen (gM2.spuren 1) := by
  have e : offen (gM2.spuren 1) = [()] := rfl
  rw [e]
  exact List.mem_singleton.mpr rfl

/-- The write moved the global: it reads `5` now. -/
theorem gW1w_glob5 : (gM2.speicher.globs ()).n = 5 := by rfl

/-- The start global reads `0`. -/
theorem gSp0_glob0 : (gSp0.globs ()).n = 0 := by rfl

/-- Memory really moved: the global went from `0` to `5`. -/
theorem gMoved : gM2.speicher.globs () ≠ gSp0.globs () := by
  intro hcon
  have hn : (gM2.speicher.globs ()).n = (gSp0.globs ()).n :=
    congrArg Zahl.n hcon
  rw [gW1w_glob5, gSp0_glob0] at hn
  exact absurd hn (by decide)

/-- **Inhabitation for `rely_aus_sperre_global`.** All premises hold
    jointly on `gD`: the PC run reaches `gM2` (lock, then the global
    write) with thread 1 holding the lock guarding the global, and a
    step of thread 0 (a local assignment) keeps the global.
    Non-degenerate: some function writes a table (`gTabWrite`) and the
    run moves the global from `0` to `5`. -/
theorem rely_aus_sperre_global_zeuge :
    (gM3.speicher.globs () = gM2.speicher.globs ()) ∧
    (gM2.speicher.globs () ≠ gSp0.globs ()) ∧
    (∃ f t, gD.schreibt f t = true) := by
  refine ⟨?_, gMoved, gTabWrite⟩
  exact rely_aus_sperre_global gPr gO 0 gO_gut gProg gSp0 gM2 gPc2
    gReach 1 0 (by decide) () gHaelt1 gM3 _ gStep0 () gGuardInst

/-! ## CUTS: what is not proved here
  - `sperre_exklusiv` lifts the take-time scheduler rule (`GenFrei`)
    to held-state disjointness; it does not relate held state to the
    run-level `ForeignExclusion` beyond sharing the `nimmt` rule.
  - `blatt_erhaelt_globs` covers `axiomCall` through the oracle frame
    plus `hgd`; the trace half of `GutO` is not needed and not used.
  - Both witnesses use hand-built thread programs (`witProg`,
    `gProg`) rather than extracted ones (`Extraktion.progAus`): the
    rely holds for every `PCProg`, so no extraction adequacy is owed.
  - The global witness program `gPr` carries trivial contracts; no
    contract discharge is claimed.
-/

#print axioms Gabbro.Grammatik.lese_globs_gleich
#print axioms Gabbro.Grammatik.storeGlob_fremd_global
#print axioms Gabbro.Grammatik.schreibSlot_globs_gleich
#print axioms Gabbro.Grammatik.merke_globs_gleich
#print axioms Gabbro.Grammatik.schreibBytes_globs_gleich
#print axioms Gabbro.Grammatik.blatt_erhaelt_globs
#print axioms Gabbro.Grammatik.sperre_exklusiv
#print axioms Gabbro.Grammatik.rely_aus_sperre
#print axioms Gabbro.Grammatik.rely_aus_sperre_zeuge
#print axioms Gabbro.Grammatik.rely_aus_sperre_global
#print axioms Gabbro.Grammatik.rely_aus_sperre_global_zeuge
