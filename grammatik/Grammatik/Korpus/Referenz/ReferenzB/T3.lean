/- Part 3 of 3 of `ReferenzB` (split by instrumente/teile/lean-teilen.py; the umbrella `ReferenzB.lean` imports all parts). -/
import Grammatik.Korpus.Referenz.ReferenzB.T2

namespace Gabbro.Grammatik

/-- Memory really moved: `konto[0]` reads `100`, the start reads `0`. -/
theorem refB_schreibt : MB.speicher.slots () 0 () ≠
    refSp0.slots () 0 () := by
  have h100 := refMB_slot
  have h0 : refSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert refD (refD.typ () ())) := rfl
  rw [h100, h0]
  intro hcon
  have hn : (refV100.n) = ((⟨0, by decide, by decide⟩ :
      Wert refD (refD.typ () ())).n) := congrArg Zahl.n hcon
  simp only [refV100, Int.reduceEq] at hn

/-- Witness for `refB_schreibt`: the premises of the reached run are
    instantiated JOINTLY -- the concrete machine `MB` reached from the
    start state with a memory-changing step (slot `0 -> 100`). The run is
    NON-DEGENERATE: one table that the leaf writes (`refSchrittBF` via
    `execStmt`) and four reached steps (`nimmt`, writing `blatt`, `ruf`,
    `rueck`). Both conjuncts are used. -/
theorem refB_schreibt_zeuge : ∃ (M : RufMaschineF refD),
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
    M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨MB, refB_erreicht, refB_schreibt⟩

/-! ## 8. The PC run from `GenStart`: lock, then the writing leaf -/

/-- Thread program for the PC run: thread 1 takes the lock, then fires
    the writing leaf; thread 0 rests. -/
def refB_prog : PCProg refD
  | 1 => [.take (), .leaf [Res.held (D := refD) ()] [Sum.inl (())]]
  | _ => []

/-- Counter after the lock step on thread 1. -/
def refB_pc1 : PCStand := pcAdvance (fun _ => 0) 1

/-- Counter after the leaf step on thread 1. -/
def refB_pc2 : PCStand := pcAdvance refB_pc1 1

/-- Step 1 (PC): thread 1 takes the lock from the start machine. -/
theorem refB_pc_take :
    PCSchritt refP refO 0 refB_prog (GenStart refSp0) (fun _ => 0) 1
      refPC1pre refB_pc1 := by
  have hself : (() : refD.Lock) ∉ offen ((GenStart refSp0).spuren 1) := by
    intro hmem
    have e : ((GenStart refSp0).spuren 1) = [] := rfl
    have hnil : offen ((GenStart refSp0).spuren 1) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hrang : ∀ K ∈ offen ((GenStart refSp0).spuren 1),
      refD.rang K < refD.rang (()) := by
    intro K hK
    have e : ((GenStart refSp0).spuren 1) = [] := rfl
    have hnil : offen ([] : List (Ereignis refD)) = [] := rfl
    rw [e, hnil, List.mem_nil_iff] at hK
    exact absurd hK (by decide)
  have hfrei : GenFrei (GenStart refSp0) 1 (()) := by
    intro g hne hmem
    have e : ((GenStart refSp0).spuren g) = [] := rfl
    have hnil : offen ((GenStart refSp0).spuren g) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hpc : (refB_prog 1)[(fun _ => 0) 1]? =
      some (PCAtom.take (D := refD) ()) := rfl
  exact PCSchritt.take (GenStart refSp0) (fun _ => 0) 1 ()
    hself hrang hfrei hpc

/-- Step 2 (PC): thread 1 fires the writing leaf at position 1. -/
theorem refB_pc_leaf :
    PCSchritt refP refO 0 refB_prog refPC1pre refB_pc1 1 refPC2 refB_pc2 := by
  have hpc : (refB_prog 1)[refB_pc1 1]? =
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

/-- The PC witness run from `GenStart`: lock, then the writing leaf. -/
theorem refB_pc_erreicht :
    PCReach refP refO 0 refB_prog (GenStart refSp0) refPC2 refB_pc2 := by
  have h1 : PCReach refP refO 0 refB_prog (GenStart refSp0) refPC1pre
      refB_pc1 :=
    PCReach.step _ _ _ _ _ PCReach.start refB_pc_take
  exact PCReach.step _ _ _ _ _ h1 refB_pc_leaf

/-- Memory really moved on the PC run: `konto[0]` reads `100`. -/
theorem refB_pc_schreibt : refPC2.speicher.slots () 0 () ≠
    refSp0.slots () 0 () :=
  refPCschreibt_zeuge

/-- Witness for `refB_pc_schreibt`: the reached PC machine, its counter,
    the reachability, and the memory move, instantiated JOINTLY. The run
    is NON-DEGENERATE: one table that the leaf writes (`refB_pc_leaf` via
    `execStmt`) and two reached steps. All conjuncts are used. -/
theorem refB_pc_schreibt_zeuge : ∃ (M : GenMaschine refD) (pc : PCStand),
    PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
    M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

/-! ## CUTS:
  - COMPLETE (attempt B of 2, continued on RufMaschineF): `refD`/`refP`/
    `refO`/`refO_gut`/`refSp0` are kept unchanged. The F-machine run
    reaches `MB` from `RufStartF refP refSp0 initB` through `nimmt` (step
    A), the writing `blatt` (step B), `ruf` (step C), and `rueck`
    (step D) with `refB_erreicht` proved; `refB_schreibt` (slot `0 -> 100`)
    with `refB_schreibt_zeuge`. The PC run reaches `refPC2` from
    `GenStart refSp0` through `take` and the writing leaf with
    `refB_pc_erreicht` proved; `refB_pc_schreibt` with
    `refB_pc_schreibt_zeuge`. The F design fixes both D blockages below:
    frames carry their local environment (no free `rho`), and the return
    world is the read world, so a return that reads the slot is fine.
  - The D-machine run of section 5 is KEPT as the documented negative
    result: it stops at the call (`refReachC`) because (1) the popped
    caller frame would need its entry world to equal the post-write
    world (false as stated), and (2) `ErgExpr.orte` of the `lies` return
    is `[.inl ()]`, not `[]`, so the return world cannot be the thread
    world. Both are artefacts of the D design (free `rho`, no stored
    environment), fixed by the F machine -- not model gaps.
  - No contract discharge: neither machine gates on contracts, and no
    theorem connects `rueck` events to `ReqAmEintritt`/`EnsAmRueck`.
-/

#print axioms Gabbro.Grammatik.refD
#print axioms Gabbro.Grammatik.refO_gut
#print axioms Gabbro.Grammatik.refReachC
#print axioms Gabbro.Grammatik.refPCschritt
#print axioms Gabbro.Grammatik.refPCschreibt
#print axioms Gabbro.Grammatik.refPCschreibt_zeuge
#print axioms Gabbro.Grammatik.refB_erreicht
#print axioms Gabbro.Grammatik.refB_schreibt
#print axioms Gabbro.Grammatik.refB_schreibt_zeuge
#print axioms Gabbro.Grammatik.refB_pc_erreicht
#print axioms Gabbro.Grammatik.refB_pc_schreibt
#print axioms Gabbro.Grammatik.refB_pc_schreibt_zeuge


end Gabbro.Grammatik
