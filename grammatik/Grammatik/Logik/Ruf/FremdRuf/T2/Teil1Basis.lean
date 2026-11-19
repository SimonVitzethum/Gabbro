module

public import Grammatik.Logik.Ruf.FremdRuf.T1

@[expose] public section



namespace Gabbro.Grammatik

/-- After the leaf: memory carries `5` at slot `0`. -/
def fdPC1 : GenMaschine fdD :=
  ⟨(((fdPC0.weltVon 1).lese ([] : List (Res fdD))
      (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
      fdK0 () fdV5).speicher,
   genUpdate fdPC0.spuren 1
     (((fdPC0.weltVon 1).lese ([] : List (Res fdD))
       (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
       fdK0 () fdV5).spur,
   fdPC0.lauf ++ genEigen 1
     [Ereignis.zugriff () true ([] : List (Res fdD)) (fdPC0.weltVon 1).haelt],
   fdPC0.start,
   fdPC0.welten ++
     [((fdPC0.weltVon 1).lese ([] : List (Res fdD))
       (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
       fdK0 () fdV5],
   fdPC0.tiefe + 1⟩

/-- Firing the write from the start world stores `5` at slot `0`. -/
theorem fdPCwrite :
    (execStmt (D := fdD) (V := vertragVon fdD fdArbeit) fdO 0 keinRuf
      fdWriteSt (fdPC0.weltVon 1) Env.nil).welt =
      some (((fdPC0.weltVon 1).lese ([] : List (Res fdD))
        (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
        fdK0 () fdV5) := by rfl

/-- Thread 1 holds nothing at the start, as the leaf demands. -/
theorem fdPC1haelt :
    HeldGenau ([] : List (Res fdD)) (offen (fdPC0.spuren 1)) := by
  have e : offen (fdPC0.spuren 1) = [] := rfl
  rw [e]
  intro L
  exact nomatch L

/-- One PC step: thread 1 fires the writing leaf. -/
theorem fdPCschritt :
    PCSchritt fdP fdO 0 fdProg fdPC0 (fun _ => 0) 1 fdPC1
      (pcAdvance (fun _ => 0) 1) := by
  have hpc : (fdProg 1)[(fun _ => 0) 1]? =
      some (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := rfl
  have hneu : (((fdPC0.weltVon 1).lese ([] : List (Res fdD))
      (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
      fdK0 () fdV5).spur =
      [Ereignis.zugriff () true ([] : List (Res fdD))
        (fdPC0.weltVon 1).haelt] ++ fdPC0.spuren 1 := rfl
  have hkn : ∀ (L : fdD.Lock) (h : List fdD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true ([] : List (Res fdD))
        (fdPC0.weltVon 1).haelt] := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  have hmark : ∀ e ∈ [Ereignis.zugriff () true ([] : List (Res fdD))
      (fdPC0.weltVon 1).haelt], ∀ (m : fdD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := by
    intro e hm m st hlam
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.lambda, List.not_mem_nil] at hlam
  have hcar : ∀ e ∈ [Ereignis.zugriff () true ([] : List (Res fdD))
      (fdPC0.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers
          (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := by
    intro e hm o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.traeger, Option.some.injEq] at ho
    subst ho
    have hc : PCAtom.carriers (D := fdD)
        (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) =
        [Sum.inl (())] := rfl
    rw [hc]
    exact List.Mem.head _
  exact PCSchritt.leaf fdPC0 (fun _ => 0) 1
    (vertragVon fdD fdArbeit) false [] [] []
    fdWriteSt Env.nil rfl fdPC1haelt _ _ fdPCwrite hneu hkn
    [] [Sum.inl ()] hpc rfl hmark hcar

/-- The witness run from `GenStart`: the writing leaf. -/
theorem fdPC_erreicht :
    PCReach fdP fdO 0 fdProg (GenStart fdSp0) fdPC1
      (pcAdvance (fun _ => 0) 1) :=
  PCReach.step _ _ _ _ _ PCReach.start fdPCschritt

/-- The final memory carries `5` at slot `0`. -/
theorem fdPC_slot5 : fdPC1.speicher.slots () 0 () = fdV5 := by
  have hhit := storeSlot_hit (D := fdD)
    ((fdPC0.weltVon 1).lese ([] : List (Res fdD))
      (fdIdx.orte ++ fdVal5.orte)) () fdK0 () fdV5
  have k0 : fdK0 = (0 : Int) := rfl
  have hmem : fdPC1.speicher.slots () 0 () =
      ((((fdPC0.weltVon 1).lese ([] : List (Res fdD))
        (fdIdx.orte ++ fdVal5.orte)).storeSlot ()
        fdK0 () fdV5).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit

/-- Memory really moved: slot `0` reads `5`, the start reads `0`. -/
theorem fdPC_schreibt : fdPC1.speicher.slots () 0 () ≠
    fdSp0.slots () 0 () := by
  have h5 := fdPC_slot5
  have h0 : fdSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert fdD (fdD.typ () ())) := rfl
  rw [h5, h0]
  intro hcon
  have hn : (fdV5.n) = ((⟨0, by decide, by decide⟩ :
      Wert fdD (fdD.typ () ())).n) := congrArg Zahl.n hcon
  simp only [fdV5, Int.reduceEq] at hn

/-! ## 8. Witnesses: joint premises on a non-degenerate program -/

end Gabbro.Grammatik
