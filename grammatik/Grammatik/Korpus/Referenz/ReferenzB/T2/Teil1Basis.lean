module

public import Grammatik.Korpus.Referenz.ReferenzB.T1

@[expose] public section



namespace Gabbro.Grammatik

def refM3B : RufMaschineD refD :=
  ⟨refM2B.speicher,
   rufUpdateD refM2B.faeden 1
     ⟨(refM2B.faeden 1).kopf :: (refM2B.faeden 1).stapel,
      ⟨refLies, Env.nil, refM2B.weltVon 1,
       ⟨false, refD.params refLies,
        Signatur.anfang refD (refD.signatur refLies),
        refP.rumpf refLies⟩⟩,
      (refM2B.weltVon 1).spur,
      (RufEreignisD.eintritt refLies Env.nil (refM2B.weltVon 1)) ::
        (refM2B.faeden 1).log⟩,
   refM2B.lauf ++ rufEigenD 1 [],
   refM2B.start⟩

/-- After step B, thread 1 holds the lock exactly. -/
theorem refM2haelt :
    HeldGenau [Res.held (D := refD) ()]
      (offen (refM2B.faeden 1).spur) := by
  have e : offen (refM2B.faeden 1).spur =
      offen (refM1B.faeden 1).spur := rfl
  rw [e]
  exact refM1haelt

theorem refSchrittC : RufSchrittD refP refO 0 refM2B 1 refM3B := by
  have hhead : (refM2B.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := refD) ()],
        .cons (.call (V := vertragVon refD refEin) refLies refArgsLies
          refHpLiesAt rfl)
          (.ret .empty (by simp [Vertrag.ende]))⟩ := rfl
  have hs0 : refM2B.weltVon 1 =
      (refM2B.weltVon 1).lese [Res.held (D := refD) ()]
        (Args.orte refArgsLies) := rfl
  have hrho : (Env.nil : Env refD (refD.params refLies)) =
      evalArgs (refM2B.weltVon 1) refArgsLies (refM2B.weltVon 1) refRho7 := rfl
  have hneu : (refM2B.weltVon 1).spur =
      [] ++ (refM2B.faeden 1).spur := rfl
  have hΛ : HeldGenau [Res.held (D := refD) ()]
      (offen (refM2B.faeden 1).spur) := refM2haelt
  exact RufSchrittD.ruf (P := refP) (O := refO) (passes := 0) refM2B 1
    false [.int 0 10] [Res.held (D := refD) ()]
    refLies refArgsLies refHpLiesAt rfl _ refRho7 hhead hΛ _
    hs0 _ hrho _ hneu

theorem refReachC : RufErreichbarD refP refO 0 refM0B refM3B :=
  RufErreichbarD.schritt _ _ 1 refReachB refSchrittC

/-! ## 6. One PC step that writes `konto` -/

/-- Thread program: thread 1 fires a writing leaf at position 0, thread 0
    rests. The atom names the lock holdings and the written carrier. -/
def refProgB : PCProg refD
  | 1 => [.leaf [Res.held (D := refD) ()] [Sum.inl (())]]
  | _ => []

/-- The start machine for the PC run, over the reference memory. -/
def refPC0 : GenMaschine refD := GenStart refSp0

/-- Thread 1 holds the lock at the PC start: its trace takes the lock. -/
def refPC1pre : GenMaschine refD :=
  ⟨refSp0,
   genUpdate (refPC0.spuren) 1
     [Ereignis.nimmt (D := refD) () []],
   refPC0.lauf ++ genEigen 1 [Ereignis.nimmt (D := refD) () []],
   refPC0.start,
   refPC0.welten ++ [refSp0.welt [Ereignis.nimmt (D := refD) () []]],
   refPC0.tiefe + 1⟩

/-- Firing the reference write from the PC start world writes `100`. -/
theorem refPCwrite :
    (execStmt (D := refD) (V := vertragVon refD refEin) refO 0 keinRuf
      refWriteStAt (refPC1pre.weltVon 1) refRho7).welt =
      some (((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
        [Res.held (D := refD) ()] refK0 () refV100) := by rfl

/-- Thread 1 holds the lock at the PC start. -/
theorem refPC1haelt :
    HeldGenau [Res.held (D := refD) ()]
      (offen (refPC1pre.spuren 1)) := by
  have e : offen (refPC1pre.spuren 1) = [()] := rfl
  have h : HeldGenau [Res.held (D := refD) ()] [()] := by
    intro L
    constructor
    · intro hL
      have he : Res.held (D := refD) L = Res.held (D := refD) () :=
        (List.mem_singleton.mp hL)
      have eL : L = () := by cases he; rfl
      have hmem : L ∈ ([()] : List refD.Lock) := eL ▸ List.mem_singleton.mpr rfl
      exact hmem
    · intro hL
      have he : L = () := (List.mem_singleton.mp hL)
      have hmem : Res.held (D := refD) L ∈
          ([Res.held (D := refD) ()] : List (Res refD)) :=
        he ▸ List.mem_singleton.mpr rfl
      exact hmem
  rw [e]
  exact h

/-- One PC step: thread 1 fires the writing leaf at position 0. -/
def refPC2 : GenMaschine refD :=
  ⟨(((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
      [Res.held (D := refD) ()] refK0 () refV100).speicher,
   genUpdate refPC1pre.spuren 1
     (((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
       (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
       [Res.held (D := refD) ()] refK0 () refV100).spur,
   refPC1pre.lauf ++ genEigen 1
     [Ereignis.zugriff () true [Res.held (D := refD) ()]
       (refPC1pre.weltVon 1).haelt],
   refPC1pre.start,
   refPC1pre.welten ++
     [((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
       (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
       [Res.held (D := refD) ()] refK0 () refV100],
   refPC1pre.tiefe + 1⟩

theorem refPCschritt :
    PCSchritt refP refO 0 refProgB refPC1pre (fun _ => 0) 1 refPC2
      (pcAdvance (fun _ => 0) 1) := by
  have hpc : (refProgB 1)[(fun _ => 0) 1]? =
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
  exact PCSchritt.leaf refPC1pre (fun _ => 0) 1
    (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    refWriteStAt refRho7 rfl refPC1haelt _ _ refPCwrite hneu hkn
    [Res.held (D := refD) ()] [Sum.inl (())] hpc rfl hmark hcar

/-- The PC step starts from `GenStart`: the `nimmt` pre-step is a
    `GenSchritt`, and the leaf is a `PCSchritt` over it. The full
    `PCReach` chain from `GenStart` (with the lock pre-taken) is open:
    `refPC1pre` is hand-built, not reached. -/
theorem refPCschreibt : refPC2.speicher.slots () 0 () = refV100 := by
  have hhit := storeSlot_hit (D := refD)
    ((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) () refK0 () refV100
  have k0 : refK0 = (0 : Int) := rfl
  have hmem : refPC2.speicher.slots () 0 () =
      ((((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).storeSlot ()
        refK0 () refV100).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit

/-- The PC write really moved memory: slot `konto[0]` reads `100`,
    while the start memory reads `0`. -/
theorem refPCschreibt_zeuge : refPC2.speicher.slots () 0 () ≠
    refSp0.slots () 0 () := by
  have h100 := refPCschreibt
  have h0 : refSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert refD (refD.typ () ())) := rfl
  rw [h100, h0]
  intro hcon
  have hn : (refV100.n) = ((⟨0, by decide, by decide⟩ :
      Wert refD (refD.typ () ())).n) := congrArg Zahl.n hcon
  simp only [refV100, Int.reduceEq] at hn


end Gabbro.Grammatik
