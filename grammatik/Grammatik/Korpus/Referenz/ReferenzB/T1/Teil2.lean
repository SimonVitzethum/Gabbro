module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineD
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Korpus.Referenz.ReferenzB.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- Step B fires the writing leaf `konto[0] := 100` on thread 1.
    The outcome and events are named from the `execStmt` equation for
    `assignSlot`, so the `blatt` constructor closes on `rfl` facts. -/
def refM2B : RufMaschineD refD :=
  ⟨(((refM1B.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)).schreibSlot () [Res.held (D := refD) ()]
      refK0 () refV100).speicher,
   rufUpdateD refM1B.faeden 1
     ⟨(refM1B.faeden 1).stapel,
      ⟨(refM1B.faeden 1).kopf.f, (refM1B.faeden 1).kopf.rho,
       (refM1B.faeden 1).kopf.s0,
       ⟨false, [.int 0 10], [Res.held (D := refD) ()],
        .cons (.call (V := vertragVon refD (refM1B.faeden 1).kopf.f)
          refLies refArgsLies
          (refHpLiesAt) rfl)
          (.ret .empty (by simp [Vertrag.ende]))⟩⟩,
      (((refM1B.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).schreibSlot () [Res.held (D := refD) ()]
        refK0 () refV100).spur,
      (refM1B.faeden 1).log⟩,
   refM1B.lauf ++ rufEigenD 1
     [Ereignis.zugriff () true [Res.held (D := refD) ()]
       (refM1B.weltVon 1).haelt],
   refM1B.start⟩

/-- The head statement of thread 1 is the write, followed by the call. -/
theorem refM1rest :
    (refM1B.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := refD) ()],
        .cons (refEin_start ▸ refWriteSt)
          (.cons (.call (V := vertragVon refD refEin) refLies refArgsLies
            refHpLiesAt rfl)
            (.ret .empty (by simp [Vertrag.ende])))⟩ := rfl

/-- Step B: thread 1 fires the write `konto[0] := 100`. Every `blatt`
    premise is a named `rfl` fact about the `assignSlot` equation. -/
theorem refSchrittB : RufSchrittD refP refO 0 refM1B 1 refM2B := by
  have hhead : (refM1B.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := refD) ()],
        .cons refWriteStAt
          (.cons (.call (V := vertragVon refD refEin) refLies refArgsLies
            refHpLiesAt rfl)
            (.ret .empty (by simp [Vertrag.ende])))⟩ := rfl
  have hstep : (execStmt refO 0 keinRuf refWriteStAt
      (refM1B.weltVon 1) refRho7).welt =
      some (((refM1B.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
        [Res.held (D := refD) ()] refK0 () refV100) := rfl
  have hneu : (((refM1B.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)).schreibSlot () [Res.held (D := refD) ()]
      refK0 () refV100).spur =
      [Ereignis.zugriff () true [Res.held (D := refD) ()]
        (refM1B.weltVon 1).haelt] ++ (refM1B.faeden 1).spur := rfl
  have hkn : ∀ (L : refD.Lock) (h : List refD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := refD) ()] (refM1B.weltVon 1).haelt] := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  exact RufSchrittD.blatt refM1B 1 false [.int 0 10]
    [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    refWriteStAt _ refRho7 rfl hhead refM1haelt _ _ hstep hneu hkn

theorem refReachB : RufErreichbarD refP refO 0 refM0B refM2B :=
  RufErreichbarD.schritt _ _ 1 refReachA refSchrittB

/-- Step C: thread 1 calls `lies`. The head residue after step B is the
    call; the argument reads (empty) leave the world unchanged, and the
    evaluated arguments are the empty environment.
    The `passes` index is `0`: the constructor leaves it implicit in the
    step shape, matched here by the `refM3B` unfolding. -/
def refPassB : Nat := 0


end Gabbro.Grammatik
