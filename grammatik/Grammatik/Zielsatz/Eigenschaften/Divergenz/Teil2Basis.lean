module

public import Grammatik.Zielsatz.Eigenschaften.NeverAsm
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
public import Grammatik.Zielsatz.Eigenschaften.Divergenz.Teil1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik

/-- Start slot value: `0`. -/
theorem divSp0_slot :
    divSp0.slots () 0 () = (⟨0, by decide, by decide⟩ :
      Wert divD (divD.typ () ())) := by rfl

/-- Thread start: thread 0 runs `lies`, thread 1 runs `schreib 7`. -/
def divInit : Faden → Σ f : divD.Fn, Env divD (divD.params f)
  | 0 => ⟨divLies, Env.nil⟩
  | _ => ⟨divSchreib, divRho7⟩

/-! ## 6. The witness run: lock, write, then the head stands at `forever` -/

/-- The start machine for the witness run. -/
def divM0F : RufMaschineF divD := RufStartF divP divSp0 divInit

/-- The lock is free at the start: every trace is empty. -/
theorem divFrei0F : RufFreiF divM0F 1 (()) := by
  intro g hne hmem
  have e : (divM0F.faeden g).spur = [] := rfl
  have hnil : offen (divM0F.faeden g).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List divD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing yet. -/
theorem divSelf0F : (() : divD.Lock) ∉ offen (divM0F.faeden 1).spur := by
  intro hmem
  have e : (divM0F.faeden 1).spur = [] := rfl
  have hnil : offen (divM0F.faeden 1).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List divD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing, so the rank side is vacuous. -/
theorem divRang0F (K : divD.Lock) (hK : K ∈ offen (divM0F.faeden 1).spur) :
    divD.rang K < divD.rang (()) := by
  have e : (divM0F.faeden 1).spur = [] := rfl
  have hnil : offen ([] : List (Ereignis divD)) = [] := rfl
  rw [e, hnil, List.mem_nil_iff] at hK
  exact absurd hK (by decide)

/-- Step A: thread 1 takes the lock. -/
def divM1F : RufMaschineF divD :=
  ⟨divM0F.speicher,
   rufUpdateF divM0F.faeden 1
     ⟨(divM0F.faeden 1).stapel, (divM0F.faeden 1).kopf,
      Ereignis.nimmt () (offen (divM0F.faeden 1).spur) :: (divM0F.faeden 1).spur,
      (divM0F.faeden 1).log⟩,
   divM0F.lauf ++ rufEigenF 1 [Ereignis.nimmt () (offen (divM0F.faeden 1).spur)],
   divM0F.start⟩

theorem divSchrittAF :
    RufSchrittF divP divO 0 divM0F 1 divM1F := by
  unfold divM1F
  exact RufSchrittF.nimmt divM0F 1 () divSelf0F (fun K hK => divRang0F K hK)
    divFrei0F

theorem divReachAF : RufErreichbarF divP divO 0 divM0F divM1F :=
  RufErreichbarF.schritt _ _ 1 RufErreichbarF.start divSchrittAF

/-- Thread 1 holds the lock exactly after step A. -/
theorem divM1Fhaelt :
    HeldGenau [Res.held (D := divD) ()]
      (offen (divM1F.faeden 1).spur) := by
  intro L
  have eL : L = () := by cases L <;> rfl
  have eH : offen (divM1F.faeden 1).spur = [()] := rfl
  rw [eH, eL]
  constructor
  · intro hL
    have heq : Res.held (D := divD) L = Res.held (D := divD) () :=
      (List.mem_singleton.mp hL)
    cases heq
    exact List.mem_singleton.mpr rfl
  · intro hL
    have heq : L = () :=
      (List.mem_singleton.mp (eH ▸ hL))
    cases heq
    exact List.mem_singleton.mpr rfl

/-- The evaluated index: `0`. -/
def divK0 : Int := 0

/-- The evaluated cap: `100` in range. -/
def divV100 : Wert divD (.int 0 100) := ⟨100, by decide, by decide⟩

/-- Step B: thread 1 fires the writing leaf `konto[0] := 100`. The head
    after the step stands at the diverging `forever`. -/
def divM2F : RufMaschineF divD :=
  ⟨(((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
      divK0 () divV100).speicher,
   rufUpdateF divM1F.faeden 1
     ⟨(divM1F.faeden 1).stapel,
      ⟨(divM1F.faeden 1).kopf.f, (divM1F.faeden 1).kopf.rho,
       (divM1F.faeden 1).kopf.s0,
       ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
        .cons divSchleife (.ret .empty (by rfl))⟩⟩,
      (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
        (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
        divK0 () divV100).spur,
      (divM1F.faeden 1).log⟩,
   divM1F.lauf ++ rufEigenF 1
     [Ereignis.zugriff () true [Res.held (D := divD) ()]
       (divM1F.weltVon 1).haelt],
   divM1F.start⟩

theorem divSchrittBF : RufSchrittF divP divO 0 divM1F 1 divM2F := by
  have hhead : (divM1F.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
        .cons divWriteStAt
          (.cons divSchleife (.ret .empty (by rfl)))⟩ := rfl
  have hstep : (execStmt divO 0 keinRuf divWriteStAt
      (divM1F.weltVon 1) divRho7) =
      Ausgang.ok (D := divD) (V := vertragVon divD divSchreib)
        (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
          (divIdx.orte ++ divHundert.orte)).schreibSlot ()
          [Res.held (D := divD) ()] divK0 () divV100) divRho7 := rfl
  have hneu : (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
      divK0 () divV100).spur =
      [Ereignis.zugriff () true [Res.held (D := divD) ()]
        (divM1F.weltVon 1).haelt] ++ (divM1F.faeden 1).spur := rfl
  have hkn : ∀ (L : divD.Lock) (h : List divD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := divD) ()] (divM1F.weltVon 1).haelt] := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  exact RufSchrittF.blatt divM1F 1 false [.int 0 10]
    [Res.held (D := divD) ()] [Res.held (D := divD) ()]
    divWriteStAt _ divRho7 rfl hhead divM1Fhaelt _ _ _ hstep hneu hkn

theorem divReachBF : RufErreichbarF divP divO 0 divM0F divM2F :=
  RufErreichbarF.schritt _ _ 1 divReachAF divSchrittBF

/-- `divM0F` IS the start machine. -/
theorem divM0F_start : divM0F = RufStartF divP divSp0 divInit := by rfl

/-- The witness run: lock, then the writing leaf -- reached from start. -/
theorem divB_erreicht :
    RufErreichbarF divP divO 0 (RufStartF divP divSp0 divInit) divM2F := by
  rw [← divM0F_start]
  exact divReachBF

/-- The final memory carries the written cap at `konto[0]`. -/
theorem divMB_slot : divM2F.speicher.slots () 0 () = divV100 := by
  have hhit := storeSlot_hit (D := divD)
    ((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)) () divK0 () divV100
  have k0 : divK0 = (0 : Int) := rfl
  have hmem : divM2F.speicher.slots () 0 () =
      ((((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
        (divIdx.orte ++ divHundert.orte)).storeSlot ()
        divK0 () divV100).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit

end Gabbro.Grammatik.Zielsatz
