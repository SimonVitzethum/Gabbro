/- Part 2 of 3 of `ReferenzB` (split by instrumente/teile/lean-teilen.py; the umbrella `ReferenzB.lean` imports all parts). -/
import Grammatik.Korrespondenz.Allgemein.ReferenzB.T1

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
          (.ret .empty (by rfl))⟩ := rfl
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
        [Res.held (D := refD) ()] refK0 () refV100) := rfl

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
    simp at hm
  have hmark : ∀ e ∈ [Ereignis.zugriff () true [Res.held (D := refD) ()]
      (refPC1pre.weltVon 1).haelt], ∀ (m : refD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf [Res.held (D := refD) ()]
          [Sum.inl (())]) := by
    intro e hm m st hlam
    simp at hm
    subst hm
    simp [Ereignis.lambda] at hlam
  have hcar : ∀ e ∈ [Ereignis.zugriff () true [Res.held (D := refD) ()]
      (refPC1pre.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf [Res.held (D := refD) ()]
          [Sum.inl (())]) := by
    intro e hm o ho
    simp at hm
    subst hm
    simp [Ereignis.traeger] at ho
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
  simp [refV100] at hn

/-! ## 7. The call-machine run on RufMaschineF: lock, write, call, return

    The D-machine run of section 5 stops at the call (`refReachC`): its
    `rueck` step needs frame equalities the D design cannot supply (no
    stored environment, entry-world projection -- see CUTS). The F machine
    stores each frame's local environment next to its residue and compares
    frames only by (function, parameters, entry world), so the same bodies
    go through: thread 1 takes the lock, fires the writing leaf, calls
    `lies`, and returns the post-write slot value through the read world.
    Proof pattern follows `schritt1F`/`schritt2F`/`schritt3F` in
    RufMaschineF.lean; order differs (write before call) because the kept
    `refP` puts the write first in the `einzahlen` body. -/

/-- Thread start for the F run: thread 0 runs `lies`, thread 1 runs
    `einzahlen 7`. -/
def initB : Faden → Σ f : refD.Fn, Env refD (refD.params f)
  | 0 => ⟨refLies, Env.nil⟩
  | _ => ⟨refEin, refRho7⟩

/-- The start machine for the F witness run. -/
def refM0F : RufMaschineF refD := RufStartF refP refSp0 initB

/-- The lock is free at the F start: every trace is empty. -/
theorem refFrei0F : RufFreiF refM0F 1 (()) := by
  intro g hne hmem
  have e : (refM0F.faeden g).spur = [] := rfl
  have hnil : offen (refM0F.faeden g).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing yet at the F start. -/
theorem refSelf0F : (() : refD.Lock) ∉ offen (refM0F.faeden 1).spur := by
  intro hmem
  have e : (refM0F.faeden 1).spur = [] := rfl
  have hnil : offen (refM0F.faeden 1).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing, so the rank side is vacuous. -/
theorem refRang0F (K : refD.Lock) (hK : K ∈ offen (refM0F.faeden 1).spur) :
    refD.rang K < refD.rang (()) := by
  have e : (refM0F.faeden 1).spur = [] := rfl
  have hnil : offen ([] : List (Ereignis refD)) = [] := rfl
  rw [e, hnil, List.mem_nil_iff] at hK
  exact absurd hK (by decide)

/-- Step A (F): thread 1 takes the lock. -/
def refM1F : RufMaschineF refD :=
  ⟨refM0F.speicher,
   rufUpdateF refM0F.faeden 1
     ⟨(refM0F.faeden 1).stapel, (refM0F.faeden 1).kopf,
      Ereignis.nimmt () (offen (refM0F.faeden 1).spur) :: (refM0F.faeden 1).spur,
      (refM0F.faeden 1).log⟩,
   refM0F.lauf ++ rufEigenF 1 [Ereignis.nimmt () (offen (refM0F.faeden 1).spur)],
   refM0F.start⟩

theorem refSchrittAF :
    RufSchrittF refP refO 0 refM0F 1 refM1F := by
  unfold refM1F
  exact RufSchrittF.nimmt refM0F 1 () refSelf0F (fun K hK => refRang0F K hK)
    refFrei0F

theorem refReachAF : RufErreichbarF refP refO 0 refM0F refM1F :=
  RufErreichbarF.schritt _ _ 1 RufErreichbarF.start refSchrittAF

/-- Thread 1 head still runs `einzahlen` after taking the lock (F). -/
theorem refM1Fkopf : (refM1F.faeden 1).kopf.f = refEin := rfl

/-- Thread 1 holds the lock exactly after step A (F). -/
theorem refM1Fhaelt :
    HeldGenau [Res.held (D := refD) ()]
      (offen (refM1F.faeden 1).spur) := by
  intro L
  have eL : L = () := by cases L <;> rfl
  have eH : offen (refM1F.faeden 1).spur = [()] := rfl
  rw [eH, eL]
  constructor
  · intro hL
    have heq : Res.held (D := refD) L = Res.held (D := refD) () :=
      (List.mem_singleton.mp hL)
    cases heq
    exact List.mem_singleton.mpr rfl
  · intro hL
    have heq : L = () :=
      (List.mem_singleton.mp (eH ▸ hL))
    cases heq
    exact List.mem_singleton.mpr rfl

/-- Step B (F): thread 1 fires the writing leaf `konto[0] := 100` under
    the STORED `refRho7`; the outcome stores the same environment. -/
def refM2F : RufMaschineF refD :=
  ⟨(((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)).schreibSlot () [Res.held (D := refD) ()]
      refK0 () refV100).speicher,
   rufUpdateF refM1F.faeden 1
     ⟨(refM1F.faeden 1).stapel,
      ⟨(refM1F.faeden 1).kopf.f, (refM1F.faeden 1).kopf.rho,
       (refM1F.faeden 1).kopf.s0,
       ⟨false, [.int 0 10], [Res.held (D := refD) ()], refRho7,
        .cons (.call (V := vertragVon refD refEin) refLies refArgsLies
          refHpLiesAt rfl)
          (.ret .empty (by rfl))⟩⟩,
      (((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).schreibSlot () [Res.held (D := refD) ()]
        refK0 () refV100).spur,
      (refM1F.faeden 1).log⟩,
   refM1F.lauf ++ rufEigenF 1
     [Ereignis.zugriff () true [Res.held (D := refD) ()]
       (refM1F.weltVon 1).haelt],
   refM1F.start⟩

theorem refSchrittBF : RufSchrittF refP refO 0 refM1F 1 refM2F := by
  have hhead : (refM1F.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := refD) ()], refRho7,
        .cons refWriteStAt
          (.cons (.call (V := vertragVon refD refEin) refLies refArgsLies
            refHpLiesAt rfl)
            (.ret .empty (by rfl)))⟩ := rfl
  have hstep : (execStmt refO 0 keinRuf refWriteStAt
      (refM1F.weltVon 1) refRho7) =
      Ausgang.ok (D := refD) (V := vertragVon refD refEin)
        (((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
          (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
          [Res.held (D := refD) ()] refK0 () refV100) refRho7 := rfl
  have hneu : (((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)).schreibSlot () [Res.held (D := refD) ()]
      refK0 () refV100).spur =
      [Ereignis.zugriff () true [Res.held (D := refD) ()]
        (refM1F.weltVon 1).haelt] ++ (refM1F.faeden 1).spur := rfl
  have hkn : ∀ (L : refD.Lock) (h : List refD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := refD) ()] (refM1F.weltVon 1).haelt] := by
    intro L h hm
    simp at hm
  exact RufSchrittF.blatt refM1F 1 false [.int 0 10]
    [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    refWriteStAt _ refRho7 rfl hhead refM1Fhaelt _ _ _ hstep hneu hkn

theorem refReachBF : RufErreichbarF refP refO 0 refM0F refM2F :=
  RufErreichbarF.schritt _ _ 1 refReachAF refSchrittBF

/-- Step C (F): thread 1 calls `lies`. The head residue after step B is
    the call under the stored `refRho7`; the argument reads (empty) leave
    the world unchanged, and the evaluated arguments are `Env.nil`. -/
def refM3F : RufMaschineF refD :=
  ⟨refM2F.speicher,
   rufUpdateF refM2F.faeden 1
     ⟨(refM2F.faeden 1).kopf :: (refM2F.faeden 1).stapel,
      ⟨refLies, Env.nil, refM2F.weltVon 1,
       ⟨false, refD.params refLies,
        Signatur.anfang refD (refD.signatur refLies),
        Env.nil, refP.rumpf refLies⟩⟩,
      (refM2F.weltVon 1).spur,
      (RufEreignisF.eintritt refLies Env.nil (refM2F.weltVon 1)) ::
        (refM2F.faeden 1).log⟩,
   refM2F.lauf ++ rufEigenF 1 [],
   refM2F.start⟩

/-- After step B, thread 1 holds the lock exactly (F). -/
theorem refM2Fhaelt :
    HeldGenau [Res.held (D := refD) ()]
      (offen (refM2F.faeden 1).spur) := by
  have e : offen (refM2F.faeden 1).spur =
      offen (refM1F.faeden 1).spur := rfl
  rw [e]
  exact refM1Fhaelt

theorem refSchrittCF : RufSchrittF refP refO 0 refM2F 1 refM3F := by
  have hhead : (refM2F.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := refD) ()], refRho7,
        .cons (.call (V := vertragVon refD refEin) refLies refArgsLies
          refHpLiesAt rfl)
          (.ret .empty (by rfl))⟩ := rfl
  have hs0 : refM2F.weltVon 1 =
      (refM2F.weltVon 1).lese [Res.held (D := refD) ()]
        (Args.orte refArgsLies) := rfl
  have hrho : (Env.nil : Env refD (refD.params refLies)) =
      evalArgs (refM2F.weltVon 1) refArgsLies (refM2F.weltVon 1) refRho7 := rfl
  have hneu : (refM2F.weltVon 1).spur =
      [] ++ (refM2F.faeden 1).spur := rfl
  have hΛ : HeldGenau [Res.held (D := refD) ()]
      (offen (refM2F.faeden 1).spur) := refM2Fhaelt
  exact RufSchrittF.ruf (P := refP) (O := refO) (passes := 0) refM2F 1
    false [.int 0 10] [Res.held (D := refD) ()]
    refLies refArgsLies refHpLiesAt rfl _ refRho7 hhead hΛ _
    hs0 _ hrho _ hneu

theorem refReachCF : RufErreichbarF refP refO 0 refM0F refM3F :=
  RufErreichbarF.schritt _ _ 1 refReachBF refSchrittCF

/-- The caller frame waiting under the `lies` call (F): start entry
    world, stored environment `refRho7`, residue past the write. -/
def refCallerFF : RufRahmenF refD :=
  ⟨refEin, refRho7, refSp0.welt [],
   ⟨false, [.int 0 10], [Res.held (D := refD) ()], refRho7,
    .cons (.call (V := vertragVon refD refEin) refLies refArgsLies
      refHpLiesAt rfl)
      (.ret .empty (by rfl))⟩⟩

/-- The return value: the cap `100` at the `lies` result type. -/
def refV100back : ErgVal refD (refD.erg refLies) :=
  refLies_erg.symm ▸ refV100

/-- Step D (F): thread 1 returns from `lies`. The return reads the slot,
    so the return world is the READ world `(weltVon).lese Λ e.orte` with
    its read event; the value is the post-write cap `100`. -/
def MB : RufMaschineF refD :=
  ⟨(refM3F.weltVon 1).speicher,
   rufUpdateF refM3F.faeden 1
     ⟨[], refCallerFF,
      ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())]).spur,
      (RufEreignisF.rueck refLies Env.nil refV100back
        (refM3F.faeden 1).kopf.s0
        ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())])) ::
        (refM3F.faeden 1).log⟩,
   refM3F.lauf ++ rufEigenF 1
     [Ereignis.zugriff () false [Res.held (D := refD) ()]
       (refM3F.weltVon 1).haelt],
   refM3F.start⟩

/-- The `lies` return expression: the slot read as a result. -/
def refRetLies : ErgExpr refD [] (Signatur.anfang refD (refD.signatur refLies))
    (refD.erg refLies) :=
  .val (.slot () () refIdxBodyLies refDarfBodyLies)

/-- The return reads the table (one carrier). -/
theorem refRetLies_orte : ErgExpr.orte refRetLies = [Sum.inl (())] := rfl

/-- After step C the head runs `lies` with the empty environment (F). -/
theorem refM3Frho : (refM3F.faeden 1).kopf.rho = Env.nil := rfl

/-- After step C the head residue is the `lies` return (F). -/
theorem refM3Frest :
    (refM3F.faeden 1).kopf.rest =
      ⟨false, refD.params refLies,
        Signatur.anfang refD (refD.signatur refLies),
        Env.nil, refP.rumpf refLies⟩ := rfl

/-- Step D (F): thread 1 returns from `lies` with value `100`, read from
    the post-write slot through the read world. Every premise is used:
    `hpop`/`hfg`/`hrho`/`hs0` select the head frame, `hΛ` the lock state,
    `hs1`/`hv`/`hneu` feed the constructor. -/
theorem refSchrittDF : RufSchrittF refP refO 0 refM3F 1 MB := by
  have hpop : (refM3F.faeden 1).stapel = [refCallerFF] := rfl
  have hhead : (refM3F.faeden 1).kopf.rest =
      ⟨false, refD.params refLies,
        Signatur.anfang refD (refD.signatur refLies),
        Env.nil, .ret refRetLies (by rfl)⟩ := by
    rw [refM3Frest]
    rfl
  have hfg : (refM3F.faeden 1).kopf.f = refLies := rfl
  have hrho : (refM3F.faeden 1).kopf.rho =
      (refLies_params ▸ Env.nil : Env refD (refD.params refLies)) := refM3Frho
  have hs0 : (refM3F.faeden 1).kopf.s0 = refM2F.weltVon 1 := rfl
  have hΛ : HeldGenau (Signatur.anfang refD (refD.signatur refLies))
      (offen (refM3F.faeden 1).spur) := by
    have e : offen (refM3F.faeden 1).spur =
        offen (refM1F.faeden 1).spur := rfl
    rw [e, refLies_start]
    exact refM1Fhaelt
  have hs1 : ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())]) =
      (refM3F.weltVon 1).lese (Signatur.anfang refD (refD.signatur refLies))
        (ErgExpr.orte refRetLies) := rfl
  have hv : refV100back =
      hfg ▸ evalErg ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())])
        refRetLies
        ((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())])
        Env.nil := rfl
  have hneu : (((refM3F.weltVon 1).lese [Res.held (D := refD) ()] [Sum.inl (())])).spur =
      [Ereignis.zugriff () false [Res.held (D := refD) ()]
        (refM3F.weltVon 1).haelt] ++ (refM3F.faeden 1).spur := rfl
  exact RufSchrittF.rueck (P := refP) (O := refO) (passes := 0) refM3F 1
    _ [] hpop _ _ _ _ _ hhead _ hfg _ hrho _ hs0 hΛ _
    hs1 _ hv _ hneu

theorem refReachDF : RufErreichbarF refP refO 0 refM0F MB :=
  RufErreichbarF.schritt _ _ 1 refReachCF refSchrittDF

/-- `refM0F` IS the start machine. -/
theorem refM0F_start : refM0F = RufStartF refP refSp0 initB := rfl

/-- The F witness run: lock, writing leaf, call, return -- reached from
    the start state. -/
theorem refB_erreicht :
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB := by
  rw [← refM0F_start]
  exact refReachDF

/-- The final memory carries the written cap at `konto[0]`. -/
theorem refMB_slot : MB.speicher.slots () 0 () = refV100 := by
  have hhit := storeSlot_hit (D := refD)
    ((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) () refK0 () refV100
  have k0 : refK0 = (0 : Int) := rfl
  have hmem : MB.speicher.slots () 0 () =
      ((((refM1F.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).storeSlot ()
        refK0 () refV100).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit


end Gabbro.Grammatik
