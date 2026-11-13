module

public import Grammatik.Korpus.Referenz.ReferenzB.T1.Teil1Basis
public import Grammatik.Logik.Ruf.Maschine.RufMaschineD
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF

@[expose] public section




namespace Gabbro.Grammatik

/-- `einzahlen` holds the lock: start equals end. -/
theorem refEin_start : Signatur.anfang refD (refD.signatur refEin) =
    [Res.held (D := refD) ()] := by rfl

/-- The call from `einzahlen` to `lies`: no arguments, the callee holds the
    same lock, writes nothing, needs nothing. Works at any holdings whose
    lock set is exactly `[()]` (the `hh` shape). -/
theorem refHpLiesAt :
    RufPasst refD (vertragVon refD refEin) (refD.signatur refLies)
      [Res.held (D := refD) ()] where
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _
    (OwnerFlow.empty_of_empty (refD.signatur refLies).owner)
  hw := fun t ht => by cases t <;> rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (by
    intro L
    have eH : (refD.signatur refLies).haelt = [()] := rfl
    constructor
    · intro hL
      have eL : L = () := by
        have hmem : Res.held (D := refD) L ∈ [Res.held (D := refD) ()] := hL
        have heq : Res.held (D := refD) L = Res.held (D := refD) () :=
          (List.mem_singleton.mp hmem)
        cases heq
        rfl
      rw [eH]
      exact eL ▸ List.mem_singleton.mpr rfl
    · intro hL
      have eL : L = () := by
        have hmem : L ∈ [()] := by rw [← eH]; exact hL
        exact (List.mem_singleton.mp hmem)
      show Res.held (D := refD) _ ∈ _
      rw [eL]
      exact List.mem_singleton.mpr rfl)
  hx := RufPasst.hx_von (by
    intro L
    have eH : (refD.signatur refLies).haelt = [()] := rfl
    constructor
    · intro hL
      have eL : L = () := by
        have hmem : Res.held (D := refD) L ∈ [Res.held (D := refD) ()] := hL
        have heq : Res.held (D := refD) L = Res.held (D := refD) () :=
          (List.mem_singleton.mp hmem)
        cases heq
        rfl
      rw [eH]
      exact eL ▸ List.mem_singleton.mpr rfl
    · intro hL
      have eL : L = () := by
        have hmem : L ∈ [()] := by rw [← eH]; exact hL
        exact (List.mem_singleton.mp hmem)
      show Res.held (D := refD) _ ∈ _
      rw [eL]
      exact List.mem_singleton.mpr rfl)

/-- No arguments for the `lies` call. -/
def refArgsLies :
    Args refD [.int 0 10] [Res.held (D := refD) ()] (refD.params refLies) :=
  Args.nil

/-- The `einzahlen` write: `konto[0] := 100`. -/
def refWriteSt : Stmt refD (vertragVon refD refEin) false [.int 0 10]
    (vertragVon refD refEin).ende (vertragVon refD refEin).ende :=
  .assignSlot () () refIdxEin refHundert (by cases () <;> rfl) refDarfEin

/-- `einzahlen` write: `konto[0] := 100`, at the lock holdings. -/
def refWriteStAt : Stmt refD (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()] [Res.held (D := refD) ()] :=
  refEin_ende ▸ refWriteSt

/-- `einzahlen` body: write the cap, call `lies`, return. -/
def refRumpfEin :
    Endblock refD (vertragVon refD refEin) false [.int 0 10]
      [Res.held (D := refD) ()] :=
  .cons refWriteStAt
    (.cons (.call (V := vertragVon refD refEin) refLies refArgsLies
      refHpLiesAt rfl)
      (.ret .empty (by first | exact List.Perm.refl _ | (simp [Vertrag.ende, nach, nachSig, Signatur.anfang, vertragVon, Vertrag.vonSig]))))

/-- `lies` holds the lock: start equals end. -/
theorem refLies_start : Signatur.anfang refD (refD.signatur refLies) =
    [Res.held (D := refD) ()] := by rfl

/-- Index `0` in the `lies` body context, at the start holdings. -/
def refIdxBodyLies : Expr refD [] (Signatur.anfang refD (refD.signatur refLies))
    (.index (refD.count ())) :=
  refLies_start ▸ refIdxLies

/-- `lies` locks the table in its body context. -/
theorem refDarfBodyLies :
    darf refD () (Signatur.anfang refD (refD.signatur refLies)) := by
  rw [refLies_start]
  exact refDarf

/-- `lies` body: return `konto[0]`. -/
def refRumpfLies :
    Endblock refD (vertragVon refD refLies) false []
      (Signatur.anfang refD (refD.signatur refLies)) :=
  .ret (.val (.slot () () refIdxBodyLies refDarfBodyLies)) (by first | exact List.Perm.refl _ | (simp [Vertrag.ende, nach, nachSig, Signatur.anfang, vertragVon, Vertrag.vonSig]))

/-- The program: `true` requires, ensured non-decrease, write-call-return;
    `false` requires `true`, ensures result equality, slot return.
    Bodies are stated at the lock holdings and cast to the signature
    holdings (definitionally the same list). -/
def refP : Programm refD where
  invariante := fun i => nomatch i
  requires
    | true => refReqEin
    | false => refReqLies
  ensures
    | true => refEnsEin
    | false => refEnsLies
  rumpf
    | true => refEin_start ▸ refRumpfEin
    | false => refLies_start ▸ refRumpfLies

/-! ## 4. Oracle, memory, contracts at the place -/

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def refO : Orakel refD where
  wirktL := fun a => nomatch a
  regLiesL := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbarL := fun g => nomatch g

/-- The oracle is good: every conjunct closes on its empty domain. -/
theorem refO_gut : GutO refO := by
  intro a σ ρ
  exact nomatch a

/-- The start memory: slot `konto[0]` reads `0`, slot `konto[1]` reads `0`. -/
def refSp0 : Speicher refD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Start slot value: `0`. -/
theorem refSp0_slot :
    refSp0.slots () 0 () = (⟨0, by decide, by decide⟩ :
      Wert refD (refD.typ () ())) := by rfl

/-- `refP.rumpf` of `einzahlen` is the write-call-return body. -/
theorem refP_rumpf_ein : refP.rumpf refEin = refEin_start ▸ refRumpfEin := by rfl

/-- `refP.rumpf` of `lies` is the slot return. -/
theorem refP_rumpf_lies : refP.rumpf refLies = refLies_start ▸ refRumpfLies := by rfl

/-! ## 5. The call-machine run: lock, write, call, return -/

/-- Thread start: thread 0 runs `lies`, thread 1 runs `einzahlen 7`. -/
def refInitB : Faden → Σ f : refD.Fn, Env refD (refD.params f)
  | 0 => ⟨refLies, Env.nil⟩
  | _ => ⟨refEin, refRho7⟩

/-- The start machine for the witness run. -/
def refM0B : RufMaschineD refD :=
  RufStartD refP refSp0 refInitB

/-- The lock is free at the start: every trace is empty. -/
theorem refFrei0B : RufFreiD refM0B 1 (()) := by
  intro g hne hmem
  have e : (refM0B.faeden g).spur = [] := rfl
  have hnil : offen (refM0B.faeden g).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing yet. -/
theorem refSelf0B : (() : refD.Lock) ∉ offen (refM0B.faeden 1).spur := by
  intro hmem
  have e : (refM0B.faeden 1).spur = [] := rfl
  have hnil : offen (refM0B.faeden 1).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing, so the rank side is vacuous. -/
theorem refRang0B (K : refD.Lock) (hK : K ∈ offen (refM0B.faeden 1).spur) :
    refD.rang K < refD.rang (()) := by
  have e : (refM0B.faeden 1).spur = [] := rfl
  have hnil : offen ([] : List (Ereignis refD)) = [] := rfl
  rw [e, hnil, List.mem_nil_iff] at hK
  exact absurd hK (by decide)

/-- Step A: thread 1 takes the lock. -/
def refM1B : RufMaschineD refD :=
  ⟨refM0B.speicher,
   rufUpdateD refM0B.faeden 1
     ⟨(refM0B.faeden 1).stapel, (refM0B.faeden 1).kopf,
      Ereignis.nimmt () (offen (refM0B.faeden 1).spur) :: (refM0B.faeden 1).spur,
      (refM0B.faeden 1).log⟩,
   refM0B.lauf ++ rufEigenD 1 [Ereignis.nimmt () (offen (refM0B.faeden 1).spur)],
   refM0B.start⟩

theorem refSchrittA :
    RufSchrittD refP refO 0 refM0B 1 refM1B := by
  unfold refM1B
  exact RufSchrittD.nimmt refM0B 1 () refSelf0B (fun K hK => refRang0B K hK)
    refFrei0B

theorem refReachA : RufErreichbarD refP refO 0 refM0B refM1B :=
  RufErreichbarD.schritt _ _ 1 RufErreichbarD.start refSchrittA

/-- Thread 1 head still runs `einzahlen` after taking the lock. -/
theorem refM1kopf : (refM1B.faeden 1).kopf.f = refEin := by rfl

/-- Thread 1 entry environment is the call argument. -/
theorem refM1rho : (refM1B.faeden 1).kopf.rho = refRho7 := by rfl

/-- Thread 1 holds the lock exactly after step A. -/
theorem refM1haelt :
    HeldGenau [Res.held (D := refD) ()]
      (offen (refM1B.faeden 1).spur) := by
  intro L
  have eL : L = () := by cases L <;> rfl
  have eH : offen (refM1B.faeden 1).spur = [()] := rfl
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

/-- The evaluated index: `0`. -/
def refK0 : Int := 0

/-- The evaluated cap: `100` in range. -/
def refV100 : Wert refD (.int 0 100) := ⟨100, by decide, by decide⟩

end Gabbro.Grammatik
