/-
  File:      Grammatik/ReferenzB.lean
  Subject:   REFERENCE FIXTURE (attempt B) -- one shared table, one lock,
              two functions, reached runs on both machines that move memory.

  Design: `refD` has one table `konto` (2 slots, one `.int 0 100` field),
  one lock `m` guarding it (`braucht`), and two functions over `Bool` ids:
  `einzahlen` (`true`: one `.int 0 10` param, no result, writes) and `lies`
  (`false`: no params, returns `.int 0 100`, reads). The `einzahlen` body is
  straight-line `write; call lies; ret` so that, from `RufStartD`, thread 1
  fires `nimmt`, a writing `blatt`, `ruf`, `rueck` in that order (the call
  machine never unfolds compounds, so no `ite` appears: the write stores the
  constant cap `100`, the upper branch of the `min`).

  Later lanes build their rule-13 witnesses on `refD`/`refP`/`refO`/`refSp0`
  and the two reached runs below.
-/
import Grammatik.Logik.Ruf.Maschine.RufMaschineD
import Grammatik.Logik.Ruf.Maschine.RufMaschineF

namespace Gabbro.Grammatik

/-- Signature of `einzahlen`: one `.int 0 10` parameter, no result, holds
    the lock, may write the table. -/
def refSigEin : Signatur Unit Empty Unit Empty where
  params := [.int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Signature of `lies`: no parameters, one `.int 0 100` result, holds the
    lock, writes nothing. -/
def refSigLies : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The reference declaration: one table `konto` of 2 slots with one
    `.int 0 100` field, guarded by the single lock `m` (`braucht`);
    `einzahlen` is `true`, `lies` is `false`; both signatures line up by id.
    `geteilit` is true so the shared table is guarded, not orphaned. -/
def refD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => refSigEin | _ => refSigLies
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The two function ids: `einzahlen` (`true`) and `lies` (`false`). -/
def refEin : refD.Fn := show refD.Fn from true

def refLies : refD.Fn := show refD.Fn from false

/-- Parameters of `einzahlen`, by computation. -/
theorem refEin_params : refD.params refEin = [.int 0 10] := rfl

/-- `einzahlen` returns nothing. -/
theorem refEin_erg : refD.erg refEin = none := rfl

/-- Parameters of `lies`, by computation. -/
theorem refLies_params : refD.params refLies = [] := rfl

/-- `lies` returns `.int 0 100`. -/
theorem refLies_erg : refD.erg refLies = some (.int 0 100) := rfl

/-- The argument of the witness call: 7 in `.int 0 10`. -/
def refRho7 : Env refD (refD.params refEin) :=
  refEin_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env refD [.int 0 10])

/-- `einzahlen` writes the table. -/
theorem refEin_schreibt (t : refD.Tab) :
    (vertragVon refD refEin).schreibt t = true := by
  cases t <;> rfl

/-- `lies` writes nothing. -/
theorem refLies_schreibt (t : refD.Tab) :
    (refD.signatur refLies).schreibt t = false := by
  cases t <;> rfl

/-- `lies` holds the lock. -/
theorem refLies_haelt : (refD.signatur refLies).haelt = [()] := rfl

/-- `lies` has no error channel. -/
theorem refLies_gruende : refD.gruende refLies = 0 := rfl

/-- End holdings of `einzahlen`: the lock. -/
theorem refEin_ende :
    (vertragVon refD refEin).ende = [Res.held (D := refD) ()] := rfl

/-- End holdings of `lies`: the lock. -/
theorem refLies_ende :
    (vertragVon refD refLies).ende = [Res.held (D := refD) ()] := rfl

/-- The table access is allowed holding the lock. -/
theorem refDarf : darf refD () [Res.held (D := refD) ()] := by
  intro w h
  simp only [refD] at h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  have hh : w ∈ refD.braucht () := h
  rw [e] at hh ⊢
  exact List.mem_singleton.mpr rfl

/-- Same access right at the `einzahlen` end holdings. -/
theorem refDarfEin : darf refD () (vertragVon refD refEin).ende := by
  rw [refEin_ende]
  exact refDarf

/-- Same access right at the `lies` end holdings. -/
theorem refDarfLies : darf refD () (vertragVon refD refLies).ende := by
  rw [refLies_ende]
  exact refDarf

/-! ## 2. Expressions and contracts -/

/-- Index `0` into the two-slot table, in the `einzahlen` context. -/
def refIdxEin : Expr refD [.int 0 10] [Res.held (D := refD) ()]
    (.index (refD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- Index `0` in the `lies` body context. -/
def refIdxLies : Expr refD [] [Res.held (D := refD) ()]
    (.index (refD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The cap value `100` in range. -/
def refHundert : Expr refD [.int 0 10] [Res.held (D := refD) ()] (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 100)

/-- `einzahlen` requires `true`. -/
def refReqEin : Expr refD (refD.params refEin)
    (Signatur.anfang refD (refD.signatur refEin)) .bool :=
  .tru

/-- `einzahlen` ensures the slot did not decrease (`old ≤ new`). -/
def refEnsEin : Expr refD (ErgCtx (refD.params refEin) (refD.erg refEin))
    (vertragVon refD refEin).ende .bool :=
  .le (.oldS () () refIdxEin refDarfEin)
    (.slot () () refIdxEin refDarfEin)

/-- Index `0` in the `lies` ensures context (result before params). -/
def refIdxEnsLies :
    Expr refD (ErgCtx (refD.params refLies) (refD.erg refLies))
      (vertragVon refD refLies).ende (.index (refD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- `lies` requires `true`. -/
def refReqLies : Expr refD (refD.params refLies)
    (Signatur.anfang refD (refD.signatur refLies)) .bool :=
  .tru

/-- `lies` ensures `result = konto[0]`. -/
def refEnsLies : Expr refD (ErgCtx (refD.params refLies) (refD.erg refLies))
    (vertragVon refD refLies).ende .bool :=
  .eq (.var .here)
    (.slot () () refIdxEnsLies refDarfLies)

/-! ## 3. Bodies and the program -/

/-- `einzahlen` holds the lock: start equals end. -/
theorem refEin_start : Signatur.anfang refD (refD.signatur refEin) =
    [Res.held (D := refD) ()] := rfl

/-- The call from `einzahlen` to `lies`: no arguments, the callee holds the
    same lock, writes nothing, needs nothing. Works at any holdings whose
    lock set is exactly `[()]` (the `hh` shape). -/
theorem refHpLiesAt :
    RufPasst refD (vertragVon refD refEin) (refD.signatur refLies)
      [Res.held (D := refD) ()] where
  hw := fun t ht => by cases t <;> rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
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
      (.ret .empty (by rfl)))

/-- `lies` holds the lock: start equals end. -/
theorem refLies_start : Signatur.anfang refD (refD.signatur refLies) =
    [Res.held (D := refD) ()] := rfl

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
  .ret (.val (.slot () () refIdxBodyLies refDarfBodyLies)) (by rfl)

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
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

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
      Wert refD (refD.typ () ())) := rfl

/-- `refP.rumpf` of `einzahlen` is the write-call-return body. -/
theorem refP_rumpf_ein : refP.rumpf refEin = refEin_start ▸ refRumpfEin := rfl

/-- `refP.rumpf` of `lies` is the slot return. -/
theorem refP_rumpf_lies : refP.rumpf refLies = refLies_start ▸ refRumpfLies := rfl

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
theorem refM1kopf : (refM1B.faeden 1).kopf.f = refEin := rfl

/-- Thread 1 entry environment is the call argument. -/
theorem refM1rho : (refM1B.faeden 1).kopf.rho = refRho7 := rfl

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
          (.ret .empty (by rfl))⟩⟩,
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
            (.ret .empty (by rfl)))⟩ := rfl

/-- Step B: thread 1 fires the write `konto[0] := 100`. Every `blatt`
    premise is a named `rfl` fact about the `assignSlot` equation. -/
theorem refSchrittB : RufSchrittD refP refO 0 refM1B 1 refM2B := by
  have hhead : (refM1B.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := refD) ()],
        .cons refWriteStAt
          (.cons (.call (V := vertragVon refD refEin) refLies refArgsLies
            refHpLiesAt rfl)
            (.ret .empty (by rfl)))⟩ := rfl
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
    simp at hm
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
