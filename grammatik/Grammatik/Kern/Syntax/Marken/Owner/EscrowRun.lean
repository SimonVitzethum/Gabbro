module

public import Grammatik.Kern.Syntax.Marken.Owner.EscrowFixture
public import Grammatik.Kern.Syntax.Marken.Owner.Activation
public import Grammatik.Kern.Syntax.Marken.Owner.InvocationFlow
public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm
public import Grammatik.Kern.Semantik.Semantik.T1.Teil1
public import Grammatik.Kern.Semantik.Semantik.T2.Teil1
public import Grammatik.Kern.Semantik.Maschine.T1.Teil1
public import Grammatik.Kern.Semantik.Semantik.T1.Teil2
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T2
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3

@[expose] public section

namespace Gabbro.Grammatik.EscrowWitness

/-! ## The witness run: one push, one return, over the shared fixture

    The caller (`false`) calls the callee (`true`) with the loaned owner in
    hand; the callee returns at once. `schrittPushE` fires the `ruf` rule,
    `schrittPopE` the `rueck` rule; `pushE`/`popE` bind them to the same
    canonical `OwnerInvocation`, so the dynamic escrow lemmas of
    `Owner/Escrow.lean` instantiate on this run. -/

/-- The held set at the call: exactly the loaned owner. -/
def anfE : List (Res escrowD) :=
  Signatur.anfang escrowD (escrowD.signatur false)

theorem anfE_eq : anfE = [Res.marke true 0] := rfl

/-- The call fits: same rights, the owner input in hand, escrow-ready flow. -/
theorem hpE : RufPasst escrowD (vertragVon escrowD false) (escrowD.signatur true) anfE where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨_, List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun L => nomatch L
  ownerReady := escrowReadyE

theorem hrE : escrowD.gruende true = 0 := rfl

/-- The call arguments: none (the handoff is resource-only). -/
def argsE : Args escrowD [] anfE (escrowD.params true) := .nil

/-- The callee answer: no value (the return carries only the owner). -/
def retE : ErgExpr escrowD (escrowD.params true) anfE none := .empty

theorem calleePermE : anfE.Perm (vertragVon escrowD true).ende :=
  List.Perm.refl _

/-- The callee body: return at once, holding exactly the loaned owner. -/
def calleeBodyE : Endblock escrowD (vertragVon escrowD true) false
    (escrowD.params true) anfE :=
  .ret retE calleePermE

/-- The caller residue after the call: the same return. -/
def restE : Endblock escrowD (vertragVon escrowD false) false
    (escrowD.params false) (nach escrowD true anfE) :=
  .ret .empty (List.Perm.refl _)

/-- The caller body: a single call to the callee, then return. -/
def callerBodyE : Endblock escrowD (vertragVon escrowD false) false
    (escrowD.params false) anfE :=
  .cons (.call true argsE hpE hrE) restE

/-- The program: the caller calls, the callee returns. -/
def progE : Programm escrowD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => calleeBodyE
    | false => callerBodyE

theorem progE_rumpf_true : progE.rumpf true = calleeBodyE := rfl

theorem progE_rumpf_false : progE.rumpf false = callerBodyE := rfl

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def orakelE : Orakel escrowD where
  wirkt := fun _ σ _ => (σ, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- Start memory: slot 0 holds 0 (the run moves no memory). -/
def spE : Speicher escrowD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

def rhoE : Env escrowD [] := .nil

def rhoCallerE : Env escrowD (escrowD.params false) :=
  (escrowParams false).symm ▸ rhoE

def initE : Faden → Σ f : escrowD.Fn, Env escrowD (escrowD.params f) :=
  fun _ => ⟨false, rhoCallerE⟩

def M0E : RufMaschineG escrowD := RufStartG progE spE initE

/-- The start head is the caller body with the entry environment. -/
theorem M0E_kopf :
    (M0E.faeden 0).kopf.rest =
    ⟨false, escrowD.params false, anfE, rhoCallerE, .ende (progE.rumpf false)⟩ := by
  have hstart : (RufStartG (D := escrowD) progE spE initE).faeden 0 =
      (match initE 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spE.welt [],
          ⟨false, escrowD.params g', Signatur.anfang escrowD (escrowD.signatur g'),
           rho', .ende (progE.rumpf g')⟩⟩ : RufRahmenG escrowD),
        [], [RufEreignisF.eintritt g' rho' (spE.welt [])]⟩ :
          RufFadenG escrowD)) := rfl
  have hif : initE 0 = (⟨false, rhoCallerE⟩ :
      Σ f : escrowD.Fn, Env escrowD (escrowD.params f)) := by
    simp only [initE]
  have hM : M0E.faeden 0 =
      (⟨[], (⟨false, rhoCallerE, spE.welt [],
        ⟨false, escrowD.params false, anfE,
         rhoCallerE, .ende (progE.rumpf false)⟩⟩ : RufRahmenG escrowD),
       [], [RufEreignisF.eintritt false rhoCallerE (spE.welt [])]⟩ :
        RufFadenG escrowD) := by
    simp only [M0E]
    rw [hstart, hif]
    rfl
  have hrumpf : progE.rumpf false = callerBodyE := rfl
  rw [hM, hrumpf]

/-- The suspended caller frame: residue advanced past the call. -/
def callerFrameE : RufRahmenG escrowD :=
  ⟨false, rhoCallerE, spE.welt [],
   ⟨false, escrowD.params false, nach escrowD true anfE, rhoCallerE, .ende restE⟩⟩

/-- The callee entry world: the caller thread world read at no places. -/
def s0E : World escrowD := (M0E.weltVon 0).lese anfE argsE.orte

/-- The machine after the `ruf` step: caller suspended, callee installed. -/
def M1E : RufMaschineG escrowD :=
  ⟨M0E.speicher,
   rufUpdateG M0E.faeden 0
     ⟨callerFrameE :: (M0E.faeden 0).stapel,
      ⟨true, rhoE, s0E,
       ⟨false, escrowD.params true, anfE, rhoE, .ende (progE.rumpf true)⟩⟩,
      s0E.spur,
      (RufEreignisF.eintritt true rhoE s0E) ::
        (M0E.faeden 0).log⟩,
   M0E.lauf ++ rufEigenG 0 [],
   M0E.start⟩

/-- Step 1 fires the `ruf` rule on the caller frame. -/
theorem schrittPushE : RufSchrittG progE orakelE 0 M0E 0 M1E := by
  have hhead : (M0E.faeden 0).kopf.rest =
      ⟨false, escrowD.params false, anfE, rhoCallerE,
       .ende (.cons (.call true argsE hpE hrE) restE)⟩ := by
    rw [M0E_kopf, progE_rumpf_false]
    rfl
  have hΛ : HeldIn anfE (offen (M0E.faeden 0).spur) := fun L => nomatch L
  have hs0 : s0E = (M0E.weltVon 0).lese anfE argsE.orte := rfl
  have hrho : rhoE = evalArgs s0E argsE s0E rhoCallerE := rfl
  have hneu : s0E.spur = [] ++ (M0E.faeden 0).spur := rfl
  exact RufSchrittG.ruf M0E 0 false (escrowD.params false) anfE true
    argsE hpE rfl _ rhoCallerE hhead hΛ _ hs0 _ hrho _ hneu

/-- The callee head after the call is the immediate return. -/
theorem M1E_kopf :
    (M1E.faeden 0).kopf.rest =
    ⟨false, escrowD.params true, anfE, rhoE, .ende (progE.rumpf true)⟩ := by
  rfl

/-- The return world: the callee thread world read at no result places. -/
def s1E : World escrowD := (M1E.weltVon 0).lese anfE retE.orte

def vE : ErgVal escrowD (escrowD.erg true) := ()

/-- The machine after the `rueck` step: caller restored, return logged. -/
def M2E : RufMaschineG escrowD :=
  ⟨s1E.speicher,
   rufUpdateG M1E.faeden 0
     ⟨[], callerFrameE, s1E.spur,
      [RufEreignisF.rueck true rhoE vE s0E s1E] ++
        (M1E.faeden 0).log⟩,
   M1E.lauf ++ rufEigenG 0 [],
   M1E.start⟩

/-- Step 2 fires `rueck`: the callee frame pops to the waiting caller. -/
theorem schrittPopE : RufSchrittG progE orakelE 0 M1E 0 M2E := by
  have hpop : (M1E.faeden 0).stapel = [callerFrameE] := rfl
  have hhead : (M1E.faeden 0).kopf.rest =
      ⟨false, escrowD.params true, anfE, rhoE, .ende (.ret retE calleePermE)⟩ := by
    rw [M1E_kopf, progE_rumpf_true]
    rfl
  have hfg : (M1E.faeden 0).kopf.f = true := rfl
  have hrho : (M1E.faeden 0).kopf.rho = hfg ▸ rhoE := rfl
  have hs0 : (M1E.faeden 0).kopf.s0 = s0E := rfl
  have hΛ : HeldIn anfE (offen (M1E.faeden 0).spur) := fun L => nomatch L
  have hs1 : s1E = (M1E.weltVon 0).lese anfE retE.orte := rfl
  have hv : vE = hfg ▸ evalErg s1E retE s1E rhoE := rfl
  have hneu : s1E.spur = [] ++ (M1E.faeden 0).spur := rfl
  exact RufSchrittG.rueck M1E 0 callerFrameE [] hpop _ _ _ _ _ hhead _ hfg
    rhoE hrho _ hs0 hΛ _ hs1 _ hv _ hneu rfl

/-- The one canonical invocation: `true` entered from the start frame. -/
def invocE : OwnerInvocation escrowD where
  thread := 0
  before := (M0E.faeden 0).log
  callee := true
  arguments := rhoE
  entry := M0E.weltVon 0
  parent := 0
  ancestors := []
  active := rfl

theorem invocCallerE : invocE.caller = callerF := rfl

theorem invocFrameE : invocE.frame = calleeF := rfl

theorem pushE : invocE.Push progE orakelE 0 M0E M1E where
  step := schrittPushE
  beforeLog := rfl
  afterLog := rfl
  key := rfl
  stack := rfl

def popE : invocE.Return progE orakelE 0 M1E M2E where
  step := schrittPopE
  nested := []
  event := .rueck true rhoE vE s0E s1E
  beforeLog := rfl
  active := rfl
  outcome := Or.inl ⟨vE, s1E, rfl⟩
  afterLog := rfl
  stack := rfl

end Gabbro.Grammatik.EscrowWitness
