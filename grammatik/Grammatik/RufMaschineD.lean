/-
  File:      Grammatik/RufMaschineD.lean
  Subject:   THE CALL MACHINE (attempt D) -- threads with a FRAME STACK over
             shared memory, call entry and return events with the ACTUAL
             parameter environment, result, and entry world.

  Why: the PC machine (`PCAtom`: leaf/take/rel, Maschine.lean) executes
  footprints, never calls; leaves run with `keinRuf`. Contracts can therefore
  not be checked at their place in a concurrent run, and the goal theorem had
  to fall back to `QRequires`/`QEnsures` (proved degenerate, `QLeer.lean`).
  `VertragOrtB.lean` has the right contract shape (`ReqAmEintritt`,
  `EnsAmRueck` with the actual rho, v and the entry world s0) but its runs
  (`ContrLauf`) are free data. This file generates the runs: a thread state
  with a frame stack, a step relation through `execStmt` (so memory moves on
  writes by construction), call/return events recorded in a per-thread log,
  and reachability generated from a start state.

  Design notes:
  - Frames hold real `Endblock` residues of the callee contract
    (`vertragVon`), so leaf steps run through `execStmt` with `keinRuf`
    (leaves never consult the call handler). Compounds (`ite`, `locks`
    bodies, ...) have no unfold step: the machine is partial there, and the
    adequacy fragment covers only straight-line `ret` bodies (see CUTS).
  - `locks` take/release are standalone scheduler steps (`nimmt`/`gibt`)
    with the `GenSchritt` rule (take only while nobody else holds the lock).
    The machine never gates on contracts: `VertragAmOrtMaschineD` is a
    predicate ON generated runs, not a firing condition.
  - The `rueck` event carries the return world `s1` next to the entry world
    `s0`, so `EnsAmRueck` (which needs both) is stated per event.
-/
import Grammatik.Maschine
import Grammatik.VertragOrtB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Call and return events with the actual values -/

/-- Call/return events carrying the ACTUAL values: entry carries the actual
    parameter environment `rho` and the entry world `s0`; return carries the
    actual `rho`, the actual result `v`, the entry world `s0` (the `old(..)`
    side of `ensures`) and the return world `s1`. -/
inductive RufEreignisD (D : Deklaration) where
  | eintritt (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
  | rueck (f : D.Fn) (rho : Env D (D.params f))
      (v : ErgVal D (D.erg f)) (s0 s1 : World D)

/-! ## 2. Frames, threads, the machine -/

/-- One frame: the running function `f`, its actual parameter environment
    `rho`, its entry world `s0` (the `old(..)` side of `ensures`), and the
    remaining callee residue under the callee contract `vertragVon D f`.
    A `Sigma` packs the context and resource indices together with the
    residue block. -/
structure RufRahmenD (D : Deklaration) where
  f : D.Fn
  rho : Env D (D.params f)
  s0 : World D
  rest : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Endblock D (vertragVon D f) l Γ Λ

/-- A thread: a non-empty frame stack (the head is the running frame, the
    tail the suspended callers), its own event log, and the held-lock list
    witnessing `HeldGenau` at the running head. -/
structure RufFadenD (D : Deklaration) where
  stapel : List (RufRahmenD D)
  kopf : RufRahmenD D
  spur : List (Ereignis D)
  log : List (RufEreignisD D)

/-- The machine: shared memory, one thread state per thread id, the
    interleaved run so far, and the start world. -/
structure RufMaschineD (D : Deklaration) where
  speicher : Speicher D
  faeden : Faden → RufFadenD D
  lauf : Lauf D
  start : World D

/-- The current world of thread `f`: live shared memory plus its own trace. -/
def RufMaschineD.weltVon (M : RufMaschineD D) (f : Faden) : World D :=
  M.speicher.welt (M.faeden f).spur

/-- No thread other than `f` holds `L` right now -- the scheduler rule side. -/
def RufFreiD (M : RufMaschineD D) (f : Faden) (L : D.Lock) : Prop :=
  ∀ g, g ≠ f → L ∉ offen (M.faeden g).spur

/-- The new run events of one step, all attributed to the acting thread. -/
def rufEigenD (f : Faden) (neu : List (Ereignis D)) : Lauf D :=
  neu.reverse.map fun e => Schritt.mk f e

/-! ## 3. The step relation -/

/-- One thread state replaced, all others kept. -/
def rufUpdateD (m : Faden → RufFadenD D) (f : Faden) (z : RufFadenD D) :
    Faden → RufFadenD D :=
  fun g => if g = f then z else m g

theorem rufUpdateD_self (m : Faden → RufFadenD D) (f : Faden) (z : RufFadenD D) :
    rufUpdateD m f z f = z := by
  simp [rufUpdateD]

theorem rufUpdateD_noteq (m : Faden → RufFadenD D) (f g : Faden) (h : g ≠ f)
    (z : RufFadenD D) :
    rufUpdateD m f z g = m g := by
  simp [rufUpdateD, h]

/-- **One step of the call machine.** `blatt`: the running frame's head
    statement executes through `execStmt` with `keinRuf` (leaves never
    consult the call handler; shared memory moves on writes by construction
    of `execStmt`); the emitted events extend the acting thread's trace and
    the step appends its post-world's memory. `nimmt`/`gibt`: `f` takes or
    releases `L`; taking fires only while no other thread holds `L` (the lock
    as scheduler rule, as in `GenSchritt`). `ruf`: a call pushes the callee
    frame built from the callee body `P.rumpf f` with evaluated arguments and
    records `eintritt f rho s0` with the entry world. `rueck`: the callee
    residue is `ret`, whose value and post-world come from `execEnd`-free
    `ret` evaluation; the frame pops and the step records
    `rueck f rho v s0 s1` with entry world `s0` from the popped frame and
    return world `s1`. -/
inductive RufSchrittD (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineD D → Faden → RufMaschineD D → Prop where
  | blatt (M : RufMaschineD D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, .cons s rest⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
      RufSchrittD P O passes M f
        ⟨σ'.speicher,
         rufUpdateD M.faeden f
           ⟨(M.faeden f).stapel, (M.faeden f).kopf,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenD f neu, M.start⟩
  | nimmt (M : RufMaschineD D) (f : Faden) (L : D.Lock)
      (hself : L ∉ offen (M.faeden f).spur)
      (hrang : ∀ K ∈ offen (M.faeden f).spur, D.rang K < D.rang L)
      (hfrei : RufFreiD M f L) :
      RufSchrittD P O passes M f
        ⟨M.speicher,
         rufUpdateD M.faeden f
           ⟨(M.faeden f).stapel, (M.faeden f).kopf,
            Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
            (M.faeden f).log⟩,
         M.lauf ++ rufEigenD f [Ereignis.nimmt L (offen (M.faeden f).spur)],
         M.start⟩
  | gibt (M : RufMaschineD D) (f : Faden) (L : D.Lock)
      (hhaelt : L ∈ offen (M.faeden f).spur) :
      RufSchrittD P O passes M f
        ⟨M.speicher,
         rufUpdateD M.faeden f
           ⟨(M.faeden f).stapel, (M.faeden f).kopf,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenD f [Ereignis.gibt L], M.start⟩
  | ruf (M : RufMaschineD D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (g : D.Fn) (args : Args D Γ Λ (D.params g))
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, .cons (.call g args hp hr) rest⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittD P O passes M f
        ⟨M.speicher,
         rufUpdateD M.faeden f
           ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              P.rumpf g⟩⟩,
            s0.spur, (RufEreignisD.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenD f neu,
         M.start⟩
  | rueck (M : RufMaschineD D) (f : Faden)
      (caller : RufRahmenD D) (rest : List (RufRahmenD D))
      (hpop : (M.faeden f).stapel = caller :: rest)
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest = ⟨false, Γ, Λ, .ret e hperm⟩)
      (g : D.Fn) (hfg : (M.faeden f).kopf.f = g)
      (rho : Env D (D.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
      (s0 : World D) (hs0 : (M.faeden f).kopf.s0 = s0)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (s1 : World D)
      (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
      (v : ErgVal D (D.erg g))
      (hv : v = hfg ▸ evalErg s1 e s1 ρ)
      (neu : List (Ereignis D))
      (hneu : s1.spur = neu ++ (M.faeden f).spur) :
      RufSchrittD P O passes M f
        ⟨s1.speicher,
         rufUpdateD M.faeden f
           ⟨rest, caller, s1.spur,
            (RufEreignisD.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenD f neu,
         M.start⟩

/-! ## 4. Reachability and the entry/return matching invariant -/

/-- The start machine: shared memory, every thread in its entry frame with
    an empty trace and a single `eintritt` log entry recording the entry
    world. -/
def RufStartD (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    RufMaschineD D :=
  ⟨sp, fun f =>
    let ⟨g, rho⟩ := init f
    ⟨[], ⟨g, rho, sp.welt [],
      ⟨false, D.params g, Signatur.anfang D (D.signatur g), P.rumpf g⟩⟩,
     [], [RufEreignisD.eintritt g rho (sp.welt [])]⟩,
   [], sp.welt []⟩

/-- Reachable machines, generated from `M0` by the step relation. -/
inductive RufErreichbarD (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineD D) : RufMaschineD D → Prop where
  | start : RufErreichbarD P O passes M0 M0
  | schritt (M M' : RufMaschineD D) (f : Faden)
      (h : RufErreichbarD P O passes M0 M) (hs : RufSchrittD P O passes M f M') :
      RufErreichbarD P O passes M0 M'

/-! NEXT -/

end Gabbro.Grammatik
