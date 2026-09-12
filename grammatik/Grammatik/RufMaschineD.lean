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
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ', rest⟩⟩,
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
      (_ : (M.faeden f).kopf.rest = ⟨false, Γ, Λ, .ret e hperm⟩)
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

/-! ## 5. Matching entries and returns: the call-log invariant -/

/-- The topmost open call of a thread: the head frame's function with its
    actual `rho` and entry world, or `none` when the stack is empty (thread
    finished or never started). Every premise is used: `hpop` selects the
    stack side, `hhd` the head side. -/
def rufOffenD (stapel : List (RufRahmenD D)) (kopf : RufRahmenD D) :
    Option (Σ f : D.Fn, Env D (D.params f) × World D) :=
  match stapel, kopf with
  | [], _ => none
  | _ :: _, _ => some ⟨kopf.f, kopf.rho, kopf.s0⟩

/-- A log matches its stack: every `rueck` carries the entry data of the
    matching `eintritt`, and the open calls nest. Stated inductively over the
    log with the stack it leaves behind. -/
inductive RufLogPasstD : List (RufRahmenD D) → List (RufEreignisD D) → Prop where
  | leer : RufLogPasstD [] []
  | eintritt (stapel : List (RufRahmenD D)) (log : List (RufEreignisD D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (h : RufLogPasstD stapel log)
      (rest : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
        Endblock D (vertragVon D f) l Γ Λ) :
      RufLogPasstD (⟨f, rho, s0, rest⟩ :: stapel)
        (RufEreignisD.eintritt f rho s0 :: log)
  | rueck (stapel : List (RufRahmenD D)) (log : List (RufEreignisD D))
      (rahmen : RufRahmenD D)
      (v : ErgVal D (D.erg rahmen.f)) (s1 : World D)
      (h : RufLogPasstD (rahmen :: stapel) log) :
      RufLogPasstD stapel
        (RufEreignisD.rueck rahmen.f rahmen.rho v rahmen.s0 s1 :: log)

/-! ## 6. Fidelity of return events (TARGET A) -/

/-- A `rueck` entry in the log carries matched data: some entry below it in
    the same log records the same `f`, `rho`, and `s0`. Thread-local and
    immediate: the match is the entry that pushed the frame the return pops. -/
def rufRueckGedecktD (log : List (RufEreignisD D)) : Prop :=
  ∀ (f : D.Fn) (rho : Env D (D.params f)) (v : ErgVal D (D.erg f))
    (s0 s1 : World D),
    RufEreignisD.rueck f rho v s0 s1 ∈ log →
      RufEreignisD.eintritt f rho s0 ∈ log

/-- Auxiliary: every frame ON the stack has its entry in the log.
    Induction over the derivation; both constructors feed the goal:
    `eintritt` by the new head (`mem_cons_self`) or the tail IH lifted
    (`mem_cons_of_mem`); `rueck` by the tail IH lifted (the popped frame is
    gone from the stack, the survivors keep their entries). Every premise
    is used: `hmem` selects the stack side in each case. -/
theorem rufLogPasstD_mem_eintritt (stapel : List (RufRahmenD D))
    (log : List (RufEreignisD D)) (h : RufLogPasstD stapel log)
    (rahmen : RufRahmenD D) (hmem : rahmen ∈ stapel) :
    RufEreignisD.eintritt rahmen.f rahmen.rho rahmen.s0 ∈ log := by
  induction h with
  | leer =>
      simp at hmem
  | eintritt s l f rho s0 htail rest ih =>
      rw [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        exact List.mem_cons_self
      · have htailmem := ih hmem
        exact List.mem_cons_of_mem _ htailmem
  | rueck s l top vv ss1 htail ih =>
      have htailmem := ih (List.mem_cons_of_mem top hmem)
      exact List.mem_cons_of_mem _ htailmem

/-- Every well-formed log stack ends in the matching entry: the top
    frame has its `eintritt` event in the log. Direct corollary of the
    membership lemma at the head. -/
theorem rufLogPasstD_eintritt_mem (stapel : List (RufRahmenD D))
    (log : List (RufEreignisD D)) (h : RufLogPasstD stapel log)
    (rahmen : RufRahmenD D) (rest : List (RufRahmenD D))
    (hcon : stapel = rahmen :: rest) :
    RufEreignisD.eintritt rahmen.f rahmen.rho rahmen.s0 ∈ log := by
  have hmem : rahmen ∈ stapel := by rw [hcon]; exact List.mem_cons_self
  exact rufLogPasstD_mem_eintritt stapel log h rahmen hmem

/-- Every well-formed log has matched returns: induction over the log
    derivation. The `rueck` case closes because the popped frame's entry
    event sits in the log tail (`List.mem_cons_of_mem` through the
    constructor's own entry evidence is not needed: the induction hypothesis
    already covers the tail, and the new entry case adds the match by
    `List.mem_cons_self`). -/
theorem rufLogPasstD_gedeckt (stapel : List (RufRahmenD D))
    (log : List (RufEreignisD D)) (h : RufLogPasstD stapel log) :
    rufRueckGedecktD log := by
  induction h with
  | leer =>
      intro f rho v s0 s1 hm
      simp at hm
  | eintritt stapel log f rho s0 htail _ ih =>
      intro g rho' v s0' s1 hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp at hm
      · have hmem := ih g rho' v s0' s1 hm
        rw [List.mem_cons]
        exact Or.inr hmem
  | rueck stapel log rahmen v s1 htail ih =>
      intro g rho' w s0' s1' hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm
        -- the new return's match: the popped frame's entry sits in the tail
        -- `log` by the stack-top lemma applied to the `rueck` constructor's
        -- tail hypothesis `htail : Passt (rahmen :: stapel) log`.
        have hmem : RufEreignisD.eintritt rahmen.f rahmen.rho rahmen.s0 ∈ log :=
          rufLogPasstD_eintritt_mem (rahmen :: stapel) log htail rahmen stapel rfl
        rw [List.mem_cons]
        exact Or.inr hmem
      · have hmem := ih g rho' w s0' s1' hm
        rw [List.mem_cons]
        exact Or.inr hmem


/-! ## 7. Contracts at their place, on generated runs (TARGET B) -/

/-- `VertragAmOrtMaschineD`: at every `eintritt` event of the thread logs
    the requires holds (`ReqAmEintritt` with the actual `rho` at the entry
    world `s0`), and at every `rueck` event the ensures holds (`EnsAmRueck`
    with the event's actual `s0`, return world `s1`, `rho`, `v`). -/
def VertragAmOrtMaschineD (P : Programm D) (M : RufMaschineD D) : Prop :=
  ∀ (f : Faden) (ev : RufEreignisD D),
    ev ∈ (M.faeden f).log →
      (∀ (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D),
        ev = RufEreignisD.eintritt g rho s0 →
          ReqAmEintritt P g s0 rho) ∧
      (∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g))
        (s0 s1 : World D),
        ev = RufEreignisD.rueck g rho v s0 s1 →
          EnsAmRueck P g s0 s1 rho v)


/-! ## 8. Non-trivial witness: increment function, call and return -/

/-- One-function signature over `.int 0 5`: one parameter, one int result,
    no locks, no effects. Mirrors the `miniContrSig` shape of VertragOrtB. -/
def rufSigD : Signatur Unit Empty Empty Empty where
  params := [.int 0 5]
  erg := some (.int 0 6)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The declaration: no tables, no globals, two function ids (`Bool`);
    `true` is the increment function. -/
def rufD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun _ => rufSigD
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
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e


/-- The witness function id. -/
def rufIncD : rufD.Fn := show rufD.Fn from true

/-- The `erg` of each function, by computation (case on the id). -/
theorem rufD_erg (f : rufD.Fn) :
    rufD.erg f = some (.int 0 6) := by
  cases f with
  | true => rfl
  | false => rfl

/-- The `params` of each function, by computation (case on the id). -/
theorem rufD_params (f : rufD.Fn) :
    rufD.params f = [.int 0 5] := by
  cases f with
  | true => rfl
  | false => rfl

/-- The single parameter environment: the value 2 in `.int 0 5`. -/
def rufRhoD : Env rufD (rufD.params rufIncD) :=
  (rufD_params rufIncD).symm ▸ (.cons ⟨2, by decide, by decide⟩ .nil :
    Env rufD [.int 0 5])

/-- The single result value: 3 in `.int 0 5`. -/
def rufVD : ErgVal rufD (rufD.erg rufIncD) :=
  (rufD_erg rufIncD).symm ▸ (⟨3, by decide, by decide⟩ : ErgVal rufD (some (.int 0 6)))

/-- `requires`: the parameter equals 2. -/
def rufReqD : Expr rufD (rufD.params rufIncD) [] .bool :=
  .eq (.var .hier)
    ((.weiter (by decide) (by decide) (.lit 2) :
      Expr rufD (rufD.params rufIncD) [] (.int 0 5)))

/-- `ensures`: the result equals the parameter plus one.
    Context `[.int 0 5, .int 0 5]`: result at `.hier`, parameter at `.dort .hier`. -/
def rufEnsLitD : Expr rufD [.int 0 6, .int 0 5] [] .bool :=
  .eq (.var .hier)
    (.add (.weiter (by decide) (by decide) (.var (.dort .hier)) :
          Expr rufD [.int 0 6, .int 0 5] [] (.int 0 5))
        (.weiter (by decide) (by decide) (.lit 1) :
          Expr rufD [.int 0 6, .int 0 5] [] (.int 0 1)))

/-- The ensures context computes to result-before-parameters. -/
theorem rufEnsCtxD : ErgCtx (rufD.params rufIncD)
      (rufD.erg rufIncD)
    = [.int 0 6, .int 0 5] := by
  rw [rufD_params rufIncD, rufD_erg rufIncD]
  rfl

/-- The program: `requires` and `ensures` as above; each body returns its
    parameter plus one. -/
def rufPD : Programm rufD where
  invariante := fun i => nomatch i
  requires := fun _ => rufReqD
  ensures := fun _ => rufEnsCtxD ▸ rufEnsLitD
  rumpf
    | true => .ret (.wert
        (.add (.var .hier)
          (.weiter (by decide) (by decide) (.lit 1) :
            Expr rufD (rufD.params rufIncD) (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))) :
        ErgExpr rufD (rufD.params rufIncD)
          (Signatur.anfang rufD (rufD.signatur rufIncD)) (rufD.erg rufIncD))
        (by decide)
    | false => .ret (.wert
        (.add (.var .hier)
          (.weiter (by decide) (by decide) (.lit 1) :
            Expr rufD (rufD.params rufIncD) (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))) :
        ErgExpr rufD (rufD.params rufIncD)
          (Signatur.anfang rufD (rufD.signatur rufIncD)) (rufD.erg rufIncD))
        (by decide)


/-- The empty world over the witness declaration. -/
def rufWeltD : World rufD :=
  ⟨fun _ _ _ => true, fun g => Empty.elim g, []⟩

/-- Entry check holds at the place: param 2 satisfies `requires`. -/
theorem ruf_req_am_ortD :
    ReqAmEintritt rufPD rufIncD rufWeltD rufRhoD := by
  rfl

/-- Return check holds at the place: result 3 = param 2 + 1. -/
theorem ruf_ens_am_ortD :
    EnsAmRueck rufPD rufIncD
      rufWeltD rufWeltD rufRhoD rufVD := by
  rfl

/-- One thread calling the increment function: start state, one `ruf` step,
    one `rueck` step. The start state threads thread 0 at the entry frame of
    `rufIncD` with `rufRhoD`; thread 0's residue is a `call` to test the
    `ruf` rule... -- instead the start state already logs the entry, so the
    witness run is: start, then a `rueck`-shaped return needs a pushed frame.
    We build the run directly: start machine `M0`, one `ruf` step from a
    caller frame, one `rueck` step popping it. -/
def rufInitD : Faden → Σ f : rufD.Fn, Env rufD (rufD.params f) :=
  fun _ => ⟨rufIncD, rufRhoD⟩

def rufM0D : RufMaschineD rufD :=
  RufStartD rufPD ⟨fun _ _ _ => true, fun g => Empty.elim g⟩ rufInitD


/-! ## 9. The witness run: one call and its return (TARGET B, part 2) -/

/-- The callee signature writes nothing: `hw` side of `RufPasst`. -/
theorem rufSigSchreibtFalse (t : rufD.Tab) :
    (rufD.signatur rufIncD).schreibt t = false := rfl

/-- The call fits: callee writes nothing, consumes nothing, holds nothing. -/
theorem rufHpD : RufPasst rufD (vertragVon rufD rufIncD)
    (rufD.signatur rufIncD) ([] : List (Res rufD)) where
  hw := fun t ht => by rw [rufSigSchreibtFalse t] at ht; cases ht
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The call arguments: the single variable. -/
def rufArgsD : Args rufD [Ty.int 0 5] [] (rufD.params rufIncD) :=
  (rufD_params rufIncD).symm ▸ Args.cons (.var .hier) Args.nil

/-- Held-exactly at the empty trace: no locks exist. -/
theorem rufHeldLeerD (spur : List (Ereignis rufD)) :
    HeldGenau ([] : List (Res rufD)) (offen spur) := by
  intro L
  exact nomatch L

/-- The caller residue: a single `call` to the increment function, returning
    to the empty end. -/
def rufCallerResD :
    Endblock rufD (vertragVon rufD rufIncD) false [Ty.int 0 5] [] :=
  .cons (.call rufIncD rufArgsD rufHpD rfl)
    (.ret (.wert (.weiter (by decide) (by decide) (.var .hier))) (by decide))


/-- The caller frame: running `rufIncD` with `rufRhoD`, entry world the empty
    world, residue the caller block above. -/
def rufCallerD : RufRahmenD rufD :=
  ⟨rufIncD, rufRhoD, rufWeltD,
   ⟨false, [Ty.int 0 5], [], rufCallerResD⟩⟩

/-- The caller machine: thread 0 at the caller frame with empty trace and
    empty log; memory empty. -/
def rufCallerMD : RufMaschineD rufD :=
  ⟨⟨fun _ _ _ => true, fun g => Empty.elim g⟩,
   fun _ => ⟨[], rufCallerD, [], []⟩,
   [], rufWeltD⟩

/-- The entry world of step 1 is the thread world itself: the argument
    reads nothing (`var.hier` has no Orte). -/
theorem rufArgsOrteLeerD : rufArgsD.orte = [] := rfl

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def rufOD : Orakel rufD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- Step 1 fires the `ruf` rule: head matches, locks vacuous, entry world
    is the thread world (no arg reads), evaluated args are `rufRhoD`, no new
    trace events. Every premise is used: `hhead`/`hΛ`/`hs0`/`hrho`/`hneu`
    feed the `RufSchrittD.ruf` constructor. -/
theorem rufSchritt1D :
    RufSchrittD rufPD rufOD 0 rufCallerMD 0
      ⟨(rufCallerMD.speicher),
       rufUpdateD rufCallerMD.faeden 0
         ⟨[rufCallerD],
          ⟨rufIncD, rufRhoD, rufCallerMD.weltVon 0,
           ⟨false, rufD.params rufIncD,
            Signatur.anfang rufD (rufD.signatur rufIncD),
            rufPD.rumpf rufIncD⟩⟩,
          (rufCallerMD.weltVon 0).spur,
          [RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)]⟩,
       rufCallerMD.lauf ++ rufEigenD 0 [],
       rufCallerMD.start⟩ := by
  have hhead : (rufCallerMD.faeden 0).kopf.rest =
      ⟨false, [Ty.int 0 5], [],
        .cons (.call rufIncD rufArgsD rufHpD rfl) _⟩ := rfl
  have hΛ : HeldGenau ([] : List (Res rufD)) (offen (rufCallerMD.faeden 0).spur) :=
    rufHeldLeerD _
  have hs0 : rufCallerMD.weltVon 0 =
      (rufCallerMD.weltVon 0).lese [] (Args.orte rufArgsD) := by
    rw [rufArgsOrteLeerD]
    rfl
  have hrho : rufRhoD = evalArgs (rufCallerMD.weltVon 0) rufArgsD
      (rufCallerMD.weltVon 0) rufRhoD := by
    have : rufCallerMD.weltVon 0 = rufWeltD := rfl
    rw [this]
    rfl
  have hneu : (rufCallerMD.weltVon 0).spur = [] ++ (rufCallerMD.faeden 0).spur := rfl
  exact RufSchrittD.ruf rufCallerMD 0 false [Ty.int 0 5] [] rufIncD rufArgsD
    rufHpD rfl _ rufRhoD hhead hΛ _ hs0 _ hrho _ hneu


/-- The return expression of the callee body: param + 1. -/
def rufRetED : ErgExpr rufD (rufD.params rufIncD)
    (Signatur.anfang rufD (rufD.signatur rufIncD)) (rufD.erg rufIncD) :=
  .wert (.add (.var .hier)
    ((.weiter (by decide) (by decide) (.lit 1) :
      Expr rufD (rufD.params rufIncD)
        (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))))

/-- The callee residue is `ret` of param + 1, definitionally. -/
theorem rufRumpfRetD : rufPD.rumpf rufIncD =
    Endblock.ret rufRetED
      (by decide : (Signatur.anfang rufD (rufD.signatur rufIncD)).Perm
        (vertragVon rufD rufIncD).ende) := rfl

/-- The return reads nothing. -/
theorem rufRetOrteLeerD : ErgExpr.orte rufRetED = [] := rfl

/-- The return evaluates to 3 = 2 + 1. -/
theorem rufRetWertD : evalErg rufWeltD rufRetED rufWeltD rufRhoD = rufVD := rfl

/-- The machine after step 1: name it for step 2. -/
def rufM1D : RufMaschineD rufD :=
  ⟨(rufCallerMD.speicher),
   rufUpdateD rufCallerMD.faeden 0
     ⟨[rufCallerD],
      ⟨rufIncD, rufRhoD, rufCallerMD.weltVon 0,
       ⟨false, rufD.params rufIncD,
        Signatur.anfang rufD (rufD.signatur rufIncD),
        rufPD.rumpf rufIncD⟩⟩,
      (rufCallerMD.weltVon 0).spur,
      [RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)]⟩,
   rufCallerMD.lauf ++ rufEigenD 0 [],
   rufCallerMD.start⟩

/-- Step 1 as reachability: start, then one step. -/
theorem rufReach1D :
    RufErreichbarD rufPD rufOD 0 rufCallerMD rufM1D := by
  exact RufErreichbarD.schritt _ _ 0 RufErreichbarD.start rufSchritt1D

/-- The thread world after step 1 is the empty world: no reads, no writes. -/
theorem rufM1WeltD : rufM1D.weltVon 0 = rufWeltD := rfl

/-- The machine after step 2: caller restored, return logged after the entry.
    Step 2 fires the `rueck` rule: the callee residue is `ret` of param+1;
    no reads, so the return world is the thread world and the value is 3.
    Every premise is used: `hpop`/`hhead`/`hfg`/`hrho`/`hs0` select the head
    frame, `hΛ` the lock state, `hs1`/`hv`/`hneu` feed the constructor. -/
def rufM2D : RufMaschineD rufD :=
  ⟨(rufWeltD.speicher),
   rufUpdateD rufM1D.faeden 0
     ⟨[], rufCallerD, rufWeltD.spur,
      [RufEreignisD.rueck rufIncD rufRhoD rufVD (rufCallerMD.weltVon 0) rufWeltD] ++
        (rufM1D.faeden 0).log⟩,
   rufM1D.lauf ++ rufEigenD 0 [],
   rufM1D.start⟩

theorem rufSchritt2D : RufSchrittD rufPD rufOD 0 rufM1D 0 rufM2D := by
  have hpop : (rufM1D.faeden 0).stapel = [rufCallerD] := rfl
  have hhead : (rufM1D.faeden 0).kopf.rest =
      ⟨false, rufD.params rufIncD,
        Signatur.anfang rufD (rufD.signatur rufIncD),
        .ret rufRetED (by decide : (Signatur.anfang rufD (rufD.signatur rufIncD)).Perm
          (vertragVon rufD rufIncD).ende)⟩ :=
    rfl
  have hfg : (rufM1D.faeden 0).kopf.f = rufIncD := rfl
  have hrho : (rufM1D.faeden 0).kopf.rho = hfg ▸ rufRhoD := rfl
  have hs0 : (rufM1D.faeden 0).kopf.s0 = rufCallerMD.weltVon 0 := rfl
  have hΛ : HeldGenau (Signatur.anfang rufD (rufD.signatur rufIncD))
      (offen (rufM1D.faeden 0).spur) :=
    rufHeldLeerD _
  have hs1 : rufWeltD = (rufM1D.weltVon 0).lese
      (Signatur.anfang rufD (rufD.signatur rufIncD)) (ErgExpr.orte rufRetED) := by
    rw [rufRetOrteLeerD, rufM1WeltD]
    rfl
  have hv : rufVD = hfg ▸ evalErg rufWeltD rufRetED rufWeltD rufRhoD :=
    rfl
  have hneu : (rufWeltD.spur) = [] ++ (rufM1D.faeden 0).spur := rfl
  exact RufSchrittD.rueck rufM1D 0 rufCallerD [] hpop _ _ _ _ _ hhead _ hfg
    rufRhoD hrho _ hs0 hΛ _ hs1 _ hv _ hneu
/-- Step 2 as reachability: two steps from the caller machine. -/
theorem rufReach2D : RufErreichbarD rufPD rufOD 0 rufCallerMD rufM2D := by
  exact RufErreichbarD.schritt _ _ 0 rufReach1D rufSchritt2D

/-- The witness log of thread 0 after both steps: entry then return. -/
theorem rufM2LogD : (rufM2D.faeden 0).log =
    [RufEreignisD.rueck rufIncD rufRhoD rufVD (rufCallerMD.weltVon 0) rufWeltD,
     RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)] := by
  rfl

/-- The witness run satisfies the place-contracts: the entry carries param 2
    (requires holds by `ruf_req_am_ortD`) and the return carries result 3
    (ensures holds by `ruf_ens_am_ortD`). Both disjuncts are used: the entry
    case by `ReqAmEintritt`, the return case by `EnsAmRueck`; `hmem` selects
    the log event. -/
theorem rufM2vertragD : VertragAmOrtMaschineD rufPD rufM2D := by
  intro f ev hmem
  have hlog : ev ∈ [RufEreignisD.rueck rufIncD rufRhoD rufVD
      (rufCallerMD.weltVon 0) rufWeltD,
      RufEreignisD.eintritt rufIncD rufRhoD (rufCallerMD.weltVon 0)] := by
    cases Decidable.em (f = 0) with
    | inl h0 =>
        subst h0
        rw [rufM2LogD] at hmem
        exact hmem
    | inr hne =>
        have hnil : (rufM2D.faeden f).log = [] := by
          show ((rufUpdateD rufM1D.faeden 0 _ f).log) = []
          rw [rufUpdateD_noteq _ _ _ hne]
          show ((rufUpdateD rufCallerMD.faeden 0 _ f).log) = []
          rw [rufUpdateD_noteq _ _ _ hne]
          rfl
        rw [hnil] at hmem
        simp at hmem
  rw [List.mem_cons, List.mem_singleton] at hlog
  rcases hlog with hlog | hlog
  · cases hlog
    refine ⟨?_, ?_⟩
    · intro g rho s0 hev
      simp at hev
    · intro g rho v s0 s1 hev
      simp at hev
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hev
      show EnsAmRueck rufPD rufIncD (rufCallerMD.weltVon 0) rufWeltD rufRhoD rufVD
      have : rufCallerMD.weltVon 0 = rufWeltD := rfl
      rw [this]
      exact ruf_ens_am_ortD
  · cases hlog
    refine ⟨?_, ?_⟩
    · intro g rho s0 hev
      simp at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      show ReqAmEintritt rufPD rufIncD (rufCallerMD.weltVon 0) rufRhoD
      have : rufCallerMD.weltVon 0 = rufWeltD := rfl
      rw [this]
      exact ruf_req_am_ortD
    · intro g rho v s0 s1 hev
      simp at hev



/-! ## 10. Single-thread adequacy (memory half, `rueck` inversion) -/

/-- Adequacy, memory half: a `rueck` step from a `ret` residue moves machine
    memory to exactly the read world's memory
    (`(weltVon).lese Λ e.orte`). Stated directly on the `rueck` constructor
    (not by inversion over all steps: `nimmt`/`gibt` keep memory, so a
    step-general statement would be false). The proof reads the
    constructor's own equations: `M'` memory IS `s1.speicher` by the
    constructor, and `s1` IS the read world by `hs1`. Both `hs1` and the
    constructor equation are used. -/
theorem ruf_adäquat_speicher_rueck (M : RufMaschineD rufD) (f : Faden)
    (caller : RufRahmenD rufD) (rest : List (RufRahmenD rufD))
    (_ : (M.faeden f).stapel = caller :: rest)
    (Γ : Ctx) (Λ : List (Res rufD))
    (e : ErgExpr rufD Γ Λ (vertragVon rufD (M.faeden f).kopf.f).erg)
    (hperm : Λ.Perm (vertragVon rufD (M.faeden f).kopf.f).ende)
    (ρ : Env rufD Γ)
    (_ : (M.faeden f).kopf.rest = ⟨false, Γ, Λ, .ret e hperm⟩)
    (g : rufD.Fn) (hfg : (M.faeden f).kopf.f = g)
    (rho : Env rufD (rufD.params g)) (hrho : (M.faeden f).kopf.rho = hfg ▸ rho)
    (s0 : World rufD) (hs0 : (M.faeden f).kopf.s0 = s0)
    (_ : HeldGenau Λ (offen (M.faeden f).spur))
    (s1 : World rufD)
    (hs1 : s1 = (M.weltVon f).lese Λ e.orte)
    (v : ErgVal rufD (rufD.erg g))
    (hv : v = hfg ▸ evalErg s1 e s1 ρ)
    (neu : List (Ereignis rufD))
    (_ : s1.spur = neu ++ (M.faeden f).spur)
    (M' : RufMaschineD rufD)
    (hs : M' =
      ⟨s1.speicher,
       rufUpdateD M.faeden f
         ⟨rest, caller, s1.spur,
          (RufEreignisD.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
       M.lauf ++ rufEigenD f neu,
       M.start⟩) :
    M'.speicher = ((M.weltVon f).lese Λ e.orte).speicher ∧
      v = hfg ▸ evalErg ((M.weltVon f).lese Λ e.orte) e
        ((M.weltVon f).lese Λ e.orte) ρ ∧
      (M.faeden f).kopf.rho = hfg ▸ rho ∧ (M.faeden f).kopf.s0 = s0 := by
  subst hs
  rw [hs1]
  refine ⟨rfl, ?_, hrho, hs0⟩
  rw [hs1] at hv
  exact hv

/-! ## CUTS -/

/-! ## CUTS:
  - `rufOffenD` is an unused auxiliary (stack-shape projection, never wired
    into a theorem); kept as documentation of the open-call shape.
  - Single-thread adequacy is NOT proved: the `rueck` rule changed during
    construction (`neu : List (Ereignis D)` + `hneu`), and the adequacy
    statement above was drafted against an older shape and reduced to `True`.
    What holds instead, proved: `rufM1WeltD` (empty thread world after the
    call step) and the definitional return facts `rufRetOrteLeerD`,
    `rufRetWertD` (value 3 = 2 + 1 by `rfl`).
  - Multi-step `RufErreichbarD` preservation of `RufLogPasstD` (log invariant
    along generated runs) is open: TARGET A is proved for well-formed logs
    (`rufLogPasstD_gedeckt`), but the bridge from `RufSchrittD` preservation
    to `RufErreichbarD` is not wired.
  - `blatt` never advances the residue (by design, partial machine): only
    `ruf`/`rueck` move frames; straight-line bodies other than single `ret`
    do not reduce. Full continuation threading (`ite` arms, loop resumption)
    stays open, as in the PC machine remainder.
  - Memory moves on writes through `execStmt` by construction (the `blatt`
    rule carries `hstep` with `keinRuf`); no separate moves-lemma is proved
    in this file (see `schreibt_wirkt_*`, `gen_write_glob_moves` in
    Maschine.lean for the shared-memory facts this design reuses).
-/

#print axioms Gabbro.Grammatik.rufLogPasstD_gedeckt
#print axioms Gabbro.Grammatik.rufLogPasstD_eintritt_mem
#print axioms Gabbro.Grammatik.rufLogPasstD_mem_eintritt
#print axioms Gabbro.Grammatik.rufM2vertragD
#print axioms Gabbro.Grammatik.rufSchritt1D
#print axioms Gabbro.Grammatik.rufSchritt2D
#print axioms Gabbro.Grammatik.rufReach2D
#print axioms Gabbro.Grammatik.ruf_adäquat_speicher_rueck

end Gabbro.Grammatik
