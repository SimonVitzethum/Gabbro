/-
  File:      Grammatik/RufMaschineF.lean
  Subject:   THE CALL MACHINE WITH LOCAL ENVIRONMENTS (attempt F) -- threads
             with a FRAME STACK over shared memory, where each frame carries
             the environment of its CURRENT context next to its residue.

  Why: `RufMaschineD.lean` (see its REVIEWER NOTE) threads every step through
  a FREE `rho : Env D Gamma`: a step may run under ANY values of the locals,
  so the machine over-approximates the program. Here each frame carries
  `Gamma` with `rho : Env D Gamma` next to the residue
  `Endblock D (vertragVon D f) l Gamma Lambda`: `blatt` runs `execStmt` with
  the STORED `rho` and stores the resulting `rho'` (the `.ok` outcome);
  `ruf` evaluates the arguments in the caller's stored `rho`; `rueck`
  evaluates the result in the callee's stored `rho`. No step constructor
  keeps a free `rho` binder. The stack/log invariant compares frames only by
  (function, parameter environment, entry world) -- never by residue -- and
  its preservation along `RufSchrittF` is proved, lifting return fidelity
  (`rufF_treu`) to every reachable machine by induction.
-/
import Grammatik.Maschine
import Grammatik.VertragOrtB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Call and return events with the actual values -/

/-- Call/return events carrying the ACTUAL values: entry carries the actual
    parameter environment `rho` and the entry world `s0`; return carries the
    actual `rho`, the actual result `v`, the entry world `s0` (the `old(..)`
    side of `ensures`) and the return world `s1`. `grund` is a return
    through the error channel (a callee answering a reason `r`); the F
    machine never logs it, the G machine logs it when a `retGrund` pops
    into a caller waiting in a `let x = g(…) else { … }`. -/
inductive RufEreignisF (D : Deklaration) where
  | eintritt (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
  | rueck (f : D.Fn) (rho : Env D (D.params f))
      (v : ErgVal D (D.erg f)) (s0 s1 : World D)
  | grund (f : D.Fn) (rho : Env D (D.params f))
      (r : Fin (D.gruende f)) (s0 s1 : World D)

/-! ## 2. Frames, threads, the machine -/

/-- One frame: the running function `f`, its actual parameter environment
    `rho`, its entry world `s0` (the `old(..)` side of `ensures`), and the
    remaining callee residue under the callee contract `vertragVon D f` with
    the environment of its CURRENT context `rho` next to it. The `Sigma`
    packs the context and resource indices together with the residue block;
    the pair packs the current environment next to that block. -/
structure RufRahmenF (D : Deklaration) where
  f : D.Fn
  rho : Env D (D.params f)
  s0 : World D
  rest :
    Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
      Env D Γ × Endblock D (vertragVon D f) l Γ Λ

/-- A thread: a frame stack of suspended callers (below) with the running
    frame `kopf` on top, its own event trace, its own call/return log. -/
structure RufFadenF (D : Deklaration) where
  stapel : List (RufRahmenF D)
  kopf : RufRahmenF D
  spur : List (Ereignis D)
  log : List (RufEreignisF D)

/-- The machine: shared memory, one thread state per thread id, the
    interleaved run so far, and the start world. -/
structure RufMaschineF (D : Deklaration) where
  speicher : Speicher D
  faeden : Faden → RufFadenF D
  lauf : Lauf D
  start : World D

/-- The current world of thread `f`: live shared memory plus its own trace. -/
def RufMaschineF.weltVon (M : RufMaschineF D) (f : Faden) : World D :=
  M.speicher.welt (M.faeden f).spur

/-- No thread other than `f` holds `L` right now -- the scheduler rule side. -/
def RufFreiF (M : RufMaschineF D) (f : Faden) (L : D.Lock) : Prop :=
  ∀ g, g ≠ f → L ∉ offen (M.faeden g).spur

/-- The new run events of one step, all attributed to the acting thread. -/
def rufEigenF (f : Faden) (neu : List (Ereignis D)) : Lauf D :=
  neu.reverse.map fun e => Schritt.mk f e

/-- One thread state replaced, all others kept. -/
def rufUpdateF (m : Faden → RufFadenF D) (f : Faden) (z : RufFadenF D) :
    Faden → RufFadenF D :=
  fun g => if g = f then z else m g

theorem rufUpdateF_self (m : Faden → RufFadenF D) (f : Faden) (z : RufFadenF D) :
    rufUpdateF m f z f = z := by
  simp [rufUpdateF]

theorem rufUpdateF_noteq (m : Faden → RufFadenF D) (f g : Faden) (h : g ≠ f)
    (z : RufFadenF D) :
    rufUpdateF m f z g = m g := by
  simp [rufUpdateF, h]

/-- **One step of the call machine with local environments.**
    `blatt`: the running frame's head statement executes through `execStmt`
    with `keinRuf` (leaves never consult the call handler) under the STORED
    `rho`; the outcome must be `.ok sigma' rho'` -- the step stores BOTH.
    `nimmt`/`gibt`: take or release a lock (take only while nobody else
    holds it). `ruf`: a call pushes the callee frame built from the callee
    body `P.rumpf g` with arguments evaluated in the CALLER's stored `rho`,
    and records `eintritt g rho s0` with the entry world. `rueck`: the
    callee residue is `ret`, whose value and post-world come from `execEnd`
    run under the CALLEE's stored `rho`; the frame pops and the step records
    `rueck g rho v s0 s1` with entry world `s0` from the popped frame and
    return world `s1`. No constructor binds a free environment. -/
inductive RufSchrittF (P : Programm D) (O : Orakel D) (passes : Nat) :
    RufMaschineF D → Faden → RufMaschineF D → Prop where
  | blatt (M : RufMaschineF D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
      (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hhead : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .cons s rest⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ) =
        Ausgang.ok (D := D) (V := vertragVon D (M.faeden f).kopf.f) σ' ρ')
      (hneu : σ'.spur = neu ++ (M.faeden f).spur)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
      RufSchrittF P O passes M f
        ⟨σ'.speicher,
         rufUpdateF M.faeden f
           ⟨(M.faeden f).stapel,
            ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
             ⟨l, Γ, Λ', ρ', rest⟩⟩,
            σ'.spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenF f neu, M.start⟩
  | nimmt (M : RufMaschineF D) (f : Faden) (L : D.Lock)
      (hself : L ∉ offen (M.faeden f).spur)
      (hrang : ∀ K ∈ offen (M.faeden f).spur, D.rang K < D.rang L)
      (hfrei : RufFreiF M f L) :
      RufSchrittF P O passes M f
        ⟨M.speicher,
         rufUpdateF M.faeden f
           ⟨(M.faeden f).stapel, (M.faeden f).kopf,
            Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
            (M.faeden f).log⟩,
         M.lauf ++ rufEigenF f [Ereignis.nimmt L (offen (M.faeden f).spur)],
         M.start⟩
  | gibt (M : RufMaschineF D) (f : Faden) (L : D.Lock)
      (hhaelt : L ∈ offen (M.faeden f).spur) :
      RufSchrittF P O passes M f
        ⟨M.speicher,
         rufUpdateF M.faeden f
           ⟨(M.faeden f).stapel, (M.faeden f).kopf,
            Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
         M.lauf ++ rufEigenF f [Ereignis.gibt L], M.start⟩
  | ruf (M : RufMaschineF D) (f : Faden)
      (l : Bool) (Γ : Ctx) (Λ : List (Res D))
      (g : D.Fn) (args : Args D Γ Λ (D.params g))
      (hp : RufPasst D (vertragVon D (M.faeden f).kopf.f) (D.signatur g) Λ)
      (hr : D.gruende g = 0)
      (rest : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ (nach D g Λ))
      (ρ : Env D Γ)
      (hhead : (M.faeden f).kopf.rest =
        ⟨l, Γ, Λ, ρ, .cons (.call g args hp hr) rest⟩)
      (hΛ : HeldGenau Λ (offen (M.faeden f).spur))
      (s0 : World D)
      (hs0 : s0 = (M.weltVon f).lese Λ args.orte)
      (rho : Env D (D.params g))
      (hrho : rho = evalArgs s0 args s0 ρ)
      (neu : List (Ereignis D))
      (hneu : s0.spur = neu ++ (M.faeden f).spur) :
      RufSchrittF P O passes M f
        ⟨M.speicher,
         rufUpdateF M.faeden f
           ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
            ⟨g, rho, s0,
             ⟨false, D.params g, Signatur.anfang D (D.signatur g),
              rho, P.rumpf g⟩⟩,
            s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenF f neu,
         M.start⟩
  | rueck (M : RufMaschineF D) (f : Faden)
      (caller : RufRahmenF D) (rest : List (RufRahmenF D))
      (hpop : (M.faeden f).stapel = caller :: rest)
      (Γ : Ctx) (Λ : List (Res D))
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden f).kopf.f).erg)
      (hperm : Λ.Perm (vertragVon D (M.faeden f).kopf.f).ende)
      (ρ : Env D Γ)
      (_ : (M.faeden f).kopf.rest = ⟨false, Γ, Λ, ρ, .ret e hperm⟩)
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
      RufSchrittF P O passes M f
        ⟨s1.speicher,
         rufUpdateF M.faeden f
           ⟨rest, caller, s1.spur,
            (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
         M.lauf ++ rufEigenF f neu,
         M.start⟩

/-! ## 4. Reachability -/

/-- The start machine: shared memory, every thread in its entry frame (with
    its entry environment `rho` as BOTH the parameter context environment
    and the residue environment) and a single `eintritt` log entry recording
    the entry world. -/
def RufStartF (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    RufMaschineF D :=
  ⟨sp, fun f =>
    let ⟨g, rho⟩ := init f
    ⟨[], ⟨g, rho, sp.welt [],
      ⟨false, D.params g, Signatur.anfang D (D.signatur g),
       rho, P.rumpf g⟩⟩,
     [], [RufEreignisF.eintritt g rho (sp.welt [])]⟩,
   [], sp.welt []⟩

/-- Reachable machines, generated from `M0` by the step relation. -/
inductive RufErreichbarF (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineF D) : RufMaschineF D → Prop where
  | start : RufErreichbarF P O passes M0 M0
  | schritt (M M' : RufMaschineF D) (f : Faden)
      (h : RufErreichbarF P O passes M0 M) (hs : RufSchrittF P O passes M f M') :
      RufErreichbarF P O passes M0 M'

/-! ## 5. Matching entries and returns: the call-log invariant -/

/-- The key of a frame: its function with its ACTUAL parameter environment
    and its entry world. Residue and local context are NOT part of the key:
    `blatt` advances the residue (and the stored local environment), so an
    invariant comparing whole frames cannot be preserved. -/
def RufSchluesselF (r : RufRahmenF D) :
    Σ f : D.Fn, Env D (D.params f) × World D :=
  ⟨r.f, r.rho, r.s0⟩

/-- The key stack of a thread: head frame first (newest call first, matching
    the newest-first log). -/
def RufFadenSchluesselF (z : RufFadenF D) :
    List (Σ f : D.Fn, Env D (D.params f) × World D) :=
  (z.kopf :: z.stapel).map RufSchluesselF

/-- A log matches its key stack: every `rueck` carries the entry data of the
    matching `eintritt`, and the open calls nest. Stated inductively over the
    log with the key stack it leaves behind. The `rueck` case pops the HEAD
    key -- the frame the return pops -- and records its data in the event. -/
inductive RufLogPasstF :
    List (Σ f : D.Fn, Env D (D.params f) × World D) →
    List (RufEreignisF D) → Prop where
  | leer : RufLogPasstF [] []
  | eintritt (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
      (log : List (RufEreignisF D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (h : RufLogPasstF ks log) :
      RufLogPasstF (⟨f, rho, s0⟩ :: ks)
        (RufEreignisF.eintritt f rho s0 :: log)
  | rueck (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
      (log : List (RufEreignisF D))
      (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
      (v : ErgVal D (D.erg f)) (s1 : World D)
      (h : RufLogPasstF (⟨f, rho, s0⟩ :: ks) log) :
      RufLogPasstF ks
        (RufEreignisF.rueck f rho v s0 s1 :: log)

/-- A thread state satisfies the invariant: its log matches its key stack. -/
def RufFadenPasstF (z : RufFadenF D) : Prop :=
  RufLogPasstF (RufFadenSchluesselF z) z.log

/-- A `rueck` entry in the log carries matched data: some entry below it in
    the same log records the same `f`, `rho`, and `s0`. Thread-local and
    immediate: the match is the entry that pushed the frame the return pops. -/
def rufRueckGedecktF (log : List (RufEreignisF D)) : Prop :=
  ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g))
    (s0 s1 : World D),
    RufEreignisF.rueck g rho v s0 s1 ∈ log →
      RufEreignisF.eintritt g rho s0 ∈ log

/-- Auxiliary: every key ON the stack has its entry in the log.
    Induction over the derivation; both constructors feed the goal:
    `eintritt` by the new head (`mem_cons_self`) or the tail IH lifted
    (`mem_cons_of_mem`); `rueck` by the tail IH lifted (the popped key is
    gone from the stack, the survivors keep their entries). Every premise
    is used: `hmem` selects the stack side in each case. -/
theorem rufLogPasstF_mem_eintritt (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstF ks log)
    (k : Σ f : D.Fn, Env D (D.params f) × World D) (hmem : k ∈ ks) :
    RufEreignisF.eintritt k.1 k.2.1 k.2.2 ∈ log := by
  induction h with
  | leer =>
      simp at hmem
  | eintritt s l f rho s0 htail ih =>
      rw [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst hmem
        exact List.mem_cons_self
      · have htailmem := ih hmem
        exact List.mem_cons_of_mem _ htailmem
  | rueck s l f rho s0 vv ss1 htail ih =>
      have htailmem := ih (List.mem_cons_of_mem _ hmem)
      exact List.mem_cons_of_mem _ htailmem

/-- Every well-formed log stack ends in the matching entry: the top
    key has its `eintritt` event in the log. Direct corollary of the
    membership lemma at the head. -/
theorem rufLogPasstF_eintritt_mem (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstF ks log)
    (k : Σ f : D.Fn, Env D (D.params f) × World D) (rest : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (hcon : ks = k :: rest) :
    RufEreignisF.eintritt k.1 k.2.1 k.2.2 ∈ log := by
  have hmem : k ∈ ks := by rw [hcon]; exact List.mem_cons_self
  exact rufLogPasstF_mem_eintritt ks log h k hmem

/-- Every well-formed log has matched returns: induction over the log
    derivation. The `rueck` case closes because the popped key's entry
    event sits in the log tail (the stack-top corollary applied to the
    constructor's tail hypothesis); earlier returns lift through the IH. -/
theorem rufLogPasstF_gedeckt (ks : List (Σ f : D.Fn, Env D (D.params f) × World D))
    (log : List (RufEreignisF D)) (h : RufLogPasstF ks log) :
    rufRueckGedecktF log := by
  induction h with
  | leer =>
      intro f rho v s0 s1 hm
      simp at hm
  | eintritt ks log f rho s0 htail ih =>
      intro g rho' v s0' s1 hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp at hm
      · have hmem := ih g rho' v s0' s1 hm
        rw [List.mem_cons]
        exact Or.inr hmem
  | rueck ks log f rho s0 v s1 htail ih =>
      intro g rho' w s0' s1' hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · cases hm
        have hmem : RufEreignisF.eintritt f rho s0 ∈ log :=
          rufLogPasstF_eintritt_mem (⟨f, rho, s0⟩ :: ks) log htail
            ⟨f, rho, s0⟩ ks rfl
        rw [List.mem_cons]
        exact Or.inr hmem
      · have hmem := ih g rho' w s0' s1' hm
        rw [List.mem_cons]
        exact Or.inr hmem

/-! ## 6. Preservation of the invariant along steps -/

/-- Key-stack helper: the `ruf` step suspends the old head and installs
    the callee head; the new key stack is the callee key over the old one. -/
theorem RufFadenSchluesselF_ruf (z : RufFadenF D)
    (neu : RufRahmenF D) (spur : List (Ereignis D))
    (log : List (RufEreignisF D)) :
    RufFadenSchluesselF
      ⟨z.kopf :: z.stapel, neu, spur, log⟩ =
      RufSchluesselF neu :: RufFadenSchluesselF z := by
  simp [RufFadenSchluesselF]

/-- Key-stack helper: the `blatt` step changes the residue (and the
    stored local environment) but keeps function, parameters, and entry
    world -- so the key stack is unchanged. Both `hfun` (function kept) and
    `hrho`/`hs0` (parameters, entry world kept) feed the rewrite; `hhead`
    selects the `blatt` constructor's head frame. -/
theorem RufFadenSchluesselF_blatt (z : RufFadenF D)
    (l : Bool) (Γ : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ)
    (rb : Endblock D (vertragVon D z.kopf.f) l Γ Λ') :
    RufFadenSchluesselF
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', rb⟩⟩,
       z.spur, z.log⟩ =
      RufFadenSchluesselF z := by
  simp [RufFadenSchluesselF, RufSchluesselF]

/-- The machine invariant: every thread's log matches its key stack. -/
def RufMaschinePasstF (M : RufMaschineF D) : Prop :=
  ∀ f, RufFadenPasstF (M.faeden f)

/-- The start machine satisfies the invariant: every thread starts in its
    entry frame with a singleton `eintritt` log, and the key stack is that
    singleton key. Every premise is used: `hlog` names the start log,
    `hkeys` the start key stack. -/
theorem rufStartF_passt (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    RufMaschinePasstF (RufStartF P sp init) := by
  intro f
  -- `init f` is matched in the start definition, not projected; keep the
  -- equation and rewrite the `match` instead of destructing the value.
  have hpair : ∃ g rho, init f = (⟨g, rho⟩ : Σ f : D.Fn, Env D (D.params f)) :=
    ⟨(init f).1, (init f).2, by cases init f with | mk g rho => rfl⟩
  obtain ⟨g, rho, hif⟩ := hpair
  have hstart : (RufStartF (D := D) P sp init).faeden f =
      (match init f with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', sp.welt [],
          ⟨false, D.params g', Signatur.anfang D (D.signatur g'),
           rho', P.rumpf g'⟩⟩ : RufRahmenF D),
         [], [RufEreignisF.eintritt g' rho' (sp.welt [])]⟩ :
          RufFadenF D)) := rfl
  have hlog : ((RufStartF P sp init).faeden f).log =
      [RufEreignisF.eintritt g rho (sp.welt [])] := by
    rw [hstart, hif]
  have hkeys : RufFadenSchluesselF ((RufStartF P sp init).faeden f) =
      [⟨g, rho, sp.welt []⟩] := by
    rw [hstart, hif]
    rfl
  unfold RufFadenPasstF
  rw [hkeys, hlog]
  exact RufLogPasstF.eintritt [] [] _ _ _ RufLogPasstF.leer

/-- One step preserves the invariant for the ACTING thread.
    `blatt`/`nimmt`/`gibt` keep the key stack (the residue moves, the key
    does not) and the log; `ruf` pushes the callee key with its entry event;
    `rueck` pops the head key with its return event. Every premise of the
    step is used: `hhead`/`hΛ` fix the firing frame, `hstep`/`hrho`/`hv`
    the computed data, `hpop`/`hfg`/`hrho`/`hs0` the popped frame identity,
    `hneu`/`hs0`/`hs1` the trace threading. -/
theorem rufSchrittF_passt_acting (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f : Faden)
    (h : RufFadenPasstF (M.faeden f))
    (hs : RufSchrittF P O passes M f M') :
    RufFadenPasstF (M'.faeden f) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel,
           ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
            ⟨l, Γ, Λ', ρ', rest⟩⟩,
           σ'.spur, (M.faeden f).log⟩ : RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel,
             ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, Λ', ρ', rest⟩⟩,
             σ'.spur, (M.faeden f).log⟩ : RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp [RufFadenSchluesselF, RufSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨σ'.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel,
             ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, Λ', ρ', rest⟩⟩,
             σ'.spur, (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu, M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel,
           ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
            ⟨l, Γ, Λ', ρ', rest⟩⟩,
           σ'.spur, (M.faeden f).log⟩ : RufFadenF D) := by
        simp [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | nimmt L hself hrang hfrei =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
           (M.faeden f).log⟩ : RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
             (M.faeden f).log⟩ : RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp [RufFadenSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
             (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f [Ereignis.nimmt L (offen (M.faeden f).spur)],
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
           (M.faeden f).log⟩ : RufFadenF D) := by
        simp [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | gibt L hhaelt =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
            RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
              RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp [RufFadenSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f [Ereignis.gibt L], M.start⟩ :
          RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, P.rumpf g⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, P.rumpf g⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenF D) =
            (⟨g, rho, s0⟩ :
              Σ f : D.Fn, Env D (D.params f) × World D) ::
              RufFadenSchluesselF (M.faeden f) := by
          simp [RufFadenSchluesselF, RufSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact RufLogPasstF.eintritt _ _ g rho s0 h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, P.rumpf g⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu,
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, P.rumpf g⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | rueck caller rest hpop Γ Λ e hperm ρ hh g hfg rho hr s0 hs0 hΛ s1 hs1 v hv neu hneu =>
      have hkeys : RufFadenPasstF
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        have hhead : RufSchluesselF (M.faeden f).kopf =
            (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
          cases hfg
          simp_all [RufSchluesselF]
        have hk : RufFadenSchluesselF (M.faeden f) =
            RufSchluesselF (M.faeden f).kopf ::
              ((caller :: rest).map RufSchluesselF) := by
          have e : RufFadenSchluesselF (M.faeden f) =
              RufSchluesselF (M.faeden f).kopf ::
                ((M.faeden f).stapel.map RufSchluesselF) := by
            simp [RufFadenSchluesselF]
          rw [e, hpop]
        have htail : RufFadenSchluesselF
            (⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
              RufFadenF D) =
            (caller :: rest).map RufSchluesselF := by
          simp [RufFadenSchluesselF]
        unfold RufFadenPasstF at h ⊢
        rw [hk, hhead] at h
        rw [htail]
        exact RufLogPasstF.rueck _ _ g rho s0 v s1 h
      have heq : (⟨s1.speicher,
          rufUpdateF M.faeden f
            ⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu,
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp [rufUpdateF_self]
      rw [heq]
      exact hkeys

/-! ## 7. Preservation for all threads, reachability, the target -/

/-- One step preserves the invariant at an UNTOUCHED thread: the
    result machine's thread state equals the old one, since `rufUpdateF`
    only replaces the acting thread. Proved by case split on `hs` with
    `subst_vars` (learning `M'`'s shape) and `rufUpdateF_noteq`.
    `hne` selects the untouched side and is consumed by the simp set. -/
theorem rufSchrittF_passt_anders (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f f' : Faden) (hne : f' ≠ f)
    (hs : RufSchrittF P O passes M f M') :
    M'.faeden f' = M.faeden f' := by
  cases hs <;> (subst_vars; simp_all [rufUpdateF_noteq])

/-- One step preserves the invariant for EVERY thread: the acting thread by
    the case split above, every other thread by `rufSchrittF_passt_anders`.
    Both `hact` (acting side) and `hoth` (other side) feed the conclusion;
    `hne` selects the side. -/
theorem rufSchrittF_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f : Faden)
    (h : RufMaschinePasstF M)
    (hs : RufSchrittF P O passes M f M') :
    RufMaschinePasstF M' := by
  intro f'
  by_cases hne : f' = f
  · subst hne
    exact rufSchrittF_passt_acting P O passes M M' f' (h f') hs
  · rw [rufSchrittF_passt_anders P O passes M M' f f' hne hs]
    exact h f'

/-- The invariant holds at every reachable machine: induction on `h`, with
    the start case by `rufStartF_passt` and the step case by
    `rufSchrittF_passt`. Both `hbase` (start evidence) and `hstep` (step
    evidence) feed the conclusion. -/
theorem rufErreichbarF_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineF D)
    (h : RufErreichbarF P O passes (RufStartF P sp init) M) :
    RufMaschinePasstF M := by
  induction h with
  | start => exact rufStartF_passt P sp init
  | schritt M M' f hbase hs ih =>
      exact rufSchrittF_passt P O passes M M' f ih hs

/-- **Return fidelity.** Every `rueck` event in a reachable thread log has
    its matching `eintritt` event in the same log. Proved by induction on
    `h` through the invariant: `rufErreichbarF_passt` gives the well-formed
    log, `rufLogPasstF_gedeckt` reads the match off it. Every premise is
    used: `h` selects the reachable machine, `hmem` the log event. -/
theorem rufF_treu (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineF D)
    (h : RufErreichbarF P O passes (RufStartF P sp init) M) (f : Faden) :
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log →
      RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  have hmach := rufErreichbarF_passt P O passes sp init M h
  have hthread := hmach f
  unfold RufFadenPasstF at hthread
  have hged := rufLogPasstF_gedeckt (RufFadenSchluesselF (M.faeden f))
    (M.faeden f).log hthread
  unfold rufRueckGedecktF at hged
  intro g rho v s0 s1 hmem
  exact hged g rho v s0 s1 hmem

/-! ## 8. Non-trivial witness: one table, a writing leaf, call and return -/

/-- The witness declaration: one table `Unit` with one field of type
    `.int 0 5` (written by the leaf), one function id (`Bool`), no locks,
    no globals, no axioms. The table gives the run a real memory write:
    `assignSlot` changes slots by construction of `execStmt`. -/
def rufDF : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 5
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
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
  sigNr := fun _ =>
    { params := [.int 0 5]
      erg := some (.int 0 6)
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
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

/-- The witness function id: `false` is the CALLER (its body calls
    `true`); `true` is the CALLEE (the writing body). -/
def rufCallerF : rufDF.Fn := show rufDF.Fn from false

def rufIncF : rufDF.Fn := show rufDF.Fn from true

/-- The `erg` of each function, by computation (case on the id). -/
theorem rufDF_erg (f : rufDF.Fn) :
    rufDF.erg f = some (.int 0 6) := by
  cases f with
  | true => rfl
  | false => rfl

/-- The `params` of each function, by computation (case on the id). -/
theorem rufDF_params (f : rufDF.Fn) :
    rufDF.params f = [.int 0 5] := by
  cases f with
  | true => rfl
  | false => rfl

/-- The single parameter environment: the value 2 in `.int 0 5`. -/
def rufRhoF : Env rufDF (rufDF.params rufIncF) :=
  (rufDF_params rufIncF).symm ▸ (.cons ⟨2, by decide, by decide⟩ .nil :
    Env rufDF [.int 0 5])

/-- The single result value: 3 in `.int 0 6`. -/
def rufVF : ErgVal rufDF (rufDF.erg rufIncF) :=
  (rufDF_erg rufIncF).symm ▸ (⟨3, by decide, by decide⟩ : ErgVal rufDF (some (.int 0 6)))

/-- The callee body: one writing leaf (`assignSlot` to slot 0, the
    parameter value), then `ret` of the parameter. The leaf is a `Stmt`
    under the callee contract with `hw : schreibt = true` (the signature
    writes) and `hL : darf` (no guards needed, `braucht = []`). -/
def rufRumpfF : Endblock rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons (.assignSlot () ()
    (.weiter (by decide) (by decide) (.lit 0) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.index (rufDF.count ())))
    ((.weiter (by decide) (by decide) (.var .hier) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 5))) rfl (fun w => nomatch w))
    (.ret (.wert ((.weiter (by decide) (by decide) (.var .hier) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6)))) (by decide))

/-- The call fits: callee writes nothing beyond the caller's rights (both
    write the one table), consumes nothing, holds nothing. -/
theorem rufHpF : RufPasst rufDF (vertragVon rufDF rufCallerF)
    (rufDF.signatur rufIncF) ([] : List (Res rufDF)) where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The call arguments: the single parameter variable. -/
def rufArgsF : Args rufDF [Ty.int 0 5] [] (rufDF.params rufIncF) :=
  (rufDF_params rufCallerF).symm ▸ Args.cons (.var .hier) Args.nil

/-- The caller body: a single `call` to the callee, returning to the empty
    end. Note the caller contract is `vertragVon rufDF rufCallerF` (same
    signature shape, so `params` coincide by `rufDF_params`). -/
def rufCallerRumpfF : Endblock rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) :=
  (rufDF_params rufCallerF).symm ▸
    (.cons (.call rufIncF rufArgsF rufHpF rfl)
      (.ret (.wert ((.weiter (by decide) (by decide) (.var .hier) :
        Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
      Endblock rufDF (vertragVon rufDF rufCallerF) false
        (rufDF.params rufIncF) (nach rufDF rufIncF []))

/-- The program: the caller calls, the callee writes; contracts trivial
    (`wahr`). `requires`/`ensures` play no role in the witness -- only the
    memory move and the log events matter. -/
def rufPF : Programm rufDF where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | true => rufRumpfF
    | false => rufCallerRumpfF

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def rufOF : Orakel rufDF where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The empty world over the witness declaration. -/
def rufWeltF : World rufDF :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => Empty.elim g, []⟩

/-- Named pieces of the witness body: the writing leaf and the `ret`
    tail, so the `blatt` step can name them. -/
def leafSF : Stmt rufDF (vertragVon rufDF rufIncF) false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .assignSlot () ()
    (.weiter (by decide) (by decide) (.lit 0) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.index (rufDF.count ())))
    ((.weiter (by decide) (by decide) (.var .hier) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 5))) rfl (fun w => nomatch w)

def restF : Endblock rufDF (vertragVon rufDF rufIncF) false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  (.ret (.wert ((.weiter (by decide) (by decide) (.var .hier) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6)))) (by decide))

theorem rufRumpfF_eq : rufRumpfF = Endblock.cons leafSF restF := rfl

/-- The leaf is a leaf. -/
theorem leafSF_blatt : leafSF.istBlatt = true := rfl

/-- The leaf writes: the outcome is `.ok` with a changed world and the same
    environment. The world changes because `assignSlot` stores the parameter
    value 2 at slot 0 (was 0); the trace gains the write event. -/
theorem leafSF_mem (σ' : World rufDF) (ρ' : Env rufDF (rufDF.params rufIncF))
    (h : (execStmt (V := vertragVon rufDF rufIncF) rufOF 0 keinRuf leafSF
      rufWeltF rufRhoF) = Ausgang.ok σ' ρ') :
    σ'.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
      ρ' = rufRhoF := by
  have hrfl : (execStmt (V := vertragVon rufDF rufIncF) rufOF 0 keinRuf leafSF
      rufWeltF rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF rufIncF) _ rufRhoF := rfl
  rw [hrfl] at h
  cases h
  refine ⟨rfl, rfl⟩

/-- Start memory: slot 0 holds 0 (the leaf will write 2). -/
def spF : Speicher rufDF :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => Empty.elim g⟩

/-- The caller-side rho: the entry value 2, transported to the caller
    params (same shape, `rufDF_params`). -/
def rhoCallerF : Env rufDF (rufDF.params rufCallerF) :=
  (rufDF_params rufCallerF).symm ▸ rufRhoF

def initF : Faden → Σ f : rufDF.Fn, Env rufDF (rufDF.params f) :=
  fun _ => ⟨rufCallerF, rhoCallerF⟩

theorem initF_rho : initF 0 =
    (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := rfl

def M0F : RufMaschineF rufDF := RufStartF rufPF spF initF

/-- The start head is the caller body with the entry environment.
    Proved by unfolding the start definition and the init function
    (`rfl` fails: the `match` on `initF 0` needs the equation). -/
theorem M0F_kopf :
    (M0F.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, rufCallerRumpfF⟩ := by
  have hstart : (RufStartF (D := rufDF) rufPF spF initF).faeden 0 =
      (match initF 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spF.welt [],
          ⟨false, rufDF.params g', Signatur.anfang rufDF (rufDF.signatur g'),
           rho', rufPF.rumpf g'⟩⟩ : RufRahmenF rufDF),
         [], [RufEreignisF.eintritt g' rho' (spF.welt [])]⟩ :
          RufFadenF rufDF)) := rfl
  have hif : initF 0 = (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by
    simp only [initF]
  have hM : M0F.faeden 0 =
      (⟨[], (⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, rufDF.params rufCallerF,
         Signatur.anfang rufDF (rufDF.signatur rufCallerF),
         rhoCallerF, rufPF.rumpf rufCallerF⟩⟩ : RufRahmenF rufDF),
       [], [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])]⟩ :
        RufFadenF rufDF) := by
    simp only [M0F]
    rw [hstart, hif]
  have hrumpf : rufPF.rumpf rufCallerF = rufCallerRumpfF := rfl
  rw [hM, hrumpf]

/-- The start head function is the caller. -/
theorem M0F_fun : (M0F.faeden 0).kopf.f = rufCallerF := rfl

/-- Caller params unfold to the single int (needed to align `rufArgsF`). -/
theorem callerParamsF : rufDF.params rufCallerF = [.int 0 5] :=
  rufDF_params rufCallerF

/-- The outcome world of the `blatt` step: read (nothing to read) then write
    slot 0 := 2. NOTE: this is the CALLEE leaf outcome at the callee thread
    world, restated below as `leafSF_ok_at` for the actual machine. -/
def outWF : World rufDF :=
  (((spF.welt []).lese
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) []).schreibSlot ()
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) 0 ()
    ⟨2, by decide, by decide⟩)

theorem leafSF_ok : (execStmt rufOF 0 (R := keinRuf)
    (V := vertragVon rufDF rufIncF)
    (Λ := Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Λ' := Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF (spF.welt []) rufRhoF) =
    Ausgang.ok (D := rufDF) (V := vertragVon rufDF rufIncF) outWF rufRhoF := by
  unfold leafSF outWF
  rfl

/-- The outcome world differs from the entry world in memory: slot 0 moves
    from 0 to 2. This is the non-degeneracy the witness needs -- a step that
    changes memory. -/
theorem outWF_moves : outWF.slots () 0 () =
    (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
    (spF.welt []).slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert rufDF (.int 0 5)) := by
  refine ⟨rfl, rfl⟩

/-- `Anfang` of the witness signature is empty: no locks, no marks. -/
theorem anfangF_leer :
    Signatur.anfang rufDF (rufDF.signatur rufIncF) = [] := rfl

/-- Held-exactly at the empty trace: no locks exist. -/
theorem heldLeerF (spur : List (Ereignis rufDF)) :
    HeldGenau ([] : List (Res rufDF)) (offen spur) := by
  intro L
  exact nomatch L

/-- The start head is the writing body with the entry environment.
    STALE shape from before the caller/callee split; kept as documentation
    of the one-function attempt. States the callee residue, which the start
    machine no longer holds (it holds the caller). -/
theorem M0F_kopf_alt :
    rufRumpfF = Endblock.cons leafSF restF :=
  rufRumpfF_eq

/-- The machine after the `ruf` step: the caller frame suspended, the
    callee frame installed with evaluated arguments (`rufRhoF`: the caller
    rho holds 2, so the callee gets 2), entry world the caller thread world
    (no arg reads), log extended with the entry event. -/
def M1F : RufMaschineF rufDF :=
  ⟨M0F.speicher,
   rufUpdateF M0F.faeden 0
     ⟨(M0F.faeden 0).kopf :: (M0F.faeden 0).stapel,
      ⟨rufIncF, rufRhoF, M0F.weltVon 0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF),
        rufRhoF, rufPF.rumpf rufIncF⟩⟩,
      (M0F.weltVon 0).spur,
      (RufEreignisF.eintritt rufIncF rufRhoF (M0F.weltVon 0)) ::
        (M0F.faeden 0).log⟩,
   M0F.lauf ++ rufEigenF 0 [],
   M0F.start⟩

/-- The callee entry world is the caller thread world: the arguments read
    nothing (`var.hier` has no Orte). -/
theorem argsOrteF : rufArgsF.orte = [] := rfl

/-- Step 1 fires the `ruf` rule: head matches (caller body is the call),
    locks vacuous, entry world is the thread world (no arg reads),
    evaluated args are `rufRhoF`, no new trace events. Every premise is
    used: `hhead`/`hΛ`/`hs0`/`hrho`/`hneu` feed the constructor. -/
theorem schritt1F : RufSchrittF rufPF rufOF 0 M0F 0 M1F := by
  have hhead : (M0F.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufCallerF, [],
       rhoCallerF,
       .cons (.call rufIncF rufArgsF rufHpF rfl)
        ((rufDF_params rufCallerF).symm ▸
          (.ret (.wert ((.weiter (by decide) (by decide) (.var .hier) :
            Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
          Endblock rufDF (vertragVon rufDF rufCallerF) false
            (rufDF.params rufIncF) (nach rufDF rufIncF []))⟩ := by
    rw [M0F_kopf]
    rfl
  have hΛ : HeldGenau ([] : List (Res rufDF)) (offen (M0F.faeden 0).spur) :=
    heldLeerF _
  have hs0 : M0F.weltVon 0 =
      (M0F.weltVon 0).lese [] (Args.orte rufArgsF) := by
    rw [argsOrteF]
    rfl
  have hrho : rufRhoF = evalArgs (M0F.weltVon 0) rufArgsF
      (M0F.weltVon 0) rhoCallerF := by
    have hw : M0F.weltVon 0 = spF.welt [] := rfl
    rw [hw]
    rfl
  have hneu : (M0F.weltVon 0).spur = [] ++ (M0F.faeden 0).spur := rfl
  exact RufSchrittF.ruf M0F 0 false (rufDF.params rufCallerF) [] rufIncF
    rufArgsF rufHpF rfl _ rhoCallerF hhead hΛ _ hs0 _ hrho _ hneu

/-- Step 1 as reachability: start, then one step. -/
theorem reach1F : RufErreichbarF rufPF rufOF 0 M0F M1F := by
  exact RufErreichbarF.schritt _ _ 0 RufErreichbarF.start schritt1F

/-- The return expression of the witness body: the parameter widened to
    `.int 0 6`. -/
def eF : ErgExpr rufDF (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (vertragVon rufDF rufIncF).erg :=
  (.wert ((.weiter (by decide) (by decide) (.var .hier) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6))))

theorem restF_eq : restF = Endblock.ret eF (by decide) := rfl

theorem eF_orte : ErgExpr.orte eF = [] := rfl

/-- The return value: the parameter 2 widened to `.int 0 6`. -/
def vF : ErgVal rufDF (rufDF.erg rufIncF) :=
  (rufDF_erg rufIncF).symm ▸ (⟨2, by decide, by decide⟩ : ErgVal rufDF (some (.int 0 6)))

theorem vF_wert : vF = evalErg (M1F.weltVon 0) eF (M1F.weltVon 0) rufRhoF := rfl

/-- The machine after the `blatt` step: the callee residue advanced to
    `restF`, the stored callee environment unchanged (the leaf does not
    bind), memory moved to `outWF`. The new events are the whole outcome
    trace, since the entry trace was empty. -/
def M2F : RufMaschineF rufDF :=
  ⟨outWF.speicher,
   rufUpdateF M1F.faeden 0
     ⟨(M1F.faeden 0).stapel,
      ⟨(M1F.faeden 0).kopf.f, (M1F.faeden 0).kopf.rho, (M1F.faeden 0).kopf.s0,
       ⟨false, rufDF.params rufIncF,
        Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF, restF⟩⟩,
      outWF.spur, (M1F.faeden 0).log⟩,
   M1F.lauf ++ rufEigenF 0 outWF.spur,
   M1F.start⟩

/-- The callee head after the call is the writing body with `rufRhoF`. -/
theorem M1F_kopf :
    (M1F.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufIncF,
     Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
     .cons leafSF restF⟩ := rfl

/-- The thread world is unchanged by the call (no new events). -/
theorem M1F_welt : M1F.weltVon 0 = spF.welt [] := rfl

/-- Step 2 fires the `blatt` rule on the callee frame: the leaf runs under
    the STORED `rufRhoF` (no free binder) and stores the resulting `rufRhoF`
    (the leaf does not bind). Memory moves to `outWF` -- the write. Every
    premise is used: `hhead`/`hΛ`/`hstep`/`hneu` feed the constructor. -/
theorem schritt2F : RufSchrittF rufPF rufOF 0 M1F 0 M2F := by
  have hhead : (M1F.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF), rufRhoF,
       .cons leafSF restF⟩ := M1F_kopf
  have hΛ : HeldGenau (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M1F.faeden 0).spur) := by
    rw [anfangF_leer]
    exact heldLeerF _
  have hstep : (execStmt rufOF 0 (R := keinRuf)
      (V := vertragVon rufDF (M1F.faeden 0).kopf.f)
      leafSF (M1F.weltVon 0) rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF (M1F.faeden 0).kopf.f)
        outWF rufRhoF := by
    rw [M1F_welt]
    exact leafSF_ok
  have hneu : outWF.spur = outWF.spur ++ (M1F.faeden 0).spur := by
    have hspur : (M1F.faeden 0).spur = [] := rfl
    rw [hspur, List.append_nil]
  have hkein : ∀ (L : rufDF.Lock) (h : List rufDF.Lock),
      Ereignis.nimmt L h ∉ (outWF.spur : List (Ereignis rufDF)) := by
    intro L h hm
    exact nomatch L
  exact RufSchrittF.blatt M1F 0 false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    leafSF restF rufRhoF leafSF_blatt hhead hΛ outWF rufRhoF
    outWF.spur hstep hneu hkein

/-- Step 2 as reachability. -/
theorem reach2F : RufErreichbarF rufPF rufOF 0 M0F M2F := by
  exact RufErreichbarF.schritt _ _ 0 reach1F schritt2F

/-- The machine after the `rueck` step: the caller restored, the return
    logged after the entry. The return world is the callee thread world
    (no reads), the value is the widened parameter 2. Every premise is
    used: `hpop`/`hfg`/`hrho`/`hs0` select the head frame, `hΛ` the lock
    state, `hs1`/`hv`/`hneu` feed the constructor. -/
def M3F : RufMaschineF rufDF :=
  ⟨(M2F.weltVon 0).speicher,
   rufUpdateF M2F.faeden 0
     ⟨[], (M0F.faeden 0).kopf, (M2F.weltVon 0).spur,
      [RufEreignisF.rueck rufIncF rufRhoF vF (M0F.weltVon 0) (M2F.weltVon 0)] ++
        (M2F.faeden 0).log⟩,
   M2F.lauf ++ rufEigenF 0 [],
   M2F.start⟩

theorem schritt3F : RufSchrittF rufPF rufOF 0 M2F 0 M3F := by
  have hpop : (M2F.faeden 0).stapel = [(M0F.faeden 0).kopf] := rfl
  have hhead : (M2F.faeden 0).kopf.rest =
      ⟨false, rufDF.params rufIncF,
       Signatur.anfang rufDF (rufDF.signatur rufIncF),
       rufRhoF, .ret eF (by decide)⟩ := rfl
  have hfg : (M2F.faeden 0).kopf.f = rufIncF := rfl
  have hrho : (M2F.faeden 0).kopf.rho = hfg ▸ rufRhoF := rfl
  have hs0 : (M2F.faeden 0).kopf.s0 = M0F.weltVon 0 := rfl
  have hΛ : HeldGenau (Signatur.anfang rufDF (rufDF.signatur rufIncF))
      (offen (M2F.faeden 0).spur) := by
    rw [anfangF_leer]
    exact heldLeerF _
  have hs1 : M2F.weltVon 0 =
      (M2F.weltVon 0).lese
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (ErgExpr.orte eF) := by
    rw [eF_orte]
    rfl
  have hv : vF = hfg ▸ evalErg (M2F.weltVon 0) eF (M2F.weltVon 0) rufRhoF := rfl
  have hneu : (M2F.weltVon 0).spur = [] ++ (M2F.faeden 0).spur := rfl
  exact RufSchrittF.rueck M2F 0 (M0F.faeden 0).kopf [] hpop _ _ _ _ _
    hhead _ hfg rufRhoF hrho _ hs0 hΛ _ hs1 _ hv _ hneu

/-- Step 3 as reachability: three steps FROM THE START STATE. -/
theorem reach3F : RufErreichbarF rufPF rufOF 0 M0F M3F := by
  exact RufErreichbarF.schritt _ _ 0 reach2F schritt3F

/-- Reachability from `RufStartF`: `M0F` IS the start machine. -/
theorem M0F_start : M0F = RufStartF rufPF spF initF := rfl

/-- The witness run reaches `M3F` from the start state. -/
theorem reach3F_start :
    RufErreichbarF rufPF rufOF 0 (RufStartF rufPF spF initF) M3F := by
  rw [← M0F_start]
  exact reach3F

/-- The witness log of thread 0 after all three steps: return, callee
    entry, caller entry. -/
theorem M3F_log : (M3F.faeden 0).log =
    [RufEreignisF.rueck rufIncF rufRhoF vF (M0F.weltVon 0) (M2F.weltVon 0),
     RufEreignisF.eintritt rufIncF rufRhoF (M0F.weltVon 0),
     RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])] := rfl

/-- **Witness for `rufF_treu`.** The premises of `rufF_treu` are instantiated
    JOINTLY with concrete values: the program `rufPF`, the oracle `rufOF`,
    one pass, start memory `spF`, every thread at the caller entry with
    `rhoCallerF`, the reached machine `M3F` (reached FROM THE START STATE by
    `reach3F_start`: `ruf` pushes the callee, `blatt` runs the writing leaf
    -- slot 0 moves 0 -> 2 by `outWF_moves`, a step that changes memory --
    `rueck` pops it), and thread `0`. The log contains the `rueck` event,
    and the matching `eintritt` sits below it in the same log. The program
    is NON-DEGENERATE: one table that the callee writes (`leafSF` via
    `execStmt`), and a three-step run with a memory-changing step. Every
    premise is used: `h` is the reachability, `hmem` the log membership. -/
theorem rufF_treu_zeuge :
    ∃ (M : RufMaschineF rufDF) (f : Faden)
      (g : rufDF.Fn) (rho : Env rufDF (rufDF.params g))
      (v : ErgVal rufDF (rufDF.erg g)) (s0 s1 : World rufDF),
      RufErreichbarF rufPF rufOF 0 (RufStartF rufPF spF initF) M ∧
        RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log ∧
        RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  exact ⟨M3F, 0, rufIncF, rufRhoF, vF, M0F.weltVon 0, M2F.weltVon 0,
    reach3F_start, by rw [M3F_log]; exact List.mem_cons_self,
    by rw [M3F_log]; exact List.mem_cons_of_mem _ (List.mem_cons_self)⟩

-- APPEND-POINT

/-! ## CUTS:
  - Compound statements (`ite`, `locks` bodies, `bind`, loops, indirect and
    reason-channel calls) have no unfold step: the machine is partial there,
    and only straight-line `ret` bodies plus one writing leaf reduce. Full
    continuation threading stays open, as in the D attempt.
  - No contract discharge: the machine never gates on contracts, and no
    theorem connects `rueck` events to `ReqAmEintritt`/`EnsAmRueck`. The
    events carry the actual values such a theorem would need.
  - `rufVF` (result 3) and `rufWeltF`/`rufStartF_passt`-era one-function
    leftovers: `rufVF` is unused (the witness returns the parameter 2 as
    `vF`); `rufWeltF` only serves `leafSF_mem`; `M0F_kopf_alt` restates
    `rufRumpfF_eq`.
-/

#print axioms Gabbro.Grammatik.RufEreignisF.eintritt
#print axioms Gabbro.Grammatik.rufF_treu
#print axioms Gabbro.Grammatik.rufF_treu_zeuge
#print axioms Gabbro.Grammatik.rufSchrittF_passt
#print axioms Gabbro.Grammatik.rufErreichbarF_passt
#print axioms Gabbro.Grammatik.rufLogPasstF_gedeckt
#print axioms Gabbro.Grammatik.schritt1F
#print axioms Gabbro.Grammatik.schritt2F
#print axioms Gabbro.Grammatik.schritt3F
#print axioms Gabbro.Grammatik.reach3F_start
#print axioms Gabbro.Grammatik.outWF_moves

end Gabbro.Grammatik
