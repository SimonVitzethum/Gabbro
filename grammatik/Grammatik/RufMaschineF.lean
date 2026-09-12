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
    side of `ensures`) and the return world `s1`. -/
inductive RufEreignisF (D : Deklaration) where
  | eintritt (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
  | rueck (f : D.Fn) (rho : Env D (D.params f))
      (v : ErgVal D (D.erg f)) (s0 s1 : World D)

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

-- APPEND-POINT

/-! ## CUTS:
  - Skeleton only: machine core, steps, invariant, target, witness follow.
-/

#print axioms Gabbro.Grammatik.RufEreignisF.eintritt

end Gabbro.Grammatik
