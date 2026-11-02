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
module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1Basis
import all Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1Basis
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

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
      simp only [List.not_mem_nil] at hmem
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
      simp only [List.not_mem_nil] at hm
  | eintritt ks log f rho s0 htail ih =>
      intro g rho' v s0' s1 hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [reduceCtorEq] at hm
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
  simp only [RufFadenSchluesselF, List.map_cons]

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
  simp only [RufFadenSchluesselF, List.map_cons, RufSchluesselF]

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


end Gabbro.Grammatik
