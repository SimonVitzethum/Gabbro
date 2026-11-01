module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.VertragOrtB

@[expose] public section



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
  simp only [rufUpdateD, ↓reduceIte]

theorem rufUpdateD_noteq (m : Faden → RufFadenD D) (f g : Faden) (h : g ≠ f)
    (z : RufFadenD D) :
    rufUpdateD m f z g = m g := by
  simp only [rufUpdateD, h, ↓reduceIte]

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
      simp only [List.not_mem_nil] at hmem
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
      simp only [List.not_mem_nil] at hm
  | eintritt stapel log f rho s0 htail _ ih =>
      intro g rho' v s0' s1 hm
      rw [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [reduceCtorEq] at hm
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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
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
  .eq (.var .here)
    ((.widen (by decide) (by decide) (.lit 2) :
      Expr rufD (rufD.params rufIncD) [] (.int 0 5)))

/-- `ensures`: the result equals the parameter plus one.
    Context `[.int 0 5, .int 0 5]`: result at `.here`, parameter at `.there .here`. -/
end Gabbro.Grammatik
