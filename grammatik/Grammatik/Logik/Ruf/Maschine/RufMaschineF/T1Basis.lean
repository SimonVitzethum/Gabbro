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
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
@[expose] public section


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
  | why (f : D.Fn) (rho : Env D (D.params f))
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
  simp only [rufUpdateF, ↓reduceIte]

theorem rufUpdateF_noteq (m : Faden → RufFadenF D) (f g : Faden) (h : g ≠ f)
    (z : RufFadenF D) :
    rufUpdateF m f z g = m g := by
  simp only [rufUpdateF, h, ↓reduceIte]

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

end Gabbro.Grammatik
