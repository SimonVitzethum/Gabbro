module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.VertragOrtB
public import Grammatik.Logik.Ruf.Maschine.RufMaschineD.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- `ensures`: the result equals the parameter plus one.
    Context `[.int 0 5, .int 0 5]`: result at `.here`, parameter at `.there .here`. -/
def rufEnsLitD : Expr rufD [.int 0 6, .int 0 5] [] .bool :=
  .eq (.var .here)
    (.add (.widen (by decide) (by decide) (.var (.there .here)) :
          Expr rufD [.int 0 6, .int 0 5] [] (.int 0 5))
        (.widen (by decide) (by decide) (.lit 1) :
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
    | true => .ret (.val
        (.add (.var .here)
          (.widen (by decide) (by decide) (.lit 1) :
            Expr rufD (rufD.params rufIncD) (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))) :
        ErgExpr rufD (rufD.params rufIncD)
          (Signatur.anfang rufD (rufD.signatur rufIncD)) (rufD.erg rufIncD))
        (by decide)
    | false => .ret (.val
        (.add (.var .here)
          (.widen (by decide) (by decide) (.lit 1) :
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
    (rufD.signatur rufIncD).schreibt t = false := by rfl

/-- The call fits: callee writes nothing, consumes nothing, holds nothing. -/
theorem rufHpD : RufPasst rufD (vertragVon rufD rufIncD)
    (rufD.signatur rufIncD) ([] : List (Res rufD)) where
  hw := fun t ht => by rw [rufSigSchreibtFalse t] at ht; cases ht
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The call arguments: the single variable. -/
def rufArgsD : Args rufD [Ty.int 0 5] [] (rufD.params rufIncD) :=
  (rufD_params rufIncD).symm ▸ Args.cons (.var .here) Args.nil

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
    (.ret (.val (.widen (by decide) (by decide) (.var .here))) (by decide))


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
theorem rufArgsOrteLeerD : rufArgsD.orte = [] := by rfl

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
  .val (.add (.var .here)
    ((.widen (by decide) (by decide) (.lit 1) :
      Expr rufD (rufD.params rufIncD)
        (Signatur.anfang rufD (rufD.signatur rufIncD)) (.int 0 1))))

/-- The callee residue is `ret` of param + 1, definitionally. -/
theorem rufRumpfRetD : rufPD.rumpf rufIncD =
    Endblock.ret rufRetED
      (by decide : (Signatur.anfang rufD (rufD.signatur rufIncD)).Perm
        (vertragVon rufD rufIncD).ende) := by rfl

/-- The return reads nothing. -/
theorem rufRetOrteLeerD : ErgExpr.orte rufRetED = [] := by rfl

/-- The return evaluates to 3 = 2 + 1. -/
theorem rufRetWertD : evalErg rufWeltD rufRetED rufWeltD rufRhoD = rufVD := by rfl

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
theorem rufM1WeltD : rufM1D.weltVon 0 = rufWeltD := by rfl

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
        simp only [List.not_mem_nil] at hmem
  rw [List.mem_cons, List.mem_singleton] at hlog
  rcases hlog with hlog | hlog
  · cases hlog
    refine ⟨?_, ?_⟩
    · intro g rho s0 hev
      simp only [reduceCtorEq] at hev
    · intro g rho v s0 s1 hev
      simp only [RufEreignisD.rueck.injEq] at hev
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hev
      show EnsAmRueck rufPD rufIncD (rufCallerMD.weltVon 0) rufWeltD rufRhoD rufVD
      have : rufCallerMD.weltVon 0 = rufWeltD := rfl
      rw [this]
      exact ruf_ens_am_ortD
  · cases hlog
    refine ⟨?_, ?_⟩
    · intro g rho s0 hev
      simp only [RufEreignisD.eintritt.injEq] at hev
      obtain ⟨rfl, rfl, rfl⟩ := hev
      show ReqAmEintritt rufPD rufIncD (rufCallerMD.weltVon 0) rufRhoD
      have : rufCallerMD.weltVon 0 = rufWeltD := rfl
      rw [this]
      exact ruf_req_am_ortD
    · intro g rho v s0 s1 hev
      simp only [reduceCtorEq] at hev



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
