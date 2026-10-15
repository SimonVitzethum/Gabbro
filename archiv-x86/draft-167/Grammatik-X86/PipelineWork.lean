/-
  File:      Grammatik/X86/PipelineWork.lean
  Subject:   Source budget to target work and time transfer over the
             direct pipeline lowering (lane 1165).

  Connects the source cost/budget accounting (source `Kosten`/budget
  stops, the goal theorem's `ZeitAb`/budget-stop kinds via
  `BudgetExecution`) to target retired-instruction work: a
  lowering-derived worst-case instruction count per source step
  (`senkStmt` chunks: value code plus address materialisation plus
  slot store), the admitted pipeline summary `pipeSummary`
  (uniform maximum 6, honest zero spill/fence, proved retry bound,
  no exclusions), the derived `Deckung` producer, and the composed
  work/time transfer (`ComposeWorkTransfer`,
  `ComposeBudgetResum`). Named per-form timing bounds stay
  hardware assumptions (`HardwareAssumptions.laufKosten`); they
  never prove software bodies, fairness or bounded CAS retries.

  Reused, not duplicated: `Pipeline.senkStmt`/`senkWertT`/
  `senkWert_als_tief`/`validate`/`pipeline_correct`,
  `ExpressionLowering.senkFrag_laenge` (via `DerivedWorkBound`),
  `DerivedWorkBound.decodiertZu`/`arbeit_decodiert`/`fragmentSummary`
  lemmas, `BudgetExecution` stops and transfer, `CostSummary`
  schema, `TimeTransfer` admission. No second IR, no second source
  interpreter, no new cost model, no checker change, no
  friend-reserved optimiser file.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.ComposeWorkTransfer
import Grammatik.X86.ComposeBudgetResum

namespace Gabbro.Grammatik.X86.PipelineWork

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.OptimizationRules

/-! ## 1. The admitted pipeline summary: uniform maximum 6.

    A shallow lowered assignment chunk is value code (1 or 3
    instructions, `senkFrag_laenge` through `senkWert_als_tief`)
    plus address materialisation plus slot store (2 more), hence
    at most 5; a shallow check is two atoms plus `cmp` plus the
    refusal jump (4). The uniform maximum 6 covers both with
    honest zero spill/fence counts, a proved retry bound and no
    exclusions. -/

/-- The pipeline summary: uniform maximum 6, honest zero
    spill/fence counts, a proved retry bound, no exclusions. -/
def pipeSummary : CostSummary where
  expand := fun _ => some 6
  spillCount := 0
  fenceCount := 0
  retryBound := some 0
  exclusions := []

/-- The pipeline summary is admitted by the validator Bool. -/
theorem pipeSummary_ok : kostenSummeOk pipeSummary = true := by
  decide

/-- The pipeline summary has uniform maximum 6. -/
theorem pipeSummary_max : alleMax pipeSummary = some 6 := by
  decide

/-- The pipeline summary bounds work over any source budget `src` by
    `src * 6`: the expansion formula with honest zero spill/fence. -/
theorem pipeSummary_expand (src : Nat) :
    expandBound pipeSummary src = some (src * 6) := by
  have h := expandBound_keinVerlust pipeSummary src 6 pipeSummary_max
  simpa [pipeSummary] using h

/-! ## 2. Lowering-derived work per source step.

    A successful `senkStmt` assignment chunk is the value code plus
    address materialisation plus slot store, hence exactly two
    instructions longer than the value code. For the shallow
    fragment the value code is 1 or 3 instructions
    (`senkFrag_laenge` through `senkWert_als_tief`), so the chunk
    is 3 or 5. Both the lowering equation and the value equation
    are used. -/

variable {D : Deklaration}

/-- CHUNK SHAPE: a lowered pipeline assignment is the value code
    plus two instructions. -/
theorem senkStmt_chunk_laenge (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (pv code : List Befehl)
    (hpv : senkWertT c e = some pv)
    (h : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) = some code) :
    code.length = pv.length + 2 := by
  unfold senkStmt at h
  dsimp only at h
  cases hk : constInt? i with
  | none =>
    rw [hk] at h
    dsimp only at h
    cases h
  | some k =>
    rw [hk] at h
    dsimp only at h
    cases hloc : L.loc t k f with
    | none =>
      rw [hloc] at h
      dsimp only at h
      cases h
    | some A =>
      rw [hloc] at h
      dsimp only at h
      by_cases hr : repOk (D.typ t f) A 8 0 = true
      · rw [if_pos hr] at h
        rw [hpv] at h
        cases h
        simp only [List.length_append, List.length_cons,
          List.length_nil]
      · rw [if_neg hr] at h
        cases h

/-- CAST TRANSPORT: the deep value lowering sees through a type
    ascription cast (both sides of `g` are variables, so `cases`
    applies). Callers instantiate with the stuck field-type
    equation. Every premise is used. -/
theorem senkWertT_cast (c : PipeCfg) {Γ : Ctx} {Λ : List (Res D)}
    {τ1 τ2 : Ty} (g : τ1 = τ2) (e : Expr D Γ Λ τ1) :
    senkWertT c (cast (congrArg (Expr D Γ Λ) g) e) = senkWertT c e := by
  cases g
  rfl

/-- SHALLOW CHUNK BOUND: a chunk over a shallow value is 3 or 5
    instructions (value code 1 or 3, plus address plus store).
    The deep lowering agrees with the shallow one on the fragment
    (`senkWert_als_tief`), so the fragment count
    (`senkFrag_laenge`) applies. The value type is carried as a
    variable with the equation `hT` (so classification unifies)
    and the statement casts (`senkWertT_cast`). Every premise is
    used: `hflach` feeds agreement and classification, `hT` the
    cast, `h` the chunk shape. -/
theorem senkStmt_flach_laenge (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (p code : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (h : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some code) :
    code.length = 3 ∨ code.length = 5 := by
  have htief : senkWertT c e = some p :=
    senkWert_als_tief _ _ _ _ _ _ hflach
  have hcast : senkWertT c (cast (congrArg (Expr D Γ Λ) hT) e) = some p := by
    rw [senkWertT_cast c hT e]
    exact htief
  have hlen := senkStmt_chunk_laenge c L l t f i _ hw hL p code hcast h
  match hIst : istWert_von (abbOf c) e c.dst c.tmp p hflach with
  | .frag e' p' h' =>
    have hfrag := senkFrag_laenge (abbOf c) e' c.dst c.tmp p' h'
    omega
  | .weiter h1 h2 e' p' h' =>
    have hfrag := senkFrag_laenge (abbOf c) e' c.dst c.tmp p' h'
    omega

/-- DECKUNG PRODUCER (the missing leg for pipeline chunks): every
    shallow lowered pipeline chunk is covered in machine work by
    the admitted pipeline summary over any positive source
    budget. `Deckung` is DERIVED from the chunk bound plus the
    summary expansion -- it is never a premise. Every premise is
    used: `hflach`/`hchunk`/`hT` bound the generated length,
    `hsrc` keeps the scaled bound above it. -/
theorem deckung_pipeChunk (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (src : Nat)
    (p chunk : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (hchunk : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk)
    (hsrc : 1 ≤ src) :
    Deckung pipeSummary src (decodiertZu chunk) := by
  have hlen := senkStmt_flach_laenge c L l t f i e hT hw hL p chunk hflach hchunk
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have hwork : targetWork ((decodiertZu chunk).map fun d => d.befehl) =
      chunk.length :=
    arbeit_decodiert chunk
  rw [hwork]
  omega

/-! ## 3. Work/time transfer over pipeline chunks.

    The derived chunk coverage (`deckung_pipeChunk`) plugs into
    the accepted separate transfer
    (`BudgetExecution.budgetAusfuehrung_transfer`): a lowered
    chunk whose generated code aggregates to named time `tt`
    under profile `prof` is covered in target time by the
    admitted pipeline summary over the source budget. Units stay
    separate: `src` counts source steps (the `Budget` ops side),
    `targetWork` counts retired generated instructions, `tt`
    counts named target time. -/

/-- MAIN: a shallow lowered pipeline chunk aggregating to named
    time `tt` is covered in target time by the admitted pipeline
    summary over the source budget. Every premise is used:
    `hflach`/`hchunk`/`hT`/`hsrc` feed the derived coverage,
    `hCost`/`hb` the hardware aggregation. -/
theorem pipeline_arbeit_zeit (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (prof : HardwareProfil) (src B tt : Nat)
    (p chunk : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (hchunk : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk)
    (hsrc : 1 ≤ src)
    (hCost : laufKosten prof (decodiertZu chunk) = some tt)
    (hb : ∀ dd ∈ decodiertZu chunk,
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B) :
    ∀ k, expandBound pipeSummary src = some k → tt ≤ B * k := by
  have hDeck := deckung_pipeChunk c L l t f i e hT hw hL src p chunk
    hflach hchunk hsrc
  exact budgetAusfuehrung_transfer pipeSummary prof _ src B tt hCost hb hDeck

/-- UNIT PINNING (generic): the three counts in the main theorem
    are three separate numbers with three separate counters --
    source steps `src` feed the summary expansion, retired
    instructions feed `targetWork`, named per-form costs feed
    `laufKosten`. Every premise feeds the closed connection. -/
theorem einheiten_pipe (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (src : Nat)
    (p chunk : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (hchunk : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk) :
    expandBound pipeSummary src = some (src * 6) ∧
    targetWork ((decodiertZu chunk).map fun d => d.befehl) = chunk.length ∧
    (chunk.length = 3 ∨ chunk.length = 5) := by
  refine ⟨pipeSummary_expand src, arbeit_decodiert chunk, ?_⟩
  exact senkStmt_flach_laenge c L l t f i e hT hw hL p chunk hflach hchunk

/-! ## 4. Budget-stop connection: exhaustion meets work spent.

    The derived chunk coverage closes the producer/consumer gap
    of `ComposeBudgetResum_verbindung`: ghost source-budget
    correspondence, transfer at `src`, resumption at `src'`, and
    the joint stopping order (over-budget head op names the
    source budget breach AND the refused head form refuses the
    target aggregation). Exhaustion TIMING stays open (owned by
    the scheduling lanes). Every premise is used. -/

/-- CLOSING: source budget exhaustion meets target work spent
    for a lowered pipeline chunk, with ghost correspondence and
    resumption. -/
theorem pipeline_budget_arbeit (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (prof : HardwareProfil) (src src' B tt ghost : Nat)
    (bound left : Nat) (op : Op) (rest : List Op)
    (dd : Decodiert) (tl : List Decodiert)
    (p chunk : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (hchunk : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk)
    (hsrc : 1 ≤ src)
    (hCost : laufKosten prof (decodiertZu chunk) = some tt)
    (hb : ∀ d ∈ decodiertZu chunk,
      ∃ cc, schrittKosten prof d = some cc ∧ cc ≤ B)
    (hGhost : ghost = src)
    (hSrcOver : ¬ op.cost ≤ left)
    (hTgtRef : schrittKosten prof dd = none)
    (hResum : src ≤ src') :
    Deckung pipeSummary ghost (decodiertZu chunk) ∧
    (∀ k, expandBound pipeSummary src = some k → tt ≤ B * k) ∧
    (∀ k', expandBound pipeSummary src' = some k' → tt ≤ B * k') ∧
    ((∃ needed, runOps bound left (op :: rest)
      = .budget "per_pass.ops" needed bound) ∧
    laufKosten prof (dd :: tl) = none) := by
  have hDeck := deckung_pipeChunk c L l t f i e hT hw hL src p chunk
    hflach hchunk hsrc
  exact ComposeBudgetResum_verbindung pipeSummary prof _ src src' B tt ghost
    bound left op rest dd tl 6 hGhost pipeSummary_max hDeck hCost hb
    hSrcOver hTgtRef hResum

/-! ## 5. Validator closing: source run, bytes, work and time.

    In the style of `pipeline_correct_entry`: the source
    `execBlock` result is related to the byte-level run on the
    loaded image (`pipeline_correct`, reused as a black box --
    no second interpreter), AND the validated bytes are exactly
    the encoding of the work-counted program (`validate_sound`
    plus the decoded link `hdec`), which carries the retired-work
    and named-time bounds. Named timing stays a hardware
    assumption; entry/image admission beyond `CodeAt` composes
    through `PipelineEntry`/`PipelineImage` (see CUTS). Every
    premise is used. -/

/-- PIPELINE WORK CORRECTNESS: a validated program runs from the
    loaded image to the code end with world and environment
    represented, its bytes are the encoding of the counted
    program, and retired work and named time are bounded. -/
theorem pipeline_arbeit_korrekt (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (prog : List Befehl)
    (hval : validate c L certs src bytes = true)
    (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (st : Zustand)
    (hcode : CodeAt st.speicher (natAdresse c.codeBase) bytes)
    (hrip : st.rip = natAdresse c.codeBase)
    (hW : WorldRep L st.speicher σ) (hE : EnvRepr ρ st.register (abbOf c))
    (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ')
    (hdec : decodeAll bytes.length bytes = some prog)
    (prof : HardwareProfil) (srcB B tt k : Nat)
    (hDeck : Deckung pipeSummary srcB (decodiertZu prog))
    (hCost : laufKosten prof (decodiertZu prog) = some tt)
    (hb : ∀ dd ∈ decodiertZu prog,
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B)
    (hk : expandBound pipeSummary srcB = some k) :
    (∃ n s', laufBytes n st = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep L s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c)) ∧
    bytes = encodeAll prog ∧
    targetWork prog ≤ k ∧ tt ≤ B * k := by
  obtain ⟨n, s', hrun, hrip', hW', hE'⟩ :=
    pipeline_correct c L certs src bytes hval hsep O passes R σ ρ st
      hcode hrip hW hE σ' ρ' hsrc
  obtain ⟨prog', hc, hlow, hbytes, hdec', hcomp⟩ :=
    validate_sound c L certs src bytes hval
  have hprog : prog' = prog := by
    rw [hdec] at hdec'
    cases hdec'
    rfl
  have hbytes' : bytes = encodeAll prog := by
    rw [hprog] at hbytes
    exact hbytes
  have hwork := hDeck k hk
  rw [arbeit_decodiert] at hwork
  have htime :=
    budgetAusfuehrung_transfer pipeSummary prof _ srcB B tt hCost hb hDeck k hk
  refine ⟨⟨n, s', hrun, hrip', hW', hE'⟩, hbytes', ?_, htime⟩
  exact hwork

/-! ## 6. Refusals: what the pipeline chunk transfer does not cover.

    Four planted cases. An underestimated work bound below the
    shortest generated chunk (3) covers nothing; multiplication
    has no deep lowering, so no chunk exists for it; a depth-two
    addition with no scratch register left is refused, not
    guessed; an unbounded retry site behind a constant bound
    refuses summary AND transfer admission together. Nothing is
    weakened to make a bound go through. -/

/-- MULTIPLICATION has no deep lowering, at any scratch stack. -/
theorem senkTief_verweigert_mul {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst : Register) (frei : List Register) :
    senkTief abb
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2)
        (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst frei = none := rfl

/-- UNSUPPORTED-FORM REFUSAL: no chunk exists for `2 * 3`. Every
    premise is used: `c` feeds the lowering in `hp`. -/
theorem pipeline_arbeit_verweigert_mul (c : PipeCfg)
    {Γ : Ctx} {Λ : List (Res D)} :
    ¬ ∃ p, senkWertT c
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2)
        (Expr.lit (Γ := Γ) (Λ := Λ) 3)) = some p := by
  intro h
  obtain ⟨p, hp⟩ := h
  unfold senkWertT at hp
  rw [senkTief_verweigert_mul] at hp
  cases hp

/-- A depth-two addition with no scratch register left has no
    deep lowering either: the inner addition already needs one. -/
theorem senkTief_verweigert_tief {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) :
    senkTief abb
      (Expr.add
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) 1)
          (Expr.lit (Γ := Γ) (Λ := Λ) 2))
        (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst [tmp] = none := rfl

/-- SCRATCH-EXHAUSTION REFUSAL: with `frei = []` the depth-two
    addition lowers to nothing -- refused, not guessed. Every
    premise is used: `hfrei` rewrites the scratch stack in
    `hp`. -/
theorem pipeline_arbeit_verweigert_tief (c : PipeCfg)
    {Γ : Ctx} {Λ : List (Res D)}
    (hfrei : c.frei = []) :
    ¬ ∃ p, senkWertT c
      (Expr.add
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) 1)
          (Expr.lit (Γ := Γ) (Λ := Λ) 2))
        (Expr.lit (Γ := Γ) (Λ := Λ) 3)) = some p := by
  intro h
  obtain ⟨p, hp⟩ := h
  unfold senkWertT at hp
  rw [hfrei] at hp
  rw [senkTief_verweigert_tief] at hp
  cases hp

/-- UNDERESTIMATED-WORK REFUSAL: no lowered chunk is covered by
    a bound below 3 -- the shortest chunk is three
    instructions. Every premise is used: `hflach`/`hchunk`
    give the length formula, `hk` the failed claim. -/
theorem pipeline_arbeit_verweigert_knapp (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (p chunk : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (hchunk : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk)
    (k : Nat) (hk : k < 3) :
    ¬ targetWork ((decodiertZu chunk).map fun d => d.befehl) ≤ k := by
  have hlen := senkStmt_flach_laenge c L l t f i e hT hw hL p chunk hflach hchunk
  rw [arbeit_decodiert]
  omega

/-- UNBOUNDED-RETRY REFUSAL: the pipeline summary with its retry
    bound removed refuses admission AND transfer together -- a
    CAS retry loop never gets a free constant. -/
theorem pipeline_arbeit_verweigert_retry (prof : HardwareProfil) :
    kostenSummeOk { pipeSummary with retryBound := none } = false ∧
    zeitTransferZulaessig { pipeSummary with retryBound := none } prof =
      false :=
  kein_freier_versuch _ prof 6 rfl rfl

/-! ## 7. Witness infrastructure: one program, real runs.

    All joint witnesses below share the accepted pipeline
    witness program (`PipelineWitnesses`: one table its contract
    writes, source run moving the slots `7 -> 35` and `9 -> 6`
    through actual `execBlock`, fetched-byte run observably
    changing memory). Its first chunk is a shallow lowered
    pipeline chunk; the whole program is fully priced. -/

/-- The first witness chunk lowers through the deep value
    lowering to the same three instructions. -/
theorem pwTief0 :
    senkWertT pwCfg pwWert0 =
      some [Befehl.movReg64 .rax .r10, Befehl.movImm64 .rcx (intWort 5),
        Befehl.addReg64 .rax .rcx] := rfl

/-- The first witness statement lowers to the first five
    instructions of the candidate: value code plus address
    materialisation plus slot store. -/
theorem pwChunkWit :
    senkStmt pwCfg pwL
      (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0 pwHw pwHL) =
      some (pwProg.take 5) := rfl

/-- The witness chunk aggregates to named time `1+1+2+1+3 = 8`. -/
theorem kosten_chunkWit :
    laufKosten profilZeuge (decodiertZu (pwProg.take 5)) = some 8 := by
  decide

/-- Every witness-chunk step costs at most 3. -/
theorem hb_chunkWit :
    ∀ d ∈ decodiertZu (pwProg.take 5),
      ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 3 := by
  have hlist : decodiertZu (pwProg.take 5) =
      [{ befehl := Befehl.movReg64 .rax .r10,
         laenge := (encode (Befehl.movReg64 .rax .r10)).length },
        { befehl := Befehl.movImm64 .rcx (intWort 5),
          laenge := (encode (Befehl.movImm64 .rcx (intWort 5))).length },
        { befehl := Befehl.addReg64 .rax .rcx,
          laenge := (encode (Befehl.addReg64 .rax .rcx)).length },
        { befehl := Befehl.movImm64 .rbx (natAdresse 8192),
          laenge := (encode (Befehl.movImm64 .rbx (natAdresse 8192))).length },
        { befehl := Befehl.store64 .rbx .rax (BitVec.ofNat 32 0),
          laenge := (encode (Befehl.store64 .rbx .rax
            (BitVec.ofNat 32 0))).length }] := rfl
  rw [hlist]
  intro d hd
  simp only [List.mem_cons, List.mem_nil_iff] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | hnil
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨2, rfl, by decide⟩
  · exact ⟨1, rfl, by decide⟩
  · exact ⟨3, rfl, by decide⟩
  · cases hnil

/-- The whole witness program is covered by the pipeline
    summary over source budget 2 (`12 ≤ 2 * 6`). -/
theorem deckung_pwProg : Deckung pipeSummary 2 (decodiertZu pwProg) := by
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have hwork : targetWork ((decodiertZu pwProg).map fun d => d.befehl) =
      pwProg.length :=
    arbeit_decodiert pwProg
  have hlen : pwProg.length = 12 := rfl
  omega

/-- The whole witness program aggregates to named time 18. -/
theorem kosten_pwProg :
    laufKosten profilZeuge (decodiertZu pwProg) = some 18 := by
  decide

/-- Every witness-program step costs at most 3: case per
    instruction form (all pilot forms but `ret` are priced `≤ 3`;
    `ret` is not in the program). -/
theorem hb_pwProg :
    ∀ d ∈ decodiertZu pwProg,
      ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 3 := by
  intro d hd
  simp only [decodiertZu, List.mem_map] at hd
  obtain ⟨a, ha, hfa⟩ := hd
  subst hfa
  cases a with
  | movImm64 _ _ => exact ⟨1, rfl, by decide⟩
  | movReg64 _ _ => exact ⟨1, rfl, by decide⟩
  | addReg64 _ _ => exact ⟨2, rfl, by decide⟩
  | subReg64 _ _ => exact ⟨2, rfl, by decide⟩
  | xorReg64 _ _ => exact ⟨2, rfl, by decide⟩
  | cmpReg64 _ _ => exact ⟨2, rfl, by decide⟩
  | load64 _ _ _ => exact ⟨3, rfl, by decide⟩
  | store64 _ _ _ => exact ⟨3, rfl, by decide⟩
  | jump32 _ => exact ⟨1, rfl, by decide⟩
  | jumpIf32 _ _ => exact ⟨1, rfl, by decide⟩
  | push64 _ => exact ⟨2, rfl, by decide⟩
  | pop64 _ => exact ⟨2, rfl, by decide⟩
  | call32 _ => exact ⟨3, rfl, by decide⟩
  | ret => exact absurd ha (by decide)

/-! ## 7. Poison probes: every refusal fires on concrete data.

    Each probe evaluates the actual lowering/validator function
    on witness data and is refused -- by computation, never by
    stipulation. -/

/-- Bound 2 covers no chunk (the witness chunk retires 5). -/
theorem gift_pipe_knapp :
    ¬ targetWork ((decodiertZu (pwProg.take 5)).map fun d => d.befehl) ≤ 2 := by
  decide

/-- `2 * 3` has no deep lowering. -/
theorem gift_pipe_mul :
    senkWertT (D := pwD) pwCfg
      (Expr.mul (Expr.lit (Γ := pwCtx) (Λ := []) 2)
        (Expr.lit (Γ := pwCtx) (Λ := []) 3)) = none := by
  decide

/-- The depth-two addition has no lowering with an empty scratch
    register file (the witness configuration lends none beyond
    `tmp`). -/
theorem gift_pipe_tief :
    senkWertT (D := pwD) pwCfg
      (Expr.add
        (Expr.add (Expr.lit (Γ := pwCtx) (Λ := []) 1)
          (Expr.lit (Γ := pwCtx) (Λ := []) 2))
        (Expr.lit (Γ := pwCtx) (Λ := []) 3)) = none := by
  decide

/-- An unbounded retry site refuses summary admission. -/
theorem gift_pipe_retry :
    kostenSummeOk { pipeSummary with retryBound := none } = false := by
  decide

/-! ## 8. Joint witnesses: one table, real runs.

    All witnesses share the accepted pipeline witness package:
    the contract writes the table, the source `execBlock` run
    moves the slots `7 -> 35` and `9 -> 6`, and the fetched-byte
    run observably changes memory. Each `_zeuge` instantiates
    ALL premises of its theorem jointly on this package and
    proves the conclusion through the proved step. -/

/-- The shared non-degenerate package Prop: a table the contract
    writes, a memory-changing source run, and a memory-changing
    fetched-byte target run. -/
def PipePaket : Prop :=
  pwV.schreibt () = true ∧
  (∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
    (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
    (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6) ∧
  (∃ a : Adresse, ausgangByte a (laufBytes 12 (pwStart 30)) ≠
    some ((pwStart 30).speicher.bytes a))

/-- The shared non-degenerate package holds. -/
theorem pipePaket_hold : PipePaket := by
  refine ⟨pwHw, ?_, ?_⟩
  · obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
    exact ⟨σ', ρ', hsrc, pw_quelle_vorher.1, h0, pw_quelle_vorher.2, h1⟩
  · have h1 := pw_bytes30.2.1
    have h2 : (pwStart 30).speicher.bytes (natAdresse 8192) = natByte 7 :=
      pw_bytes_vorher.1
    refine ⟨natAdresse 8192, ?_⟩
    rw [h1, h2]
    decide

/-- The field-type equation of the first witness slot, by `rfl`. -/
theorem pwHT0 : pwD.typ () () = pwD.typ () () := rfl

/-- The first witness chunk with its cast: the cast is the
    identity on a `rfl` equation, so the proved lowering
    applies definitionally. -/
theorem pwChunkCast :
    senkStmt pwCfg pwL
      (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
        (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
      some (pwProg.take 5) :=
  pwChunkWit

/-- Joint witness for `senkStmt_chunk_laenge`. -/
theorem senkStmt_chunk_laenge_zeuge :
    ∃ (pv code : List Befehl),
      senkWertT pwCfg pwWert0 = some pv ∧
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0
          pwHw pwHL) = some code ∧
      code.length = pv.length + 2 ∧
      PipePaket := by
  refine ⟨_, _, pwTief0, pwChunkWit, ?_, pipePaket_hold⟩
  exact senkStmt_chunk_laenge pwCfg pwL false () () pwIdx0 pwWert0 pwHw pwHL
    _ _ pwTief0 pwChunkWit

/-- Joint witness for `senkStmt_flach_laenge`. -/
theorem senkStmt_flach_laenge_zeuge :
    ∃ (p code : List Befehl),
      senkWert (abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some code ∧
      (code.length = 3 ∨ code.length = 5) ∧
      PipePaket := by
  refine ⟨_, _, pw_senkWert0, pwChunkCast, ?_, pipePaket_hold⟩
  exact senkStmt_flach_laenge pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
    pwHw pwHL _ _ pw_senkWert0 pwChunkCast

/-- Joint witness for `deckung_pipeChunk`, with the derived
    coverage. -/
theorem deckung_pipeChunk_zeuge :
    ∃ (p chunk : List Befehl),
      senkWert (abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      1 ≤ 1 ∧
      Deckung pipeSummary 1 (decodiertZu chunk) ∧
      PipePaket := by
  refine ⟨_, _, pw_senkWert0, pwChunkCast, Nat.le_refl 1, ?_, pipePaket_hold⟩
  exact deckung_pipeChunk pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
    pwHw pwHL 1 _ _ pw_senkWert0 pwChunkCast (Nat.le_refl 1)

/-- Joint witness for the main transfer, with the time bound
    `8 ≤ 3 * k` through the proved step. -/
theorem pipeline_arbeit_zeit_zeuge :
    ∃ (p chunk : List Befehl),
      senkWert (abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      1 ≤ 1 ∧
      laufKosten profilZeuge (decodiertZu chunk) = some 8 ∧
      (∀ dd ∈ decodiertZu chunk,
        ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3) ∧
      (∀ k, expandBound pipeSummary 1 = some k → 8 ≤ 3 * k) ∧
      PipePaket := by
  refine ⟨_, _, pw_senkWert0, pwChunkCast, Nat.le_refl 1, kosten_chunkWit,
    hb_chunkWit, ?_, pipePaket_hold⟩
  exact pipeline_arbeit_zeit pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
    pwHw pwHL profilZeuge 1 3 8 _ _ pw_senkWert0 pwChunkCast
    (Nat.le_refl 1) kosten_chunkWit hb_chunkWit

/-- Joint witness for `einheiten_pipe`: `src * 6` bounds work,
    work counts the generated list, the chunk is 5 long. -/
theorem einheiten_pipe_zeuge :
    ∃ (p chunk : List Befehl),
      senkWert (abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      expandBound pipeSummary 1 = some (1 * 6) ∧
      targetWork ((decodiertZu chunk).map fun d => d.befehl) =
        chunk.length ∧
      (chunk.length = 3 ∨ chunk.length = 5) ∧
      PipePaket := by
  obtain ⟨hexp, hwork, hlen⟩ :=
    einheiten_pipe pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
      pwHw pwHL 1 _ _ pw_senkWert0 pwChunkCast
  exact ⟨_, _, pw_senkWert0, pwChunkCast, hexp, hwork, hlen, pipePaket_hold⟩

/-- Joint witness for the budget-stop closing, with ghost
    budget 1, transfer at `src = 1` and resumed `src' = 2`,
    and both planted stop facts (over-budget head op, refused
    `ret` head). -/
theorem pipeline_budget_arbeit_zeuge :
    ∃ (p chunk : List Befehl),
      senkWert (abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      1 ≤ 1 ∧
      laufKosten profilZeuge (decodiertZu chunk) = some 8 ∧
      (∀ dd ∈ decodiertZu chunk,
        ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3) ∧
      1 = 1 ∧
      ¬ (fremdOp 3).cost ≤ 3 ∧
      schrittKosten profilZeuge { befehl := Befehl.ret, laenge := 1 } =
        none ∧
      1 ≤ 2 ∧
      (Deckung pipeSummary 1 (decodiertZu chunk) ∧
        (∀ k, expandBound pipeSummary 1 = some k → 8 ≤ 3 * k) ∧
        (∀ k', expandBound pipeSummary 2 = some k' → 8 ≤ 3 * k') ∧
        ((∃ needed, runOps 3 3 [fremdOp 3]
          = .budget "per_pass.ops" needed 3) ∧
        laufKosten profilZeuge [{ befehl := Befehl.ret, laenge := 1 }] =
          none)) ∧
      PipePaket := by
  refine ⟨_, _, pw_senkWert0, pwChunkCast, Nat.le_refl 1, kosten_chunkWit,
    hb_chunkWit, rfl, by decide, rfl, by decide, ?_, pipePaket_hold⟩
  exact pipeline_budget_arbeit pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
    pwHw pwHL profilZeuge 1 2 3 8 1 3 3 (fremdOp 3) []
    { befehl := Befehl.ret, laenge := 1 } [] _ _ pw_senkWert0 pwChunkCast
    (Nat.le_refl 1) kosten_chunkWit hb_chunkWit rfl (by decide) rfl (by decide)

/-- Joint witness for the validator closing: every premise holds
    jointly on the accepted program (two written slots, checked
    bytes, priced steps), and so do all four conclusions. -/
theorem pipeline_arbeit_korrekt_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧
      LayoutSep pwL ∧
      CodeAt (pwStart 30).speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      (pwStart 30).rip = natAdresse pwCfg.codeBase ∧
      WorldRep pwL (pwStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pwStart 30).register (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      decodeAll pwBytes.length pwBytes = some pwProg ∧
      Deckung pipeSummary 2 (decodiertZu pwProg) ∧
      laufKosten profilZeuge (decodiertZu pwProg) = some 18 ∧
      (∀ dd ∈ decodiertZu pwProg,
        ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3) ∧
      expandBound pipeSummary 2 = some 12 ∧
      (∃ n s', laufBytes n (pwStart 30) = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
        WorldRep pwL s'.speicher σ' ∧
        EnvRepr ρ' s'.register (abbOf pwCfg)) ∧
      pwBytes = encodeAll pwProg ∧
      targetWork pwProg ≤ 12 ∧ 18 ≤ 3 * 12 ∧
      PipePaket := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  have hmain := pipeline_arbeit_korrekt pwCfg pwL pwCerts pwSrc pwBytes pwProg
    pw_validate pw_layoutSep pwO 0 pwR pwSigma pwEnv30 (pwStart 30) pw_code
    rfl pw_worldRep pw_envRepr30 σ' ρ' hsrc pw_decode profilZeuge 2 3 18 12
    deckung_pwProg kosten_pwProg hb_pwProg (pipeSummary_expand 2)
  obtain ⟨hrun, hbytes, hwork, htime⟩ := hmain
  exact ⟨σ', ρ', pw_validate, pw_layoutSep, pw_code, rfl, pw_worldRep,
    pw_envRepr30, hsrc, pw_decode, deckung_pwProg, kosten_pwProg, hb_pwProg,
    pipeSummary_expand 2, hrun, hbytes, hwork, htime, pipePaket_hold⟩

/-- Joint witness for the underestimated-work refusal: bound 2
    covers nothing. -/
theorem pipeline_arbeit_verweigert_knapp_zeuge :
    ∃ (p chunk : List Befehl),
      senkWert (abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      2 < 3 ∧
      ¬ targetWork ((decodiertZu chunk).map fun d => d.befehl) ≤ 2 ∧
      PipePaket := by
  refine ⟨_, _, pw_senkWert0, pwChunkCast, by decide, ?_, pipePaket_hold⟩
  exact pipeline_arbeit_verweigert_knapp pwCfg pwL false () () pwIdx0
    pwWert0 pwHT0 pwHw pwHL _ _ pw_senkWert0 pwChunkCast 2 (by decide)

/-- Joint witness for the cast transport. -/
theorem senkWertT_cast_zeuge :
    ∃ (p : List Befehl),
      senkWertT pwCfg
        (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) = some p ∧
      senkWertT pwCfg pwWert0 = some p ∧
      PipePaket := by
  refine ⟨_, ?_, pwTief0, pipePaket_hold⟩
  rw [senkWertT_cast pwCfg pwHT0 pwWert0]
  exact pwTief0

/-- Joint witness for the multiplication refusal. -/
theorem pipeline_arbeit_verweigert_mul_zeuge :
    (¬ ∃ p, senkWertT (D := pwD) pwCfg
      (Expr.mul (Expr.lit (Γ := pwCtx) (Λ := []) 2)
        (Expr.lit (Γ := pwCtx) (Λ := []) 3)) = some p) ∧
    PipePaket :=
  ⟨pipeline_arbeit_verweigert_mul pwCfg, pipePaket_hold⟩

/-- Joint witness for the scratch-exhaustion refusal. -/
theorem pipeline_arbeit_verweigert_tief_zeuge :
    (¬ ∃ p, senkWertT (D := pwD) pwCfg
      (Expr.add
        (Expr.add (Expr.lit (Γ := pwCtx) (Λ := []) 1)
          (Expr.lit (Γ := pwCtx) (Λ := []) 2))
        (Expr.lit (Γ := pwCtx) (Λ := []) 3)) = some p) ∧
    PipePaket :=
  ⟨pipeline_arbeit_verweigert_tief pwCfg rfl, pipePaket_hold⟩

/-- Joint witness for the unbounded-retry refusal. -/
theorem pipeline_arbeit_verweigert_retry_zeuge :
    (kostenSummeOk { pipeSummary with retryBound := none } = false ∧
    zeitTransferZulaessig { pipeSummary with retryBound := none }
      profilZeuge = false) ∧
    PipePaket :=
  ⟨pipeline_arbeit_verweigert_retry profilZeuge, pipePaket_hold⟩

/- CUTS:
    - Proved here (generic): the admitted pipeline summary
      (`pipeSummary_ok`, `pipeSummary_max`, `pipeSummary_expand`:
      uniform maximum 6, honest zero spill/fence, proved retry
      bound, no exclusions); the lowering-derived chunk shape
      (`senkStmt_chunk_laenge`: value code plus two
      instructions); the cast transport (`senkWertT_cast`); the
      shallow chunk bound (`senkStmt_flach_laenge`: 3 or 5); the
      derived `Deckung` producer (`deckung_pipeChunk`, never a
      premise); the work/time transfer (`pipeline_arbeit_zeit`)
      with unit pinning (`einheiten_pipe`: source steps,
      retired instructions and named time stay three separate
      counts); the budget-stop closing
      (`pipeline_budget_arbeit`: ghost correspondence, transfer
      at `src`, resumption at `src'`, joint stopping order);
      the validator closing (`pipeline_arbeit_korrekt`: fetched
      run agreement plus validated-bytes equation plus
      retired-work and named-time bounds); four refusals
      (underestimated work, multiplication, scratch exhaustion,
      unbounded retry); witness infrastructure and four poison
      probes (all firing by computation); joint
      non-degenerate witnesses for every syntax-premise theorem.
    - Witness-only: every `_zeuge` is joint on the accepted
      pipeline witness program (one table its contract writes;
      source slots `7 -> 35`, `9 -> 6` through actual
      `execBlock`; fetched-byte run observably changing
      memory); `PipePaket`/`pipePaket_hold` bundle the package.
    - OPEN (fragment): per-chunk coverage is single shallow
      assignments -- a `senkWert` value (literal, variable, one
      bounded add/sub over atoms, one `weiter` skin) plus
      address materialisation plus slot store. Deeper trees
      beyond the scratch registers, checks and branches with
      jumps, loops, calls, floats, pointers, aggregates and
      globals carry no bound here -- all refused (`none`), never
      guessed.
    - OPEN (blocks): multi-statement programs compose only over
      carried `Deckung` (as in `pipeline_arbeit_korrekt`); no
      block-size induction from chunk bounds to whole-program
      `src` is proved here.
    - OPEN (scheduling): exhaustion TIMING -- when the target
      stops relative to source exhaustion, interleavings,
      waiting delays -- is owned by the scheduling/IR lanes;
      the transfer bounds admitted finite prefixes only.
    - OPEN (entry/image): admission beyond `CodeAt` (mapping,
      entry sequence, ABI duties, guards) composes through
      `PipelineImage`/`PipelineEntry`; no TSO/concurrency claim
      (per-access target-to-W/GX simulation stays with the
      bridge lanes).
    - OPEN (timing-model fidelity): `tt` counts NAMED per-form
      bounds from the selected profile, never measured silicon
      latencies; `ret` stays refused; no constant-time claim; no
      CAS-progress, fairness or zero-cost-stutter promise
      (unbounded retries are refused, never bounded).
    - No new interpreter, no second cost model, no IR: the one
      `senkStmt`/`senkWertT` lowering, the one `targetWork`,
      the one `laufKosten` aggregation and the actual
      `execBlock`/`lauf`/`laufBytes` runs are reused untouched.
      An optimisation that folds or drops code MUST recompute
      work over the new list (fold recomputation owned by
      `DerivedWorkBound`). No checker, Spec, goal, emitter or
      friend-reserved file is touched.
-/

#print axioms pipeSummary_ok
#print axioms pipeSummary_max
#print axioms pipeSummary_expand
#print axioms senkStmt_chunk_laenge
#print axioms senkWertT_cast
#print axioms senkStmt_flach_laenge
#print axioms deckung_pipeChunk
#print axioms pipeline_arbeit_zeit
#print axioms einheiten_pipe
#print axioms pipeline_budget_arbeit
#print axioms pipeline_arbeit_korrekt
#print axioms senkTief_verweigert_mul
#print axioms pipeline_arbeit_verweigert_mul
#print axioms senkTief_verweigert_tief
#print axioms pipeline_arbeit_verweigert_tief
#print axioms pipeline_arbeit_verweigert_knapp
#print axioms pipeline_arbeit_verweigert_retry
#print axioms pwTief0
#print axioms pwChunkWit
#print axioms kosten_chunkWit
#print axioms hb_chunkWit
#print axioms deckung_pwProg
#print axioms kosten_pwProg
#print axioms hb_pwProg
#print axioms gift_pipe_knapp
#print axioms gift_pipe_mul
#print axioms gift_pipe_tief
#print axioms gift_pipe_retry
#print axioms PipePaket
#print axioms pipePaket_hold
#print axioms pwHT0
#print axioms pwChunkCast
#print axioms senkStmt_chunk_laenge_zeuge
#print axioms senkStmt_flach_laenge_zeuge
#print axioms deckung_pipeChunk_zeuge
#print axioms pipeline_arbeit_zeit_zeuge
#print axioms einheiten_pipe_zeuge
#print axioms pipeline_budget_arbeit_zeuge
#print axioms pipeline_arbeit_korrekt_zeuge
#print axioms pipeline_arbeit_verweigert_knapp_zeuge
#print axioms senkWertT_cast_zeuge
#print axioms pipeline_arbeit_verweigert_mul_zeuge
#print axioms pipeline_arbeit_verweigert_tief_zeuge
#print axioms pipeline_arbeit_verweigert_retry_zeuge

end Gabbro.Grammatik.X86.PipelineWork
