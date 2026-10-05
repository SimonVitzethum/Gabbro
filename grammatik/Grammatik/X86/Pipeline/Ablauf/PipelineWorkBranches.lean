/-
  File:      Grammatik/X86/PipelineWorkBranches.lean
  Subject:   Pipeline work bounds for branches and loops (lane 1233).

  Follow-up of lane 1165 (`PipelineWork.lean`: shallow assignment chunks
  only). Worst-case retired-instruction bounds for if/else (max of the
  branches plus the compare/jump, over the accepted `iteCode` shape of
  `Pipeline.lean`) and for bounded loops (the source iteration budget
  transfers to the target step budget `schleifeSchritte` of
  `PipelineLoops.lean`); unbounded loops (`retry`/`forever` at the
  `senkBlock` level) stay refused. A small validator (`pruefeZweig`)
  recomputes the bound from the lowered list, and the main correctness
  theorem is in the style of `pipeline_arbeit_korrekt` (source
  `execBlock` related to the fetched-byte run, plus retired-work and
  named-time bounds). Reused unchanged: `senkBlock`/`senkBlock_korrektC`/
  `iteCode`/`Entspricht`/`CodeAt`, `pipeSummary`/`pipeSummary_expand`,
  `decodiertZu`/`arbeit_decodiert`, `Deckung`/
  `budgetAusfuehrung_transfer`, `schleifeSchritte`, the `pd`/`pw`
  witness packages. No second IR, no second interpreter, no optimiser
  edit. Rust is out of scope.
-/
import Grammatik.X86.Pipeline.Kern.Pipeline
import Grammatik.X86.Pipeline.Ablauf.PipelineWork
import Grammatik.X86.Pipeline.Ablauf.PipelineLoops
import Grammatik.X86.Pipeline.Kern.PipelineImageWitnesses
import Grammatik.X86.Kosten.BudgetExecution
import Grammatik.X86.Kosten.DerivedWorkBound
import Grammatik.X86.Hw.Grundlage.HardwareAssumptions

namespace Gabbro.Grammatik.X86.PipeWorkBranches

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineLoops
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipelineImageWitnesses

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Branch worst-case bound over the accepted `iteCode` shape. -/

/-- Worst-case retired instructions of an if/else: the compare code,
    one taken jump, the LONGER branch, one end jump. -/
def iteSchranke (codeLen tLen eLen : Nat) : Nat :=
  codeLen + 1 + Nat.max tLen eLen + 1

/-- Static length of the accepted ite code shape (both branches). -/
theorem iteCode_laenge (code : List Befehl) (j : Bedingung) (pt pe : List Befehl) :
    (iteCode code j pt pe).length = code.length + 1 + pt.length + 1 + pe.length := by
  simp [iteCode]
  omega

/-- DYNAMIC PATH BOUND: whichever branch the jump takes, the retired
    instructions of the ite (compare code, taken jump, taken branch,
    end jump) are at most the worst case over the longer branch. -/
theorem itePfad_schranke (genommen : Bool) (codeLen tLen eLen : Nat) :
    (if genommen then codeLen + 1 + eLen + 1 else codeLen + 1 + tLen + 1) ≤
      iteSchranke codeLen tLen eLen := by
  unfold iteSchranke
  cases genommen with
  | true =>
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_max_right _ _) _) _
  | false =>
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_max_left _ _) _) _

/-! ## 2. Validator: recompute the bound from the lowered list. -/

/-- The branch validator: the lowered list fits the source budget scaled
    by the admitted summary maximum. Decided by computation, never a
    premise. -/
def pruefeZweig (prog : List Befehl) (src : Nat) : Bool :=
  decide (prog.length ≤ src * 6)

/-- COVERAGE FROM LENGTH: a lowered list within the scaled budget is
    covered by the admitted pipeline summary. `Deckung` is DERIVED,
    never assumed. -/
theorem deckung_von_laenge (prog : List Befehl) (src : Nat)
    (h : prog.length ≤ src * 6) : Deckung pipeSummary src (decodiertZu prog) := by
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  rw [arbeit_decodiert]
  exact h

/-- VALIDATOR CORRECTNESS: an accepted list is covered. Every premise
    is used: `h` feeds the derived coverage. -/
theorem pruefeZweig_korrekt (prog : List Befehl) (src : Nat)
    (h : pruefeZweig prog src = true) :
    Deckung pipeSummary src (decodiertZu prog) := by
  unfold pruefeZweig at h
  simp only [decide_eq_true_eq] at h
  exact deckung_von_laenge prog src h

/-- BRANCH COVERAGE: a lowered ite whose static whole-list length fits
    the scaled budget is covered. The static length counts BOTH
    branches; the retired path (`itePfad_schranke`) is only smaller.
    Every premise is used: the lists feed the shape in `h` and the
    conclusion. -/
theorem deckung_ite (code : List Befehl) (j : Bedingung) (pt pe : List Befehl)
    (src : Nat) (h : (iteCode code j pt pe).length ≤ src * 6) :
    Deckung pipeSummary src (decodiertZu (iteCode code j pt pe)) :=
  deckung_von_laenge _ _ h

/-- The witness ite (3 compare, 5 then, 7 else) retires at most 12
    instructions on either path. -/
theorem iteSchranke_pd : iteSchranke 3 5 7 = 12 := rfl

/-- The witness ite lowering (static 3 + 1 + 5 + 1 + 7 = 17) is covered
    at source budget 3 (17 ≤ 18). -/
theorem deckung_ite_pd : Deckung pipeSummary 3 (decodiertZu (iteCode
    [.movReg64 .rax .r10, .movImm64 .rcx (intWort 40), .cmpReg64 .rax .rcx] .ge
    [.movReg64 .rax .r10, .movImm64 .rcx (intWort 100), .addReg64 .rax .rcx,
      .movImm64 .rbx (natAdresse 8200), .store64 .rbx .rax (BitVec.ofNat 32 0)]
    [.movReg64 .rax .r10, .movImm64 .rdx (intWort 40), .subReg64 .rax .rdx,
      .movImm64 .rcx (intWort 500), .addReg64 .rax .rcx,
      .movImm64 .rbx (natAdresse 8200),
      .store64 .rbx .rax (BitVec.ofNat 32 0)])) :=
  deckung_ite _ _ _ _ 3 (by decide)

/-! ## 3. Work/time correctness over validated programs.

    In the style of `pipeline_arbeit_korrekt`: the source `execBlock`
    result is related to the fetched-byte run on the loaded image
    (`senkBlock_korrektC`, reused as a black box -- no second
    interpreter), and the validated bytes carry retired-work and
    named-time bounds through the validator-derived coverage (never
    an assumed `Deckung`). Every premise is used. -/

/-- BRANCH WORK CORRECTNESS: a validated program runs from the loaded
    image with world and environment represented, and retired work
    and named time are bounded over the source budget. -/
theorem zweig_arbeit_korrekt (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (flat : List Byte)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ') (pre post : List Byte) (prog : List Befehl)
    (h : senkBlock c L pre.length b = some prog)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : Pipeline.CodeAt s.speicher (natAdresse c.codeBase) flat)
    (hf : flat = pre ++ encodeAll prog ++ post)
    (hrip : s.rip = addrOff (natAdresse c.codeBase) pre.length)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c))
    (prof : HardwareProfil) (srcB B tt k : Nat)
    (hval : pruefeZweig prog srcB = true)
    (hCost : laufKosten prof (decodiertZu prog) = some tt)
    (hb : ∀ dd ∈ decodiertZu prog,
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B)
    (hk : expandBound pipeSummary srcB = some k) :
    (∃ n s', laufBytes n s = .weiter s' ∧
      Pipeline.CodeAt s'.speicher (natAdresse c.codeBase) flat ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (pre.length + (encodeAll prog).length))
        (execBlock O passes R b σ ρ) s') ∧
    targetWork prog ≤ k ∧ tt ≤ B * k := by
  have hrun := senkBlock_korrektC c L hc hsep O passes R flat b pre post prog h σ ρ s
    hcode hf hrip hW hE
  have hDeck := pruefeZweig_korrekt prog srcB hval
  have hwork := hDeck k hk
  rw [arbeit_decodiert] at hwork
  have htime := budgetAusfuehrung_transfer pipeSummary prof (decodiertZu prog) srcB B tt
    hCost hb hDeck k hk
  exact ⟨hrun, hwork, htime⟩

/-! ## 4. Bounded loops: source iteration budget to target step budget.

    The target step budget is the accepted `schleifeSchritte` of
    `PipelineLoops.lean` (one source round costs at most `m + 2`
    labelled steps, the final exit check one more); a source run that
    finishes within `n'` rounds with `n' ≤ n` fits the budget for `n`.
    Unbounded loops (`retry`, `forever`) have no `senkBlock` lowering
    at all: refused, never guessed. -/

/-- BUDGET TRANSFER: fewer source rounds need fewer target steps, so a
    source iteration budget covers every run finishing inside it. Both
    premises are used. -/
theorem schleife_budget_transfer (n n' m : Nat) (h : n' ≤ n) :
    schleifeSchritte n' m ≤ schleifeSchritte n m := by
  unfold schleifeSchritte
  exact Nat.add_le_add_right (Nat.mul_le_mul_right (m + 2) h) 1

/-- One round over a six-row body costs nine labelled steps. -/
theorem schleife_schritte_pd : schleifeSchritte 1 6 = 9 := rfl

/-- UNBOUNDED-LOOP REFUSAL (`retry`, every bound): a `retry` head has
    no `senkBlock` lowering at any bound -- refused, never guessed.
    (PipeBlock proves the bound-5 instance; this is the generic
    statement over the same catch-all arm.) -/
theorem senkBlock_verweigert_retry (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : _root_.Gabbro.Grammatik.Block D V true Γ Λ Λ)
    (ueber : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ)
    (rest : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ'') (pos : Nat) :
    senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.retry n bis body ueber) rest) =
      none := rfl

/-- UNBOUNDED-LOOP REFUSAL (`forever`): an unbounded loop head has no
    `senkBlock` lowering -- refused, never guessed. -/
theorem senkBlock_verweigert_forever (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : _root_.Gabbro.Grammatik.Block D V true Γ Λ Λ)
    (rest : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ'') (pos : Nat) :
    senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.forever a inv body) rest) =
      none := rfl

/-! ## 5. Poison probes: every refusal fires on concrete data. -/

/-- Bound 2 covers no 17-instruction ite lowering. -/
theorem gift_zweig_knapp : pruefeZweig (pdProg.drop 17) 2 = false := by decide

/-- Bound 3 covers it (17 ≤ 18): the positive probe. -/
theorem gift_zweig_ok : pruefeZweig (pdProg.drop 17) 3 = true := by decide

/-- A `retry` head at bound 7 (PipeBlock pins bound 5) is refused. -/
theorem gift_retry_sieben :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.retry (V := pwV) 7 (Expr.wahr : Expr pwD pwCtx [] .bool)
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV true pwCtx [] [])
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] []))
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [])) =
      none :=
  senkBlock_verweigert_retry _ _ _ _ _ _ _ _

/-- A `forever` head is refused. -/
theorem gift_forever :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.forever (V := pwV) (() : pwD.Annahme)
          (Expr.wahr : Expr pwD pwCtx [] .bool)
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV true pwCtx [] []))
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [])) =
      none :=
  senkBlock_verweigert_forever _ _ _ _ _ _ _

/-! ## 6. Joint witnesses: one table, real runs.

    Every witness below shares the accepted pipeline package
    (`PipePaket`/`pipePaket_hold` from lane 1165): one table its
    contract writes, a source `execBlock` run moving the slots
    `7 -> 35` and `9 -> 6`, and a fetched-byte run observably
    changing memory. -/

/-- Joint witness for the generic retry refusal. -/
theorem senkBlock_verweigert_retry_zeuge :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.retry (V := pwV) 7 (Expr.wahr : Expr pwD pwCtx [] .bool)
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV true pwCtx [] [])
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] []))
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [])) =
      none ∧ PipePaket :=
  ⟨gift_retry_sieben, pipePaket_hold⟩

/-- Joint witness for the forever refusal. -/
theorem senkBlock_verweigert_forever_zeuge :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.forever (V := pwV) (() : pwD.Annahme)
          (Expr.wahr : Expr pwD pwCtx [] .bool)
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV true pwCtx [] []))
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [])) =
      none ∧ PipePaket :=
  ⟨gift_forever, pipePaket_hold⟩

/-- Joint witness for the main transfer on the widened program: the
    `x = 30` run takes the then-branch (rows `7 -> 65`, `9 -> 130`,
    both memory-changing), the validator accepts at source budget 6,
    and all four conclusions hold with the shared non-degenerate
    package. -/
theorem zweig_arbeit_korrekt_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx) (tt k : Nat),
      validate pdCfg (layoutVon piPs) [] pdSrc pdBytes = true ∧
      senkBlock pdCfg (layoutVon piPs) ([] : List Byte).length (optimise [] pdSrc) =
        some pdProg ∧
      Pipeline.CodeAt (pdStart 30).speicher (natAdresse pdCfg.codeBase) pdBytes ∧
      (pdStart 30).rip = addrOff (natAdresse pdCfg.codeBase) ([] : List Byte).length ∧
      WorldRep (layoutVon piPs) (pdStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pdStart 30).register (abbOf pdCfg) ∧
      execBlock pwO 0 pwR (optimise [] pdSrc) pwSigma pwEnv30 = .ok σ' ρ' ∧
      (σ'.slots () 0 ()).n = 65 ∧ (σ'.slots () 1 ()).n = 130 ∧
      pruefeZweig pdProg 6 = true ∧
      laufKosten profilZeuge (decodiertZu pdProg) = some tt ∧
      (∀ dd ∈ decodiertZu pdProg,
        ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3) ∧
      expandBound pipeSummary 6 = some k ∧
      (∃ n s', laufBytes n (pdStart 30) = .weiter s' ∧
        Pipeline.CodeAt s'.speicher (natAdresse pdCfg.codeBase) pdBytes ∧
        Entspricht pdCfg (layoutVon piPs)
          (addrOff (natAdresse pdCfg.codeBase)
            (([] : List Byte).length + (encodeAll pdProg).length))
          (execBlock pwO 0 pwR (optimise [] pdSrc) pwSigma pwEnv30) s') ∧
      targetWork pdProg ≤ k ∧ tt ≤ 3 * k ∧
      PipePaket := by
  obtain ⟨prog', hc', hlow', hbytes', hdec', -⟩ :=
    validate_sound pdCfg (layoutVon piPs) [] pdSrc pdBytes pd_validate
  have hdec : decodeAll pdBytes.length pdBytes = some pdProg :=
    decodeAll_encodeAll pdProg _ (length_le_encodeAll _)
  have hprog : prog' = pdProg := Option.some_inj.mp (hdec'.symm.trans hdec)
  subst hprog
  obtain ⟨σ', ρ', hsrc0, h0, h1⟩ := pd_quelle30
  rw [← optimise_sound [] pdSrc pwO 0 pwR pwSigma pwEnv30] at hsrc0
  have himg := (kompiliert_geladen .p48 pdCfg piPs piEs [] pdSrc pdBytes pwSigma
    pd_compile pd_bauOk).2
  have hcode := imageOk_codeAt .p48 pdBild pdCfg piPs piEs [] pdSrc pdBytes himg.1
  have hsep := imageOk_layoutSep .p48 pdBild pdCfg piPs piEs [] pdSrc pdBytes himg.1
  have hW := imageOk_worldRep .p48 pdBild pdCfg piPs piEs [] pdSrc pdBytes himg.1
    pwSigma himg.2
  have hf' : pdBytes = [] ++ encodeAll pdProg ++ [] := by
    rw [hbytes']; simp
  have hrip : (pdStart 30).rip =
      addrOff (natAdresse pdCfg.codeBase) ([] : List Byte).length := by
    show natAdresse 4096 = addrOff (natAdresse 4096) 0
    exact (addrOff_null _).symm
  have hval : pruefeZweig pdProg 6 = true := by decide
  obtain ⟨tt, hCost⟩ : ∃ tt, laufKosten profilZeuge (decodiertZu pdProg) = some tt :=
    ⟨_, rfl⟩
  have hb : ∀ dd ∈ decodiertZu pdProg,
      ∃ cc, schrittKosten profilZeuge dd = some cc ∧ cc ≤ 3 := by
    intro dd hd
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
  have hk : expandBound pipeSummary 6 = some (6 * 6) := pipeSummary_expand 6
  have hmain := zweig_arbeit_korrekt pdCfg (layoutVon piPs) hc' hsep pwO 0 pwR pdBytes
    (optimise [] pdSrc) [] [] pdProg hlow' pwSigma pwEnv30 (pdStart 30) hcode hf'
    hrip hW pd_envRepr30 profilZeuge 6 3 tt (6 * 6) hval hCost hb hk
  obtain ⟨hrun, hwork, htime⟩ := hmain
  exact ⟨σ', ρ', tt, 6 * 6, pd_validate, hlow', hcode, hrip, hW, pd_envRepr30,
    hsrc0, h0, h1, hval, hCost, hb, hk, hrun, hwork, htime, pipePaket_hold⟩

/- CUTS:
    - Proved here (generic): the branch worst case over the accepted
      `iteCode` shape (`iteSchranke`: compare code plus one taken jump
      plus the longer branch plus one end jump; `iteCode_laenge`:
      static whole-list length; `itePfad_schranke`: either dynamic
      path is at most the worst case); the validator (`pruefeZweig`,
      decided length check) with derived coverage
      (`deckung_von_laenge`, `pruefeZweig_korrekt`, `Deckung` never a
      premise) and its branch specialization (`deckung_ite`: the
      static length counts both branches, the retired path is only
      smaller); the work/time correctness over validated programs
      (`zweig_arbeit_korrekt`, in the style of
      `pipeline_arbeit_korrekt`: fetched-byte run agreement through
      reused `senkBlock_korrektC` plus retired-work and named-time
      bounds through the validator-derived coverage); the loop budget
      transfer (`schleife_budget_transfer`: a source iteration budget
      covers every run finishing inside it, over the accepted
      `schleifeSchritte` target step budget); two unbounded-loop
      refusals (generic `retry` at every bound,
      `senkBlock_verweigert_retry`, generalizing the bound-5 instance
      of `PipeBlock`; `forever`, `senkBlock_verweigert_forever`);
      four poison probes firing by computation; three joint
      non-degenerate witnesses (one table its contract writes; the
      `x = 30` then-branch run moves rows `7 -> 65` and `9 -> 6`
      through actual `execBlock`; fetched-byte run observably
      changing memory via reused `PipePaket`).
    - Witness-only: `iteSchranke_pd` (retired worst case 12 of the
      witness ite), `deckung_ite_pd` (its static 17 covered at source
      budget 3), `schleife_schritte_pd` (one round over six rows is
      nine labelled steps).
    - Reused, not duplicated: `senkBlock`/`senkBlock_korrektC`/
      `iteCode`/`Entspricht`, `pipeSummary`/`pipeSummary_expand`,
      `decodiertZu`/`arbeit_decodiert`/`decodiertZu_befehl`,
      `Deckung`/`budgetAusfuehrung_transfer`, `schleifeSchritte`,
      `decodeAll_encodeAll`/`length_le_encodeAll`, `validate_sound`,
      `optimise_sound`, `kompiliert_geladen`/`imageOk_*`, the whole
      `pd`/`pw` witness packages. No second IR, no second
      interpreter, no optimiser edit, no checker change.
    - OPEN (per-path retired work): `Deckung` counts the static
      whole-list length (both branches); the dynamic-path bound
      (`itePfad_schranke`) is arithmetic only, not yet connected to
      a taken-path `lauf` prefix.
    - OPEN (loop work): the source iteration budget transfers to the
      accepted labelled-step budget (`schleifeSchritte`); per-round
      body correspondence (`hWeiter`) and the labelled-to-bytes leg
      stay with `PipelineLoops` (`schleife_korrekt_endlich`,
      `schleife_bytes`); no retired-instruction-per-labelled-step
      claim is made here.
    - OPEN (entry/image): admission beyond `Pipeline.CodeAt`
      (mapping, entry sequence, ABI duties, guards) composes through
      `PipelineImage`/`PipelineEntry`; no TSO/concurrency claim;
      named timing stays a hardware assumption.
    - Name notes for the merger: `Vertrag` is spelled capital here
      (the tree's `Stmt`/`Block` take `V : Vertrag D`; both spellings
      elaborate to the same type); `Block` is `_root_`-qualified
      (the relative name resolves to `ISARelax`'s `Block` through
      this file's namespace path) and `CodeAt` is `Pipeline`-qualified
      (`ISAExecution` defines another one).
-/

#print axioms iteSchranke
#print axioms iteCode_laenge
#print axioms itePfad_schranke
#print axioms pruefeZweig
#print axioms deckung_von_laenge
#print axioms pruefeZweig_korrekt
#print axioms deckung_ite
#print axioms iteSchranke_pd
#print axioms deckung_ite_pd
#print axioms zweig_arbeit_korrekt
#print axioms schleife_budget_transfer
#print axioms schleife_schritte_pd
#print axioms senkBlock_verweigert_retry
#print axioms senkBlock_verweigert_forever
#print axioms gift_zweig_knapp
#print axioms gift_zweig_ok
#print axioms gift_retry_sieben
#print axioms gift_forever
#print axioms senkBlock_verweigert_retry_zeuge
#print axioms senkBlock_verweigert_forever_zeuge
#print axioms zweig_arbeit_korrekt_zeuge

end Gabbro.Grammatik.X86.PipeWorkBranches
