/-
  File:      Grammatik/X86/PipelineChunkDerive.lean
  Subject:   Per-chunk runs and coverage DERIVED from the lowering alone
              (lane 1219, follow-up of lane 1195 `PipelineBlockInduct`).

  Lane 1195 assumes per-chunk runs (`hrun`), coverage (`hdeck`) and time
  as premises of its two-chunk block theorem. Here the run and the
  coverage of one `assignSlot` chunk are derived from the lowering
  (`senkStmt`) plus the admitted layout/representation (`WorldRep`,
  `LayoutSep`, `cfgOk`), and the induction is extended from two conses
  to n-chunk dependent `assignSlot` chains (`blockAusChunks`). Named
  hardware timing stays a hardware assumption; unsupported shapes are
  refused, never guessed. No second IR, no second interpreter, no
  optimiser edit, no existing-file edit. Rust is out of scope.
-/
import Grammatik.X86.Pipeline.Ablauf.PipelineBlockInduct

namespace Gabbro.Grammatik.X86.PipeChunkDerive

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipeBlock

/-- A lowerable assignment chunk: one placed integer slot at a constant
    index with a deeply lowered value. By construction every element is
    an `assignSlot`, so no case split over the other statement forms
    is ever needed. -/
structure AssignChunk (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) where
  t : D.Tab
  f : D.Feld t
  i : Expr D Γ Λ (.index (D.count t))
  e : Expr D Γ Λ (D.typ t f)
  hw : V.schreibt t = true
  hL : darf D t Λ

open Gabbro.Grammatik.X86.OptimizationRules

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-! ## 1. The lowering inversion: what an accepted chunk is.

    An accepted `senkStmt` over `assignSlot` IS a constant index, a
    placed admitted slot and a deeply lowered value, followed by the
    address materialisation and the slot store. This inversion is what
    lets every later derivation start from the lowering alone. -/

/-- Canonical decoding is the canonical map: `decodiertZu` runs through
    `kanon`, the same map the `lauf` correctness lemmas use. -/
theorem decodiertZu_map_kanon (p : List Befehl) :
    decodiertZu p = p.map kanon := by
  simp [decodiertZu, kanon]

/-- LOWERING INVERSION (single chunk): an accepted assignment chunk is
    a constant index `k`, a placed admitted slot address `A` and a
    deeply lowered value `pv`, with the chunk `pv` plus address plus
    store. Every premise is used: `h` drives all four case splits. -/
theorem senkStmt_assign_inv (c : PipeCfg) (L : Layout D)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (code : List Befehl)
    (h : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) =
      some code) :
    ∃ (k : Int) (A : Nat) (pv : List Befehl),
      constInt? i = some k ∧ L.loc t k f = some A ∧
      repOk (D.typ t f) A 8 0 = true ∧ senkWertT c e = some pv ∧
      code = pv ++ [Befehl.movImm64 c.adr (natAdresse A),
        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)] := by
  simp only [senkStmt] at h
  cases hk : constInt? i with
  | none => simp [hk] at h
  | some k =>
    simp only [hk] at h
    cases hA : L.loc t k f with
    | none => simp [hA] at h
    | some A =>
      simp only [hA] at h
      by_cases hr : repOk (D.typ t f) A 8 0 = true
      · rw [if_pos hr] at h
        cases hv : senkWertT c e with
        | none => simp [hv] at h
        | some pv =>
          rw [hv] at h
          simp only [Option.map_some, Option.some.injEq] at h
          exact ⟨k, A, pv, rfl, hA, hr, rfl, h.symm⟩
      · rw [if_neg hr] at h
        cases h

/-- JOINT WITNESS for `senkStmt_assign_inv`: every component holds
    jointly on the witness chunk -- constant index `0` at `8192`, an
    admitted slot, the deeply lowered value -- with the shared
    non-degenerate package (`PipePaket`: one table the contract
    writes, memory-changing source and fetched-byte runs). -/
theorem senkStmt_assign_inv_zeuge :
    ∃ (k : Int) (A : Nat) (pv code : List Befehl),
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0
          pwHw pwHL) = some code ∧
      constInt? pwIdx0 = some k ∧ pwL.loc () k () = some A ∧
      repOk (pwD.typ () ()) A 8 0 = true ∧
      senkWertT pwCfg pwWert0 = some pv ∧
      code = pv ++ [Befehl.movImm64 pwCfg.adr (natAdresse A),
        Befehl.store64 pwCfg.adr pwCfg.dst (BitVec.ofNat 32 0)] ∧
      PipePaket := by
  refine ⟨0, 8192, _, _, pwChunkWit, rfl, rfl, by decide, pwTief0, rfl,
    pipePaket_hold⟩

/-! ## 2. The per-chunk run, derived from the lowering alone.

    Lane 1195 takes the source step (`hsrc`) and the target chunk run
    (`hrun`) as premises. Both come out of the lowering here: the
    inversion fixes the constant index (so the source step is forced),
    `assignT_lauf` runs the chunk (the write permission comes from the
    admitted `WorldRep`), and `worldRep_store` carries the
    representation to the written world. -/

/-- CHUNK RUN, DERIVED: from an accepted chunk lowering, a checked
    configuration, a separated layout and a represented start state,
    the source `assignSlot` step AND the target `lauf` run over the
    canonically decoded chunk reach the written world, represented.
    Every premise is used: `hlow` feeds the inversion, `hc` the
    value/address run, `hsep` the store preservation, `hW` the slot
    permission and base representation, `hE` the environment. -/
theorem chunk_lauf_abgeleitet (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (p : List Befehl)
    (hlow : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) =
      some p)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (st : Zustand)
    (hW : WorldRep L st.speicher σ) (hE : EnvRepr ρ st.register (abbOf c)) :
    ∃ (σ' : World D) (st' : Zustand),
      execStmt O passes R
        (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) σ ρ =
        .ok σ' ρ ∧
      lauf (decodiertZu p) st = some st' ∧
      WorldRep L st'.speicher σ' ∧ EnvRepr ρ st'.register (abbOf c) := by
  obtain ⟨k, A, pv, hk, hloc, hok, hpv, hcode⟩ :=
    senkStmt_assign_inv c L t f i e hw hL p hlow
  obtain ⟨lo, hi, hT, hlo, hhi, -⟩ := repOk_int _ A hok
  obtain ⟨-, -, hwr, -⟩ := hW t k f A hloc
  let σL := σ.lese Λ (i.orte ++ e.orte)
  have hki : (eval σL i σL ρ).n = k := by
    have hsnd := constInt?_sound i σL σL ρ k hk
    simpa [intOf] using hsnd
  obtain ⟨st1, hrun1, hwmem, hE1⟩ :=
    assignT_lauf c hc e hT hlo hhi pv hpv A ρ σL σL st hE hwr
  have hsrc : execStmt O passes R
      (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) σ ρ =
      .ok (σL.schreibSlot t Λ k f (eval σL e σL ρ)) ρ := by
    rw [← hki]
    rfl
  have hW1 : WorldRep L st1.speicher
      (σL.schreibSlot t Λ k f (eval σL e σL ρ)) :=
    worldRep_store L hsep st.speicher st1.speicher σL t k f A hloc hW lo hi
      hT (eval σL e σL ρ) hwmem Λ
  have hrun : lauf (decodiertZu p) st = some st1 := by
    rw [decodiertZu_map_kanon, hcode]
    exact hrun1
  exact ⟨σL.schreibSlot t Λ k f (eval σL e σL ρ), st1, hsrc, hrun, hW1, hE1⟩

/-- The witness assignment: row `0` gets `x + 5`. -/
def witStmt1219 : Stmt pwD pwV false pwCtx [] [] :=
  Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0 pwHw pwHL

/-- JOINT WITNESS for `chunk_lauf_abgeleitet`: every premise holds
    jointly on the witness declaration -- one table its contract
    writes, the accepted chunk lowering, a separated layout, a
    represented start state -- and so do all four conclusions, with
    the shared non-degenerate package (`PipePaket`). -/
theorem chunk_lauf_abgeleitet_zeuge :
    ∃ (σ' : World pwD) (st' : Zustand),
      senkStmt pwCfg pwL witStmt1219 = some (pwProg.take 5) ∧
      execStmt pwO 0 pwR witStmt1219 pwSigma pwEnv30 = .ok σ' pwEnv30 ∧
      lauf (decodiertZu (pwProg.take 5)) (pwStart 30) = some st' ∧
      WorldRep pwL st'.speicher σ' ∧
      EnvRepr pwEnv30 st'.register (abbOf pwCfg) ∧
      PipePaket := by
  obtain ⟨σ', st', hsrc, hrun, hW', hE'⟩ :=
    chunk_lauf_abgeleitet pwCfg pwL pw_cfgOk pw_layoutSep () () pwIdx0
      pwWert0 pwHw pwHL _ pwChunkWit pwO 0 pwR pwSigma pwEnv30 (pwStart 30)
      pw_worldRep pw_envRepr30
  exact ⟨σ', st', pwChunkWit, hsrc, hrun, hW', hE', pipePaket_hold⟩

/-! ## 3. Coverage, derived from the lowering alone.

    Two forms. The generic one scales the admitted summary budget with
    the generated size (`length` instructions fit in `length * 6`), so
    deep values are safe. The budget-1 one reuses lane 1165's
    `deckung_pipeChunk` for shallow chunks. -/

/-- A lowered chunk is straight-line code: the value code plus address
    materialisation plus slot store. Only code equations, no syntax. -/
theorem chunkCode_gerade (pv code : List Befehl) (adr dst : Register)
    (A : Nat) (hval : pv.all gerade = true)
    (hcode : code = pv ++ [Befehl.movImm64 adr (natAdresse A),
      Befehl.store64 adr dst (BitVec.ofNat 32 0)]) :
    code.all gerade = true := by
  rw [hcode]
  simp [List.all_append, hval, gerade]

/-- GENERIC CHUNK COVERAGE: any instruction list is covered by the
    admitted pipeline summary over its own length as source budget.
    No lowering premise is needed: the bound is pure arithmetic over
    the admitted expansion (`pipeSummary_expand`) and the derived
    work bridge (`arbeit_decodiert`). -/
theorem deckung_chunk_generisch (p : List Befehl) :
    Deckung pipeSummary p.length (decodiertZu p) := by
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have hwork : targetWork ((decodiertZu p).map fun d => d.befehl) =
      p.length :=
    arbeit_decodiert p
  omega

/-- BUDGET-1 COVERAGE FOR SHALLOW CHUNKS: a chunk over a shallow
    value is covered at source budget 1, reusing lane 1165's
    `deckung_pipeChunk`. Every premise feeds it directly. -/
theorem chunk_deckung_eins_abgeleitet (c : PipeCfg) (L : Layout D)
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (p chunk : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (hchunk : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk) :
    Deckung pipeSummary 1 (decodiertZu chunk) :=
  deckung_pipeChunk c L l t f i e hT hw hL 1 p chunk hflach hchunk
    (Nat.le_refl 1)

/-- JOINT WITNESS for `chunk_deckung_eins_abgeleitet`: the shallow
    witness chunk is covered at budget 1, with the shared
    non-degenerate package (`PipePaket`). -/
theorem chunk_deckung_eins_abgeleitet_zeuge :
    ∃ (chunk : List Befehl),
      senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      Deckung pipeSummary 1 (decodiertZu chunk) ∧
      PipePaket := by
  refine ⟨_, pwChunkCast, ?_, pipePaket_hold⟩
  exact chunk_deckung_eins_abgeleitet pwCfg pwL () () pwIdx0 pwWert0 pwHT0
    pwHw pwHL _ _ pw_senkWert0 pwChunkCast

/-! ## 4. N-chunk chains: lowering, runs and coverage by induction.

    An `assignSlot` preserves the resource list (`Stmt ... Λ Λ`), so a
    list of chunks is a well-typed dependent `Block` at ANY length --
    past lane 1195's two conses. The per-chunk lowering
    (`chunksAusListe`) refuses as soon as one chunk refuses; the block
    lowering (`senkBlock`) is its flattening. -/

/-- The statement of one chunk. -/
def chunkStmt (a : AssignChunk D V l Γ Λ) : Stmt D V l Γ Λ Λ :=
  .assignSlot a.t a.f a.i a.e a.hw a.hL

/-- The dependent source block of a chunk list. -/
def blockAusChunks : List (AssignChunk D V l Γ Λ) → Block D V l Γ Λ Λ
  | [] => .nil
  | a :: rest => .cons (chunkStmt a) (blockAusChunks rest)

/-- The per-chunk lowering: each chunk through `senkStmt`. -/
def chunksAusListe (c : PipeCfg) (L : Layout D) :
    List (AssignChunk D V l Γ Λ) → Option (List (List Befehl))
  | [] => some []
  | a :: rest =>
    match senkStmt c L (chunkStmt a) with
    | some p => (chunksAusListe c L rest).map (p :: ·)
    | none => none

/-- The block lowering of one chunk statement is the chunk equation. -/
theorem senkBlock_chunkStmt (c : PipeCfg) (L : Layout D)
    (a : AssignChunk D V l Γ Λ) {Λ'' : List (Res D)}
    (rest : Block D V l Γ Λ Λ'') (pos : Nat) :
    senkBlock c L pos (.cons (chunkStmt a) rest) =
      match senkStmt c L (chunkStmt a) with
      | some p => (senkBlock c L (pos + (encodeAll p).length) rest).map (p ++ ·)
      | none => none :=
  senkBlock_assign c L a.t a.f a.i a.e a.hw a.hL rest pos

/-- BLOCK LOWERING BY INDUCTION: the lowered block is the flattened
    chunk list. Every premise is used: `h` drives the case splits and
    feeds the induction. -/
theorem senkBlock_blockAusChunks (c : PipeCfg) (L : Layout D) (pos : Nat)
    (as : List (AssignChunk D V l Γ Λ)) (chunks : List (List Befehl))
    (h : chunksAusListe c L as = some chunks) :
    senkBlock c L pos (blockAusChunks as) = some chunks.flatten := by
  induction as generalizing pos chunks with
  | nil =>
    simp only [chunksAusListe, Option.some.injEq] at h
    subst h
    rfl
  | cons a rest ih =>
    simp only [chunksAusListe] at h
    cases hs : senkStmt c L (chunkStmt a) with
    | none => simp [hs] at h
    | some p =>
      simp only [hs] at h
      cases hq : chunksAusListe c L rest with
      | none => simp [hq] at h
      | some chunksRest =>
        simp only [hq, Option.map_some, Option.some.injEq] at h
        subst h
        have ihrest := ih (pos + (encodeAll p).length) chunksRest hq
        simp only [blockAusChunks]
        rw [senkBlock_chunkStmt, hs]
        simp only
        rw [ihrest]
        rfl

/-- N-CHUNK RUN, DERIVED: from the per-chunk lowering, a checked
    configuration, a separated layout and a represented start state,
    the source `execBlock` over the whole chain AND the target run
    chain over the chunks reach the final written world, represented.
    The induction threads representation through
    `chunk_lauf_abgeleitet`; the source side composes through the real
    `execBlock_cons_stmtOk`. Every premise is used. -/
theorem ketteLauf_blockAusChunks (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    (as : List (AssignChunk D V l Γ Λ)) (chunks : List (List Befehl))
    (hchunks : chunksAusListe c L as = some chunks)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (st : Zustand)
    (hW : WorldRep L st.speicher σ) (hE : EnvRepr ρ st.register (abbOf c)) :
    ∃ (σ' : World D) (st' : Zustand),
      execBlock O passes R (blockAusChunks as) σ ρ = .ok σ' ρ ∧
      KetteLauf chunks st st' ∧
      WorldRep L st'.speicher σ' ∧ EnvRepr ρ st'.register (abbOf c) := by
  induction as generalizing σ st chunks with
  | nil =>
    simp only [chunksAusListe, Option.some.injEq] at hchunks
    subst hchunks
    exact ⟨σ, st, rfl, .nil st, hW, hE⟩
  | cons a rest ih =>
    simp only [chunksAusListe] at hchunks
    cases hs : senkStmt c L (chunkStmt a) with
    | none => simp [hs] at hchunks
    | some p =>
      simp only [hs] at hchunks
      cases hq : chunksAusListe c L rest with
      | none => simp [hq] at hchunks
      | some chunksRest =>
        simp only [hq, Option.map_some, Option.some.injEq] at hchunks
        subst hchunks
        obtain ⟨σ1, st1, hsrc1, hrun1, hW1, hE1⟩ :=
          chunk_lauf_abgeleitet c L hc hsep a.t a.f a.i a.e a.hw a.hL p hs
            O passes R σ ρ st hW hE
        obtain ⟨σ2, st2, hsrcRest, hrunRest, hW2, hE2⟩ :=
          ih chunksRest hq σ1 st1 hW1 hE1
        have hsrc : execBlock O passes R (blockAusChunks (a :: rest)) σ ρ =
            .ok σ2 ρ := by
          simp only [blockAusChunks]
          rw [execBlock_cons_stmtOk O passes R (chunkStmt a) _ σ ρ σ1 ρ hsrc1]
          exact hsrcRest
        exact ⟨σ2, st2, hsrc,
          KetteLauf.cons p chunksRest st st1 st2 hrun1 hrunRest, hW2, hE2⟩

/-- N-CHUNK COVERAGE, DERIVED: the flattened chunks are covered by
    the admitted pipeline summary over the summed generated lengths.
    Generic per-chunk budgets (`deckung_chunk_generisch`) append
    through `deckung_append_pipe`. Every premise is used. -/
theorem deckung_blockAusChunks (c : PipeCfg) (L : Layout D)
    (as : List (AssignChunk D V l Γ Λ)) (chunks : List (List Befehl))
    (h : chunksAusListe c L as = some chunks) :
    Deckung pipeSummary (chunks.map List.length).sum
      (decodiertZu chunks.flatten) := by
  induction as generalizing chunks with
  | nil =>
    simp only [chunksAusListe, Option.some.injEq] at h
    subst h
    simp only [List.map_nil, List.sum_nil, List.flatten_nil, decodiertZu,
      List.map_nil]
    exact deckung_leer pipeSummary 0 (by simp [pipeSummary_expand])
  | cons a rest ih =>
    simp only [chunksAusListe] at h
    cases hs : senkStmt c L (chunkStmt a) with
    | none => simp [hs] at h
    | some p =>
      simp only [hs] at h
      cases hq : chunksAusListe c L rest with
      | none => simp [hq] at h
      | some chunksRest =>
        simp only [hq, Option.map_some, Option.some.injEq] at h
        subst h
        have hdeckRest := ih _ hq
        simp only [List.map_cons, List.sum_cons, List.flatten_cons]
        rw [decodiertZu_append]
        exact deckung_append_pipe p.length (chunksRest.map List.length).sum
          _ _ (deckung_chunk_generisch p) hdeckRest

/-- N-CHUNK STRAIGHT-LINE: every lowered chunk list flattens to
    straight-line code, so the byte-fetch bridge (`lauf_zu_laufBytes`)
    applies. Every premise is used. -/
theorem chunks_flatten_gerade (c : PipeCfg) (L : Layout D)
    (as : List (AssignChunk D V l Γ Λ)) (chunks : List (List Befehl))
    (h : chunksAusListe c L as = some chunks) :
    chunks.flatten.all gerade = true := by
  induction as generalizing chunks with
  | nil =>
    simp only [chunksAusListe, Option.some.injEq] at h
    subst h
    rfl
  | cons a rest ih =>
    simp only [chunksAusListe] at h
    cases hs : senkStmt c L (chunkStmt a) with
    | none => simp [hs] at h
    | some p =>
      simp only [hs] at h
      cases hq : chunksAusListe c L rest with
      | none => simp [hq] at h
      | some chunksRest =>
        simp only [hq, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨k, A, pv, -, -, hok, hpv, hcode⟩ :=
          senkStmt_assign_inv c L a.t a.f a.i a.e a.hw a.hL p hs
        have hg : p.all gerade = true :=
          chunkCode_gerade pv p c.adr c.dst A (senkWertT_gerade c a.e pv hpv)
            hcode
        simp [List.flatten_cons, List.all_append, hg, ih _ hq]

/-- The witness chunk: row `0` gets `x + 5`. -/
def witChunk1219 : AssignChunk pwD pwV false pwCtx [] :=
  { t := (), f := (), i := pwIdx0, e := pwWert0, hw := pwHw, hL := pwHL }

/-- Three witness chunks lower to three copies of the five-instruction
    chunk, by computation. -/
theorem chunksAusListe_drei1219 :
    chunksAusListe pwCfg pwL [witChunk1219, witChunk1219, witChunk1219] =
      some [pwProg.take 5, pwProg.take 5, pwProg.take 5] := rfl

/-- JOINT WITNESS for `senkBlock_blockAusChunks`: the three-chunk
    lowering is the flattened triple, with the shared non-degenerate
    package (`PipePaket`). -/
theorem senkBlock_blockAusChunks_zeuge :
    ∃ (prog : List Befehl),
      chunksAusListe pwCfg pwL [witChunk1219, witChunk1219, witChunk1219] =
        some [pwProg.take 5, pwProg.take 5, pwProg.take 5] ∧
      senkBlock pwCfg pwL 0
        (blockAusChunks [witChunk1219, witChunk1219, witChunk1219]) =
        some prog ∧
      prog = [pwProg.take 5, pwProg.take 5, pwProg.take 5].flatten ∧
      PipePaket := by
  refine ⟨_, chunksAusListe_drei1219, ?_, rfl, pipePaket_hold⟩
  exact senkBlock_blockAusChunks pwCfg pwL 0 _ _ chunksAusListe_drei1219

/-- JOINT WITNESS for `ketteLauf_blockAusChunks`: source run, target
    run chain and preserved representation over three witness chunks,
    with the shared non-degenerate package (`PipePaket`). -/
theorem ketteLauf_blockAusChunks_zeuge :
    ∃ (σ' : World pwD) (st' : Zustand),
      execBlock pwO 0 pwR
        (blockAusChunks [witChunk1219, witChunk1219, witChunk1219])
        pwSigma pwEnv30 = .ok σ' pwEnv30 ∧
      KetteLauf [pwProg.take 5, pwProg.take 5, pwProg.take 5]
        (pwStart 30) st' ∧
      WorldRep pwL st'.speicher σ' ∧
      EnvRepr pwEnv30 st'.register (abbOf pwCfg) ∧
      PipePaket := by
  obtain ⟨σ', st', hsrc, hrun, hW', hE'⟩ :=
    ketteLauf_blockAusChunks pwCfg pwL pw_cfgOk pw_layoutSep _ _
      chunksAusListe_drei1219 pwO 0 pwR pwSigma pwEnv30 (pwStart 30)
      pw_worldRep pw_envRepr30
  exact ⟨σ', st', hsrc, hrun, hW', hE', pipePaket_hold⟩

/-- JOINT WITNESS for `deckung_blockAusChunks`: the triple is covered
    at the summed generated length, with the shared non-degenerate
    package (`PipePaket`). -/
theorem deckung_blockAusChunks_zeuge :
    ∃ (chunks : List (List Befehl)),
      chunksAusListe pwCfg pwL [witChunk1219, witChunk1219, witChunk1219] =
        some chunks ∧
      Deckung pipeSummary (chunks.map List.length).sum
        (decodiertZu chunks.flatten) ∧
      PipePaket := by
  refine ⟨_, chunksAusListe_drei1219, ?_, pipePaket_hold⟩
  exact deckung_blockAusChunks pwCfg pwL _ _ chunksAusListe_drei1219

/-- JOINT WITNESS for `chunks_flatten_gerade`: the triple flattens to
    straight-line code, with the shared non-degenerate package
    (`PipePaket`). -/
theorem chunks_flatten_gerade_zeuge :
    ∃ (chunks : List (List Befehl)),
      chunksAusListe pwCfg pwL [witChunk1219, witChunk1219, witChunk1219] =
        some chunks ∧
      chunks.flatten.all gerade = true ∧
      PipePaket := by
  refine ⟨_, chunksAusListe_drei1219, ?_, pipePaket_hold⟩
  exact chunks_flatten_gerade pwCfg pwL _ _ chunksAusListe_drei1219

/-! ## 5. Closing: source run, target run, coverage, work.

    Everything below composes derived legs: the source run and run
    chain (`ketteLauf_blockAusChunks`), the flattened target run
    (`ketteLauf_lauf`), coverage (`deckung_blockAusChunks`), work
    (`ketteLaenge_sum`) and the lowering equation
    (`senkBlock_blockAusChunks`). Named hardware timing stays out --
    it is a hardware assumption, never a software proof. -/

/-- CLOSING (`lauf` level): over an n-chunk chain the source
    `execBlock` run, the target `lauf` run over the flattened chunks,
    coverage at the summed generated length, the work sum and the
    lowering equation all hold -- every leg derived from the lowering
    alone except the admitted representation. -/
theorem pipelineChunkDerive_schluss (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    (as : List (AssignChunk D V l Γ Λ)) (chunks : List (List Befehl))
    (hchunks : chunksAusListe c L as = some chunks)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (st : Zustand)
    (hW : WorldRep L st.speicher σ) (hE : EnvRepr ρ st.register (abbOf c)) :
    ∃ (σ' : World D) (st' : Zustand),
      execBlock O passes R (blockAusChunks as) σ ρ = .ok σ' ρ ∧
      lauf (decodiertZu chunks.flatten) st = some st' ∧
      Deckung pipeSummary (chunks.map List.length).sum
        (decodiertZu chunks.flatten) ∧
      targetWork chunks.flatten = (chunks.map targetWork).sum ∧
      senkBlock c L 0 (blockAusChunks as) = some chunks.flatten ∧
      WorldRep L st'.speicher σ' ∧ EnvRepr ρ st'.register (abbOf c) := by
  obtain ⟨σ', st', hsrc, hrun, hW', hE'⟩ :=
    ketteLauf_blockAusChunks c L hc hsep as chunks hchunks O passes R σ ρ
      st hW hE
  exact ⟨σ', st', hsrc, ketteLauf_lauf chunks st st' hrun,
    deckung_blockAusChunks c L as chunks hchunks, ketteLaenge_sum chunks,
    senkBlock_blockAusChunks c L 0 as chunks hchunks, hW', hE'⟩

/-- JOINT WITNESS for `pipelineChunkDerive_schluss`: the whole
    conjunction over three witness chunks, with the shared
    non-degenerate package (`PipePaket`). -/
theorem pipelineChunkDerive_schluss_zeuge :
    ∃ (σ' : World pwD) (st' : Zustand),
      chunksAusListe pwCfg pwL [witChunk1219, witChunk1219, witChunk1219] =
        some [pwProg.take 5, pwProg.take 5, pwProg.take 5] ∧
      execBlock pwO 0 pwR
        (blockAusChunks [witChunk1219, witChunk1219, witChunk1219])
        pwSigma pwEnv30 = .ok σ' pwEnv30 ∧
      lauf (decodiertZu [pwProg.take 5, pwProg.take 5, pwProg.take 5].flatten)
        (pwStart 30) = some st' ∧
      Deckung pipeSummary
        ([pwProg.take 5, pwProg.take 5, pwProg.take 5].map List.length).sum
        (decodiertZu
          [pwProg.take 5, pwProg.take 5, pwProg.take 5].flatten) ∧
      targetWork [pwProg.take 5, pwProg.take 5, pwProg.take 5].flatten =
        ([pwProg.take 5, pwProg.take 5, pwProg.take 5].map
          targetWork).sum ∧
      senkBlock pwCfg pwL 0
        (blockAusChunks [witChunk1219, witChunk1219, witChunk1219]) =
        some [pwProg.take 5, pwProg.take 5, pwProg.take 5].flatten ∧
      WorldRep pwL st'.speicher σ' ∧
      EnvRepr pwEnv30 st'.register (abbOf pwCfg) ∧
      PipePaket := by
  obtain ⟨σ', st', hsrc, hrun, hdeck, hwork, hlow, hW', hE'⟩ :=
    pipelineChunkDerive_schluss pwCfg pwL pw_cfgOk pw_layoutSep _ _
      chunksAusListe_drei1219 pwO 0 pwR pwSigma pwEnv30 (pwStart 30)
      pw_worldRep pw_envRepr30
  exact ⟨σ', st', chunksAusListe_drei1219, hsrc, hrun, hdeck, hwork, hlow,
    hW', hE', pipePaket_hold⟩

/-- CLOSING (byte level, in the style of `pipeline_correct`): the
    derived run chain over straight-line chunks is the fetched-byte
    run on the loaded image. The code region, its split and the entry
    pointer are named admitted premises (witnessed); the straight-line
    shape is derived from the lowering. Every premise is used. -/
theorem pipelineChunkDerive_bytes (c : PipeCfg) (L : Layout D)
    (as : List (AssignChunk D V l Γ Λ)) (chunks : List (List Befehl))
    (hchunks : chunksAusListe c L as = some chunks)
    (cs : Adresse) (flat pre post : List Byte) (st st' : Zustand)
    (hcode : CodeAt st.speicher cs flat)
    (hf : flat = pre ++ encodeAll chunks.flatten ++ post)
    (hrip : st.rip = addrOff cs pre.length)
    (hrun : KetteLauf chunks st st') :
    laufBytes chunks.flatten.length st = .weiter st' ∧
    st'.rip = addrOff cs (pre.length + (encodeAll chunks.flatten).length) ∧
    CodeAt st'.speicher cs flat ∧
    st'.speicher.lesbar = st.speicher.lesbar ∧
    st'.speicher.schreibbar = st.speicher.schreibbar := by
  have hall := chunks_flatten_gerade c L as chunks hchunks
  have hlauf : lauf (chunks.flatten.map kanon) st = some st' := by
    have hkl := ketteLauf_lauf chunks st st' hrun
    rwa [decodiertZu_map_kanon] at hkl
  obtain ⟨hb, hr, hc, hl, hs⟩ :=
    lauf_zu_laufBytes cs flat chunks.flatten pre post st st' hall hlauf
      hcode hf hrip
  exact ⟨hb, hr, hc, hl, hs⟩

/-- JOINT WITNESS for `pipelineChunkDerive_bytes`: one witness
    chunk is the prefix of the accepted candidate bytes
    (`pwBytes = chunk ++ rest`), so the fetched-byte run over the
    five-instruction chunk reaches into the loaded image with the code
    region intact -- with the shared non-degenerate package
    (`PipePaket`). -/
theorem pipelineChunkDerive_bytes_zeuge :
    ∃ (st' : Zustand),
      chunksAusListe pwCfg pwL [witChunk1219] =
        some [pwProg.take 5] ∧
      CodeAt (pwStart 30).speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      pwBytes = [] ++ encodeAll [pwProg.take 5].flatten ++
        encodeAll (pwProg.drop 5) ∧
      (pwStart 30).rip =
        addrOff (natAdresse pwCfg.codeBase) ([] : List Byte).length ∧
      KetteLauf [pwProg.take 5] (pwStart 30) st' ∧
      laufBytes [pwProg.take 5].flatten.length (pwStart 30) =
        .weiter st' ∧
      st'.rip = addrOff (natAdresse pwCfg.codeBase)
        (([] : List Byte).length +
          (encodeAll [pwProg.take 5].flatten).length) ∧
      CodeAt st'.speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      st'.speicher.lesbar = (pwStart 30).speicher.lesbar ∧
      st'.speicher.schreibbar = (pwStart 30).speicher.schreibbar ∧
      PipePaket := by
  have hch1 : chunksAusListe pwCfg pwL [witChunk1219] =
      some [pwProg.take 5] := rfl
  obtain ⟨σ1, st1, -, hrun1, -, -⟩ :=
    chunk_lauf_abgeleitet pwCfg pwL pw_cfgOk pw_layoutSep () () pwIdx0
      pwWert0 pwHw pwHL _ pwChunkWit pwO 0 pwR pwSigma pwEnv30 (pwStart 30)
      pw_worldRep pw_envRepr30
  have hrun : KetteLauf [pwProg.take 5] (pwStart 30) st1 :=
    KetteLauf.cons _ _ _ _ st1 hrun1 (.nil st1)
  have hcode : CodeAt (pwStart 30).speicher (natAdresse pwCfg.codeBase)
      pwBytes :=
    pw_code
  have hf : pwBytes = [] ++ encodeAll [pwProg.take 5].flatten ++
      encodeAll (pwProg.drop 5) := by
    have htake : pwProg.take 5 ++ pwProg.drop 5 = pwProg :=
      List.take_append_drop 5 pwProg
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
      List.nil_append]
    rw [← encodeAll_append, htake]
    rfl
  have hrip : (pwStart 30).rip =
      addrOff (natAdresse pwCfg.codeBase) ([] : List Byte).length := by
    show natAdresse 4096 = addrOff (natAdresse 4096) 0
    exact (addrOff_null _).symm
  obtain ⟨hb, hr, hc, hl, hs⟩ :=
    pipelineChunkDerive_bytes pwCfg pwL [witChunk1219] [pwProg.take 5] hch1
      (natAdresse pwCfg.codeBase) pwBytes [] (encodeAll (pwProg.drop 5))
      (pwStart 30) st1 hcode hf hrip hrun
  exact ⟨st1, hch1, hcode, hf, hrip, hrun, hb, hr, hc, hl, hs,
    pipePaket_hold⟩

/-! ## 6. The validator, refusals and poison probes.

    The validator recomputes the chunk list from the source chunks and
    accepts the candidate bytes only if they ARE its encoding
    (`chunksValidate_sound`). Unsupported shapes are refused, never
    guessed: branches (`ite`), deep values past the scratch registers,
    and every candidate for an unlowerable list. -/

/-- The validator: recompute the chunk list and accept the candidate
    bytes only if they are its encoding. -/
def chunksValidate (c : PipeCfg) (L : Layout D)
    (as : List (AssignChunk D V l Γ Λ)) (bytes : List Byte) : Bool :=
  match chunksAusListe c L as with
  | some chunks => decide (bytes = encodeAll chunks.flatten)
  | none => false

/-- VALIDATOR SOUNDNESS: an accepted candidate is the Lean
    recomputation. Every premise is used: `h` drives the split and
    yields both conjuncts. -/
theorem chunksValidate_sound (c : PipeCfg) (L : Layout D)
    (as : List (AssignChunk D V l Γ Λ)) (bytes : List Byte)
    (h : chunksValidate c L as bytes = true) :
    ∃ chunks, chunksAusListe c L as = some chunks ∧
      bytes = encodeAll chunks.flatten := by
  unfold chunksValidate at h
  cases hc : chunksAusListe c L as with
  | none => simp [hc] at h
  | some chunks =>
    simp only [hc] at h
    simp only [decide_eq_true_eq] at h
    exact ⟨chunks, rfl, h⟩

/-- Witness for `chunksValidate_sound`: the single witness chunk
    validates its own encoding, with the shared non-degenerate
    package (`PipePaket`). -/
theorem chunksValidate_sound_zeuge :
    ∃ (chunks : List (List Befehl)),
      chunksAusListe pwCfg pwL [witChunk1219] = some chunks ∧
      chunksValidate pwCfg pwL [witChunk1219]
        (encodeAll chunks.flatten) = true ∧
      PipePaket := by
  have hch1 : chunksAusListe pwCfg pwL [witChunk1219] =
      some [pwProg.take 5] := rfl
  refine ⟨_, hch1, ?_, pipePaket_hold⟩
  decide

/-- REFUSAL (branch): an `ite` statement has no chunk lowering -- it
    matches the catch-all, never a guessed sequence. -/
theorem chunkDerive_verweigert_ite (c : PipeCfg) (L : Layout D)
    {Λ' : List (Res D)}
    (cnd : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ') :
    senkStmt c L (Stmt.ite (V := V) (l := l) cnd t e) = none :=
  rfl

/-- JOINT WITNESS for the branch refusal, firing on the witness check
    with the shared non-degenerate package (`PipePaket`). -/
theorem chunkDerive_verweigert_ite_zeuge :
    ∃ (cnd : Expr pwD pwCtx [] .bool)
      (t e : Block pwD pwV false pwCtx [] []),
      senkStmt pwCfg pwL (Stmt.ite (V := pwV) (l := false) cnd t e) =
        none ∧ PipePaket := by
  refine ⟨pwCheck, Block.nil, Block.nil, ?_, pipePaket_hold⟩
  exact chunkDerive_verweigert_ite _ _ _ _ _

/-- Poison probe: the witness `ite` has no chunk lowering. -/
theorem gift1219_ite :
    senkStmt pwCfg pwL
      (Stmt.ite (V := pwV) (l := false) pwCheck
        (Block.nil : Block pwD pwV false pwCtx [] [])
        (Block.nil : Block pwD pwV false pwCtx [] [])) = none :=
  rfl

/-- The deep-value chunk: admitted slot, but no lowering past `tmp`. -/
def deepChunk1219 : AssignChunk pwD pwV false pwCtx [] :=
  { t := (), f := (), i := pwIdx0, e := tiefWertFeld1195, hw := pwHw,
    hL := pwHL }

/-- REFUSAL (deep value at list level): the deep chunk has no
    per-chunk lowering -- refused, not guessed. -/
theorem chunksAusListe_verweigert_tief :
    chunksAusListe pwCfg pwL [deepChunk1219] = none := by
  have hs : senkStmt pwCfg pwL (chunkStmt deepChunk1219) = none :=
    block_verweigert_tief_stmt
  simp [chunksAusListe, hs]

/-- Poison probe: the deep chunk list has no lowering. -/
theorem gift1219_tief :
    chunksAusListe pwCfg pwL [deepChunk1219] = none :=
  chunksAusListe_verweigert_tief

/-- REFUSAL (validator): the validator rejects every candidate for an
    unlowerable chunk list. -/
theorem chunksValidate_verweigert_tief (bytes : List Byte) :
    chunksValidate pwCfg pwL [deepChunk1219] bytes = false := by
  have hs : chunksAusListe pwCfg pwL [deepChunk1219] = none :=
    chunksAusListe_verweigert_tief
  unfold chunksValidate
  rw [hs]

/-- Poison probe: the validator rejects the empty candidate for the
    deep chunk list. -/
theorem gift1219_validate :
    chunksValidate pwCfg pwL [deepChunk1219] [] = false :=
  chunksValidate_verweigert_tief []

/- CUTS:
   - Proved here (generic): the canonical-decode bridge
     (`decodiertZu_map_kanon`); the single-chunk lowering inversion
     (`senkStmt_assign_inv`); the derived per-chunk run
     (`chunk_lauf_abgeleitet`: source step AND target run from the
     lowering plus the admitted layout/representation);
     straight-line chunk code (`chunkCode_gerade`); generic chunk
     coverage at generated length (`deckung_chunk_generisch`,
     deep-safe) and budget-1 coverage for shallow chunks
     (`chunk_deckung_eins_abgeleitet`, via 1165); n-chunk lowering
     (`senkBlock_chunkStmt`, `senkBlock_blockAusChunks`), n-chunk
     runs (`ketteLauf_blockAusChunks`), n-chunk coverage
     (`deckung_blockAusChunks`) and n-chunk straight-line shape
     (`chunks_flatten_gerade`), all by induction over the chunk list;
     the `lauf`-level closing (`pipelineChunkDerive_schluss`) and the
     byte-level closing (`pipelineChunkDerive_bytes`, via the accepted
     `ketteLauf_lauf` and `lauf_zu_laufBytes`); the validator and its
     soundness (`chunksValidate`, `chunksValidate_sound`); three
     refusals (branch `ite`, deep value at list level, validator over
     an unlowerable list) with three firing poison probes; joint
     non-degenerate witnesses for every syntax-premise theorem (one
     table its contract writes; reached source steps; target chunk
     runs; fetched-byte run observably changing memory via the reused
     `PipePaket`).
   - Reused, not duplicated: `senkStmt`, `senkWertT`,
     `senkWertT_gerade`, `senkBedT`-free (no checks in this fragment),
     `assignT_lauf`, `worldRep_store`, `repOk_int`,
     `constInt?_sound`, `execBlock_cons_stmtOk`, `senkBlock_assign`,
     `decodiertZu`/`decodiertZu_append`/`arbeit_decodiert`,
     `pipeSummary`/`pipeSummary_expand`/`deckung_pipeChunk`,
     `deckung_append_pipe`, `deckung_leer`,
     `budgetAusfuehrung_transfer`-free (no time claim here),
     `ketteLauf_lauf`, `ketteLaenge_sum`, `lauf_zu_laufBytes`,
     `validate`-free (own smaller validator), and the whole `pw`
     witness package with its chunk/cost facts.
   - OPEN (named timing): no `laufKosten`/`schrittKosten` aggregation
     and no time-transfer bound is claimed here; per-step hardware
     bounds stay hardware assumptions and compose through
     `BudgetExecution` (1195's `block_zwei_korrekt` shows the shape).
   - OPEN (fragment): only `assignSlot` chains lower here; `ite`
     branches, checks (`pruefung`), loops, calls, binds, globals,
     pointer and register statements are refused (`none`), never
     guessed. Deep values past the scratch registers are refused.
   - OPEN (machine): single core, model memory, no TSO/concurrency
     claim (inherited from `Pipeline.lean`'s own CUTS); entry/image/
     ABI mapping composes through `PipelineImage`/`PipelineEntry`;
     no optimiser certificates are taken (direct lowering, composes
     with `optimise_sound` upstream).
   - No second IR, no second interpreter, no optimiser edit, no
     weakened guarantee: unsupported shapes are refused, never
     guessed.
-/

#print axioms decodiertZu_map_kanon
#print axioms senkStmt_assign_inv
#print axioms senkStmt_assign_inv_zeuge
#print axioms chunk_lauf_abgeleitet
#print axioms witStmt1219
#print axioms chunk_lauf_abgeleitet_zeuge
#print axioms chunkCode_gerade
#print axioms deckung_chunk_generisch
#print axioms chunk_deckung_eins_abgeleitet
#print axioms chunk_deckung_eins_abgeleitet_zeuge
#print axioms chunkStmt
#print axioms blockAusChunks
#print axioms chunksAusListe
#print axioms senkBlock_chunkStmt
#print axioms senkBlock_blockAusChunks
#print axioms ketteLauf_blockAusChunks
#print axioms deckung_blockAusChunks
#print axioms chunks_flatten_gerade
#print axioms witChunk1219
#print axioms chunksAusListe_drei1219
#print axioms senkBlock_blockAusChunks_zeuge
#print axioms ketteLauf_blockAusChunks_zeuge
#print axioms deckung_blockAusChunks_zeuge
#print axioms chunks_flatten_gerade_zeuge
#print axioms pipelineChunkDerive_schluss
#print axioms pipelineChunkDerive_schluss_zeuge
#print axioms pipelineChunkDerive_bytes
#print axioms pipelineChunkDerive_bytes_zeuge
#print axioms chunksValidate
#print axioms chunksValidate_sound
#print axioms chunksValidate_sound_zeuge
#print axioms chunkDerive_verweigert_ite
#print axioms chunkDerive_verweigert_ite_zeuge
#print axioms gift1219_ite
#print axioms deepChunk1219
#print axioms chunksAusListe_verweigert_tief
#print axioms gift1219_tief
#print axioms chunksValidate_verweigert_tief
#print axioms gift1219_validate

end Gabbro.Grammatik.X86.PipeChunkDerive
