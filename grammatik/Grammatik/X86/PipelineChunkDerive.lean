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
import Grammatik.X86.PipelineBlockInduct

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

/- CUTS:
   - Skeleton green: `AssignChunk` (assignSlot-only chains, no case split).
   - OPEN: everything in the task (derived runs, coverage, n-chunk
     induction, closing theorem, refusals, witnesses).
-/

end Gabbro.Grammatik.X86.PipeChunkDerive
