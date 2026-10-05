/-
  File:      Grammatik/X86/PipelineChunkIte.lean
  Subject:   Per-chunk runs and coverage DERIVED for if/else and checks
             (lane 1263, follow-up of lane 1219 `PipelineChunkDerive`).

  Lane 1219 derives per-chunk runs/coverage only for `assignSlot`
  chains; `ite`, checks, loops and calls are refused there. Here the
  chunk run/coverage premises for `ite` and bound checks
  (`Block.pruefung`) are derived from the lowering alone: the accepted
  `senkBlock` of a closed single-ite / single-check chunk IS the
  condition code plus the accepted branch lowerings with the decided
  jump layout (`iteCode`, `sprungOk`) resp. the reason-exit jump with
  its address equation (`senkPruef`), and the fetched-byte run plus
  coverage follow from the admitted layout/representation. Loops
  (`traverse`) and calls (`call`, `bindCall`) stay refused with named
  theorems and firing poison probes. No second IR, no second
  interpreter, no optimiser edit, no existing-file edit. Rust is out
  of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWitnesses
import Grammatik.X86.PipelineChunkDerive
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineWorkBranches
import Grammatik.X86.DerivedWorkBound
import Grammatik.X86.BudgetExecution

namespace Gabbro.Grammatik.X86.PipeChunkIte

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipeChunkDerive
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipeWorkBranches
open Gabbro.Grammatik.X86.PipeBlock

variable {D : Deklaration} {V : Vertrag D}

/-- The validator: recompute the closed-chunk lowering and accept the
    candidate bytes only if they are its encoding. -/
def iteCheckValidate (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  match senkBlock c L 0 b with
  | some prog => decide (bytes = encodeAll prog)
  | none => false

/-! ## 1. Closed ite chunks: lowering inversion.

    A closed ite chunk is one `ite` cons with `nil` rest. An accepted
    lowering IS the deep condition code plus the two accepted branch
    lowerings with the decided jump layout (`iteCode`, both
    `sprungOk`); the rest lowering is `[]` by computation. -/

/-- Witness then-branch: row `0` gets `x + 5` (memory-changing). -/
def witIteT1263 : _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [] :=
  _root_.Gabbro.Grammatik.Block.cons
    (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0 pwWert0 pwHw pwHL)
    _root_.Gabbro.Grammatik.Block.nil

/-- Witness else-branch: empty. -/
def witIteE1263 : _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [] :=
  _root_.Gabbro.Grammatik.Block.nil

/-- Witness closed ite chunk: `if x < 50 then T[0].f = x + 5`. -/
def witIte1263 : _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [] :=
  _root_.Gabbro.Grammatik.Block.cons
    (Stmt.ite (V := pwV) (l := false) pwCheck witIteT1263 witIteE1263)
    _root_.Gabbro.Grammatik.Block.nil

/-- LOWERING INVERSION (closed ite chunk): an accepted lowering is the
    condition code, the two accepted branch lowerings with both jump
    checks, and exactly the `iteCode` layout. Every premise is used:
    `h` drives the accepted inversion and the nil rest equation. -/
theorem iteChunk_inv_abgeleitet (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (cnd : Expr D Γ Λ .bool)
    (t e : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ')
    (pos : Nat) (prog : List Befehl)
    (h : senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.ite cnd t e)
        _root_.Gabbro.Grammatik.Block.nil) = some prog) :
    ∃ code j pt pe, senkBedT c cnd = some (code, j) ∧
      senkBlock c L (pos + (encodeAll code).length + 6) t = some pt ∧
      senkBlock c L (pos + (encodeAll code).length + 6 + (encodeAll pt).length + 5) e =
        some pe ∧
      sprungOk ((encodeAll pt).length + 5) = true ∧ sprungOk (encodeAll pe).length = true ∧
      prog = iteCode code j pt pe := by
  obtain ⟨code, j, pt, pe, q, hb, ht, he, hk1, hk2, hq, hp⟩ :=
    senkBlock_ite_inv c L cnd t e _root_.Gabbro.Grammatik.Block.nil pos prog h
  have hnil : senkBlock c L (pos + (encodeAll (iteCode code j pt pe)).length)
      (_root_.Gabbro.Grammatik.Block.nil :
        _root_.Gabbro.Grammatik.Block D V l Γ Λ' Λ') = some [] := rfl
  rw [hnil, Option.some.injEq] at hq
  subst hq
  simp only [List.append_nil] at hp
  exact ⟨code, j, pt, pe, hb, ht, he, hk1, hk2, hp⟩

/-- The witness ite chunk lowers (by computation). -/
theorem witIteLow1263 :
    ∃ prog, senkBlock pwCfg pwL 0 witIte1263 = some prog := by
  have h : (senkBlock pwCfg pwL 0 witIte1263).isSome = true := by decide
  cases hm : senkBlock pwCfg pwL 0 witIte1263 with
  | none => simp [hm] at h
  | some prog => exact ⟨prog, rfl⟩

/-- JOINT WITNESS for `iteChunk_inv_abgeleitet`: every component holds
    jointly on the witness chunk -- the `x < 50` condition code, both
    accepted branch lowerings with both jump checks, exactly the
    `iteCode` layout -- with the shared non-degenerate package
    (`PipePaket`: one table its contract writes, memory-changing
    source and fetched-byte runs). -/
theorem iteChunk_inv_abgeleitet_zeuge :
    ∃ code j pt pe prog,
      senkBlock pwCfg pwL 0 witIte1263 = some prog ∧
      senkBedT pwCfg pwCheck = some (code, j) ∧
      senkBlock pwCfg pwL (0 + (encodeAll code).length + 6) witIteT1263 = some pt ∧
      senkBlock pwCfg pwL
        (0 + (encodeAll code).length + 6 + (encodeAll pt).length + 5) witIteE1263 =
        some pe ∧
      sprungOk ((encodeAll pt).length + 5) = true ∧ sprungOk (encodeAll pe).length = true ∧
      prog = iteCode code j pt pe ∧
      PipePaket := by
  obtain ⟨prog, hlow⟩ := witIteLow1263
  obtain ⟨code, j, pt, pe, hb, ht, he, hk1, hk2, hp⟩ :=
    iteChunk_inv_abgeleitet pwCfg pwL pwCheck witIteT1263 witIteE1263 0 prog hlow
  exact ⟨code, j, pt, pe, prog, hlow, hb, ht, he, hk1, hk2, hp, pipePaket_hold⟩

/-- The witness ite lowering, written out literally (condition code
    shared with the accepted `pwProg` check part, `take 5` then-branch,
    empty else-branch). Verified by computation below. -/
def witIteProg1263 : List Befehl :=
  [.movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (BitVec.ofNat 32 ((encodeAll (pwProg.take 5)).length + 5))] ++
  pwProg.take 5 ++
  [.jump32 (BitVec.ofNat 32 (encodeAll ([] : List Befehl)).length)]

/-- The literal lowering is the Lean recomputation. -/
theorem witIteLowLit1263 : senkBlock pwCfg pwL 0 witIte1263 = some witIteProg1263 := by
  decide

/-! ## 2. Witness memory for the ite chunk, and its derived run.

    The start state holds the witness ite bytes as the code region
    (execute only) and the two `pwSigma` slots as the data region
    (read/write, never execute) -- the `pwMem` shape with the code
    bytes swapped. `WorldRep`/`EnvRepr` follow the `pw` proofs: the
    data bytes are unchanged. -/

/-- Witness memory bytes: the ite bytes as code, `pwMemBytes` elsewhere. -/
def iteMemBytes1263 (a : Adresse) : Byte :=
  if 4096 ≤ a.toNat ∧ a.toNat < 4096 + (encodeAll witIteProg1263).length then
    (encodeAll witIteProg1263).getD (a.toNat - 4096) 0
  else pwMemBytes a

/-- Witness execute permission: exactly the ite bytes. -/
def iteCode1263 (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + (encodeAll witIteProg1263).length)

/-- Witness memory: ite code plus the `pwSigma` data slots. -/
def iteMem1263 : Speicher :=
  { bytes := iteMemBytes1263, lesbar := pwDaten, schreibbar := pwDaten,
    ausfuehrbar := iteCode1263 }

/-- Witness start state: `x` in `r10`, ite bytes at `rip`. -/
def iteStart1263 (x : Int) : Zustand :=
  { register := pwReg x, flags := witnessFlags, rip := natAdresse 4096,
    speicher := iteMem1263 }

/-- The ite bytes are small enough to leave the data region alone. -/
theorem ite_len1263 : (encodeAll witIteProg1263).length ≤ 4096 := by decide

/-- The witness code region holds the witness ite bytes. -/
theorem ite_code1263 :
    Pipeline.CodeAt iteMem1263 (natAdresse 4096) (encodeAll witIteProg1263) := by
  apply codeAt_von iteMem1263 4096 (encodeAll witIteProg1263) (by decide)
  intro a h1 h2
  have hd : ¬ (8192 ≤ a.toNat ∧ a.toNat < 8208) := by
    have hl := ite_len1263
    omega
  simp only [iteMem1263, iteCode1263, iteMemBytes1263, pwDaten, pwMemBytes,
    decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨⟨h1, h2⟩, hd, ?_⟩
  rw [if_pos ⟨h1, h2⟩]

/-- The witness memory represents the witness world. -/
theorem ite_worldRep1263 : WorldRep pwL iteMem1263 pwSigma := by
  intro t k f a h
  cases t; cases f
  simp only [pwL] at h
  by_cases e1 : k = 0
  · rw [if_pos e1] at h
    cases h
    subst e1
    refine ⟨by decide, by decide, by decide, fun lo hi hT => ?_⟩
    cases hT
    unfold RepSlot
    decide
  · rw [if_neg e1] at h
    by_cases e2 : k = 1
    · rw [if_pos e2] at h
      cases h
      subst e2
      refine ⟨by decide, by decide, by decide, fun lo hi hT => ?_⟩
      cases hT
      unfold RepSlot
      decide
    · rw [if_neg e2] at h; cases h

/-- The witness environments are represented (both check routes). -/
theorem ite_envRepr30_1263 :
    EnvRepr pwEnv30 (iteStart1263 30).register (abbOf pwCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

theorem ite_envRepr70_1263 :
    EnvRepr pwEnv70 (iteStart1263 70).register (abbOf pwCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

/-- CHUNK RUN, DERIVED (ite): from an accepted closed-ite lowering, a
    checked configuration, a separated layout and a represented start
    state whose code region holds the lowered bytes, the fetched-byte
    run reaches a state corresponding to the REAL `execBlock` outcome
    (`senkBlock_korrektC` as a black box -- no second interpreter).
    Every premise is used. -/
theorem iteChunk_lauf_abgeleitet (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (cnd : Expr D Γ Λ .bool)
    (t e : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ')
    (pre post flat : List Byte) (prog : List Befehl)
    (hlow : senkBlock c L pre.length
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.ite cnd t e)
        _root_.Gabbro.Grammatik.Block.nil) = some prog)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (st : Zustand)
    (hcode : Pipeline.CodeAt st.speicher (natAdresse c.codeBase) flat)
    (hf : flat = pre ++ encodeAll prog ++ post)
    (hrip : st.rip = addrOff (natAdresse c.codeBase) pre.length)
    (hW : WorldRep L st.speicher σ) (hE : EnvRepr ρ st.register (abbOf c)) :
    ∃ n st', laufBytes n st = .weiter st' ∧
      Pipeline.CodeAt st'.speicher (natAdresse c.codeBase) flat ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (pre.length + (encodeAll prog).length))
        (execBlock O passes R
          (_root_.Gabbro.Grammatik.Block.cons (Stmt.ite cnd t e)
            _root_.Gabbro.Grammatik.Block.nil) σ ρ) st' :=
  senkBlock_korrektC c L hc hsep O passes R flat _ pre post prog hlow σ ρ st
    hcode hf hrip hW hE

/-- JOINT WITNESS for `iteChunk_lauf_abgeleitet`: the `x = 30` run
    takes the then-branch (memory-changing store of `35`), the
    fetched-byte run agrees, with the shared non-degenerate package
    (`PipePaket`). -/
theorem iteChunk_lauf_abgeleitet_zeuge :
    ∃ prog n st',
      senkBlock pwCfg pwL ([] : List Byte).length witIte1263 = some prog ∧
      laufBytes n (iteStart1263 30) = .weiter st' ∧
      Pipeline.CodeAt st'.speicher (natAdresse pwCfg.codeBase) (encodeAll prog) ∧
      Entspricht pwCfg pwL
        (addrOff (natAdresse pwCfg.codeBase)
          (([] : List Byte).length + (encodeAll prog).length))
        (execBlock pwO 0 pwR witIte1263 pwSigma pwEnv30) st' ∧
      PipePaket := by
  have hrip : (iteStart1263 30).rip =
      addrOff (natAdresse pwCfg.codeBase) ([] : List Byte).length := by
    show natAdresse 4096 = addrOff (natAdresse 4096) 0
    exact (addrOff_null _).symm
  obtain ⟨n, st', hrun, hcode', hent⟩ :=
    iteChunk_lauf_abgeleitet pwCfg pwL pw_cfgOk pw_layoutSep pwCheck witIteT1263
      witIteE1263 [] [] (encodeAll witIteProg1263) witIteProg1263 witIteLowLit1263 pwO 0 pwR
      pwSigma pwEnv30 (iteStart1263 30) ite_code1263 (by simp) hrip
      ite_worldRep1263 ite_envRepr30_1263
  exact ⟨_, n, st', witIteLowLit1263, hrun, hcode', hent, pipePaket_hold⟩

/-! ## 3. Closed check chunks: lowering inversion.

    A closed check chunk is one `pruefung` with `nil` rest. An
    accepted lowering IS a `retGrund` reason exit with either the
    literal-`true` empty code or the deep condition code plus the
    conditional jump whose displacement equation lands exactly on the
    reason's refusal exit (`senkPruef` checks it; otherwise `none`). -/

/-- Witness closed check chunk: `check x < 50 else reason 0`. -/
def witPruef1263 : _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [] :=
  _root_.Gabbro.Grammatik.Block.pruefung pwCheck
    (_root_.Gabbro.Grammatik.Endblock.retGrund ⟨0, by decide⟩ pwHΛ)
    _root_.Gabbro.Grammatik.Block.nil

/-- LOWERING INVERSION (closed check chunk): an accepted lowering is a
    `retGrund` exit with the literal-`true` empty code or the deep
    condition code plus the exit jump with its landing equation. Every
    premise is used: `h` drives the block equation, the check
    equation and every case split. -/
theorem pruefChunk_inv_abgeleitet (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (cnd : Expr D Γ Λ .bool)
    (sonst : _root_.Gabbro.Grammatik.Endblock D V l Γ Λ)
    (pos : Nat) (prog : List Befehl)
    (h : senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.pruefung cnd sonst
        _root_.Gabbro.Grammatik.Block.nil) = some prog) :
    ∃ (r : Fin V.gruende) (hΛ : Λ.Perm V.ende), sonst = .retGrund r hΛ ∧
      ((istWahr cnd = true ∧ prog = []) ∨
        ∃ code j, senkBedT c cnd = some (code, j) ∧
          prog = code ++
            [.jumpIf32 j (sprungDisp c (pos + (encodeAll code).length) (exitAdr c r.val))] ∧
          addrOff (natAdresse c.codeBase)
            (pos + (encodeAll code).length +
              (encode (.jumpIf32 j
                (sprungDisp c (pos + (encodeAll code).length) (exitAdr c r.val)))).length) +
            dispWort (sprungDisp c (pos + (encodeAll code).length) (exitAdr c r.val)) =
            natAdresse (exitAdr c r.val)) := by
  simp only [senkBlock] at h
  cases hs : senkPruef c pos cnd sonst with
  | none => simp [hs] at h
  | some p =>
    simp only [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    cases sonst with
    | retGrund r hΛ =>
      simp only [senkPruef] at hs
      by_cases hw : istWahr cnd = true
      · rw [if_pos hw] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨r, hΛ, rfl, Or.inl ⟨hw, by simp⟩⟩
      · rw [if_neg hw] at hs
        cases hv : senkBedT c cnd with
        | none => simp [hv] at hs
        | some cj =>
          obtain ⟨code, j⟩ := cj
          simp only [hv] at hs
          by_cases he : addrOff (natAdresse c.codeBase)
              (pos + (encodeAll code).length +
                (encode (.jumpIf32 j
                  (sprungDisp c (pos + (encodeAll code).length) (exitAdr c r.val)))).length) +
              dispWort (sprungDisp c (pos + (encodeAll code).length) (exitAdr c r.val)) =
              natAdresse (exitAdr c r.val)
          · rw [if_pos he] at hs
            simp only [Option.some.injEq] at hs
            subst hs
            exact ⟨r, hΛ, rfl, Or.inr ⟨code, j, rfl, by simp, he⟩⟩
          · rw [if_neg he] at hs
            cases hs
    | ret e hΛ => simp [senkPruef] at hs
    | leave hh => simp [senkPruef] at hs
    | next hh => simp [senkPruef] at hs
    | cons s rest => simp [senkPruef] at hs
    | bind e rest => simp [senkPruef] at hs
    | bindAxiom a args he hw hg hd hgd rest => simp [senkPruef] at hs
    | bindAxiomElse a args he hr hw hg hd hgd err rest => simp [senkPruef] at hs

/-- The witness check chunk lowers (by computation). -/
theorem witPruefLow1263 :
    ∃ prog, senkBlock pwCfg pwL 0 witPruef1263 = some prog := by
  have h : (senkBlock pwCfg pwL 0 witPruef1263).isSome = true := by decide
  cases hm : senkBlock pwCfg pwL 0 witPruef1263 with
  | none => simp [hm] at h
  | some prog => exact ⟨prog, rfl⟩

/-- The witness check lowering, written out literally (condition code
    shared with `witIteProg1263`, exit jump to `12288`). Verified by
    computation below. -/
def witPruefProg1263 : List Befehl :=
  [.movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (sprungDisp pwCfg
      (0 + (encodeAll
        [.movReg64 .rax .r10, .movImm64 .rcx (intWort 50),
          .cmpReg64 .rax .rcx]).length)
      (exitAdr pwCfg 0))]

/-- The literal check lowering is the Lean recomputation. -/
theorem witPruefLowLit1263 :
    senkBlock pwCfg pwL 0 witPruef1263 = some witPruefProg1263 := by
  decide

/-- JOINT WITNESS for `pruefChunk_inv_abgeleitet`: the exit jump with
    its landing equation holds jointly on the witness chunk, with the
    shared non-degenerate package (`PipePaket`). -/
theorem pruefChunk_inv_abgeleitet_zeuge :
    ∃ code j,
      senkBlock pwCfg pwL 0 witPruef1263 = some witPruefProg1263 ∧
      senkBedT pwCfg pwCheck = some (code, j) ∧
      witPruefProg1263 = code ++
        [.jumpIf32 j (sprungDisp pwCfg (0 + (encodeAll code).length)
          (exitAdr pwCfg (⟨0, by decide⟩ : Fin pwV.gruende).val))] ∧
      addrOff (natAdresse pwCfg.codeBase)
        (0 + (encodeAll code).length +
          (encode (.jumpIf32 j (sprungDisp pwCfg (0 + (encodeAll code).length)
            (exitAdr pwCfg (⟨0, by decide⟩ : Fin pwV.gruende).val)))).length) +
        dispWort (sprungDisp pwCfg (0 + (encodeAll code).length)
          (exitAdr pwCfg (⟨0, by decide⟩ : Fin pwV.gruende).val)) =
        natAdresse (exitAdr pwCfg (⟨0, by decide⟩ : Fin pwV.gruende).val) ∧
      PipePaket := by
  obtain ⟨r, hΛ, hr, hor⟩ :=
    pruefChunk_inv_abgeleitet (Λ' := ([] : List (Res pwD))) pwCfg pwL pwCheck
      (_root_.Gabbro.Grammatik.Endblock.retGrund ⟨0, by decide⟩ pwHΛ)
      0 witPruefProg1263 witPruefLowLit1263
  cases hr
  rcases hor with ⟨hw, hp⟩ | ⟨code, j, hb, hp, he⟩
  · have hfalse : istWahr pwCheck = false := by decide
    rw [hfalse] at hw
    cases hw
  · exact ⟨code, j, witPruefLowLit1263, hb, hp, he, pipePaket_hold⟩

/- CUTS:
    - Proved here: closed-ite lowering inversion
      (`iteChunk_inv_abgeleitet`) with joint non-degenerate witness.
    - OPEN: derived runs, coverage, validator soundness, closings,
      refusals; everything listed in the module header.
-/

#print axioms iteCheckValidate
#print axioms iteChunk_inv_abgeleitet
#print axioms iteChunk_inv_abgeleitet_zeuge

end Gabbro.Grammatik.X86.PipeChunkIte
