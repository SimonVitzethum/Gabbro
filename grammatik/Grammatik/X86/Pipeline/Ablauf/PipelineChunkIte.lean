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
import Grammatik.X86.Pipeline.Kern.Pipeline
import Grammatik.X86.Pipeline.Kern.PipelineWitnesses
import Grammatik.X86.Pipeline.Ablauf.PipelineChunkDerive
import Grammatik.X86.Pipeline.Ablauf.PipelineWork
import Grammatik.X86.Pipeline.Ablauf.PipelineWorkBranches
import Grammatik.X86.Kosten.DerivedWorkBound
import Grammatik.X86.Kosten.BudgetExecution
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
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
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
    pruefChunk_inv_abgeleitet pwCfg pwL pwCheck
      (_root_.Gabbro.Grammatik.Endblock.retGrund ⟨0, by decide⟩ pwHΛ)
      0 witPruefProg1263 witPruefLowLit1263
  cases hr
  rcases hor with ⟨hw, hp⟩ | ⟨code, j, hb, hp, he⟩
  · have hfalse : istWahr pwCheck = false := by decide
    rw [hfalse] at hw
    cases hw
  · exact ⟨code, j, witPruefLowLit1263, hb, hp, he, pipePaket_hold⟩

/-! ## 4. Witness memory for the check chunk, and its derived run.

    Same shape as §2 with the check bytes: the passing route (`x = 30`)
    falls through to the end of the code, the failing route (`x = 70`)
    jumps to the refusal exit `12288`. -/

/-- Witness memory bytes: the check bytes as code, `pwMemBytes` elsewhere. -/
def pruefMemBytes1263 (a : Adresse) : Byte :=
  if 4096 ≤ a.toNat ∧ a.toNat < 4096 + (encodeAll witPruefProg1263).length then
    (encodeAll witPruefProg1263).getD (a.toNat - 4096) 0
  else pwMemBytes a

/-- Witness execute permission: exactly the check bytes. -/
def pruefCode1263 (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + (encodeAll witPruefProg1263).length)

/-- Witness memory: check code plus the `pwSigma` data slots. -/
def pruefMem1263 : Speicher :=
  { bytes := pruefMemBytes1263, lesbar := pwDaten, schreibbar := pwDaten,
    ausfuehrbar := pruefCode1263 }

/-- Witness start state: `x` in `r10`, check bytes at `rip`. -/
def pruefStart1263 (x : Int) : Zustand :=
  { register := pwReg x, flags := witnessFlags, rip := natAdresse 4096,
    speicher := pruefMem1263 }

/-- The check bytes are small enough to leave the data region alone. -/
theorem pruef_len1263 : (encodeAll witPruefProg1263).length ≤ 4096 := by decide

/-- The witness code region holds the witness check bytes. -/
theorem pruef_code1263 :
    Pipeline.CodeAt pruefMem1263 (natAdresse 4096)
      (encodeAll witPruefProg1263) := by
  apply codeAt_von pruefMem1263 4096 (encodeAll witPruefProg1263) (by decide)
  intro a h1 h2
  have hd : ¬ (8192 ≤ a.toNat ∧ a.toNat < 8208) := by
    have hl := pruef_len1263
    omega
  simp only [pruefMem1263, pruefCode1263, pruefMemBytes1263, pwDaten, pwMemBytes,
    decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨⟨h1, h2⟩, hd, ?_⟩
  rw [if_pos ⟨h1, h2⟩]

/-- The witness memory represents the witness world. -/
theorem pruef_worldRep1263 : WorldRep pwL pruefMem1263 pwSigma := by
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
theorem pruef_envRepr30_1263 :
    EnvRepr pwEnv30 (pruefStart1263 30).register (abbOf pwCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

theorem pruef_envRepr70_1263 :
    EnvRepr pwEnv70 (pruefStart1263 70).register (abbOf pwCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

/-- CHUNK RUN, DERIVED (check): from an accepted closed-check
    lowering, a checked configuration, a separated layout and a
    represented start state whose code region holds the lowered bytes,
    the fetched-byte run reaches a state corresponding to the REAL
    `execBlock` outcome -- normal fall-through or the reason exit
    (`senkBlock_korrektC` as a black box). Every premise is used. -/
theorem pruefChunk_lauf_abgeleitet (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (cnd : Expr D Γ Λ .bool)
    (sonst : _root_.Gabbro.Grammatik.Endblock D V l Γ Λ)
    (pre post flat : List Byte) (prog : List Befehl)
    (hlow : senkBlock c L pre.length
      (_root_.Gabbro.Grammatik.Block.pruefung cnd sonst
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
          (_root_.Gabbro.Grammatik.Block.pruefung cnd sonst
            _root_.Gabbro.Grammatik.Block.nil) σ ρ) st' :=
  senkBlock_korrektC c L hc hsep O passes R flat _ pre post prog hlow σ ρ st
    hcode hf hrip hW hE

/-- JOINT WITNESS for `pruefChunk_lauf_abgeleitet` (passing route):
    the `x = 30` check passes, the fetched-byte run falls through to
    the end of the code, with the shared non-degenerate package
    (`PipePaket`). -/
theorem pruefChunk_lauf_abgeleitet_zeuge :
    ∃ prog n st',
      senkBlock pwCfg pwL ([] : List Byte).length witPruef1263 = some prog ∧
      laufBytes n (pruefStart1263 30) = .weiter st' ∧
      Pipeline.CodeAt st'.speicher (natAdresse pwCfg.codeBase) (encodeAll prog) ∧
      Entspricht pwCfg pwL
        (addrOff (natAdresse pwCfg.codeBase)
          (([] : List Byte).length + (encodeAll prog).length))
        (execBlock pwO 0 pwR witPruef1263 pwSigma pwEnv30) st' ∧
      PipePaket := by
  have hrip : (pruefStart1263 30).rip =
      addrOff (natAdresse pwCfg.codeBase) ([] : List Byte).length := by
    show natAdresse 4096 = addrOff (natAdresse 4096) 0
    exact (addrOff_null _).symm
  obtain ⟨n, st', hrun, hcode', hent⟩ :=
    pruefChunk_lauf_abgeleitet pwCfg pwL pw_cfgOk pw_layoutSep pwCheck
      (_root_.Gabbro.Grammatik.Endblock.retGrund ⟨0, by decide⟩ pwHΛ)
      [] [] (encodeAll witPruefProg1263) witPruefProg1263 witPruefLowLit1263 pwO 0 pwR
      pwSigma pwEnv30 (pruefStart1263 30) pruef_code1263 (by simp) hrip
      pruef_worldRep1263 pruef_envRepr30_1263
  exact ⟨_, n, st', witPruefLowLit1263, hrun, hcode', hent, pipePaket_hold⟩

/-- The failing route on concrete data: the `x = 70` check fails, the
    fetched-byte run reaches the refusal exit `12288` with the world
    represented. -/
theorem pruefChunk_grund1263 :
    ∃ prog n st',
      senkBlock pwCfg pwL ([] : List Byte).length witPruef1263 = some prog ∧
      laufBytes n (pruefStart1263 70) = .weiter st' ∧
      Pipeline.CodeAt st'.speicher (natAdresse pwCfg.codeBase) (encodeAll prog) ∧
      Entspricht pwCfg pwL
        (addrOff (natAdresse pwCfg.codeBase)
          (([] : List Byte).length + (encodeAll prog).length))
        (execBlock pwO 0 pwR witPruef1263 pwSigma pwEnv70) st' ∧
      PipePaket := by
  have hrip : (pruefStart1263 70).rip =
      addrOff (natAdresse pwCfg.codeBase) ([] : List Byte).length := by
    show natAdresse 4096 = addrOff (natAdresse 4096) 0
    exact (addrOff_null _).symm
  obtain ⟨n, st', hrun, hcode', hent⟩ :=
    pruefChunk_lauf_abgeleitet pwCfg pwL pw_cfgOk pw_layoutSep pwCheck
      (_root_.Gabbro.Grammatik.Endblock.retGrund ⟨0, by decide⟩ pwHΛ)
      [] [] (encodeAll witPruefProg1263) witPruefProg1263 witPruefLowLit1263 pwO 0 pwR
      pwSigma pwEnv70 (pruefStart1263 70) pruef_code1263 (by simp) hrip
      pruef_worldRep1263 pruef_envRepr70_1263
  exact ⟨_, n, st', witPruefLowLit1263, hrun, hcode', hent, pipePaket_hold⟩

/-! ## 5. Coverage, validator soundness and the jump layout.

    Coverage of a closed ite/check chunk is the generic per-chunk
    coverage at generated length (`deckung_chunk_generisch`, reused):
    the lowering equation feeds the inversion, which fixes the
    program. The validator recomputes the lowering, so an accepted
    candidate re-checks every jump layout decision (`sprungOk` for
    both ite jumps, the exit equation for checks). -/

/-- CHUNK COVERAGE, DERIVED (ite): the lowered closed-ite chunk is
    covered by the admitted pipeline summary over its own generated
    length. Every premise is used: `hlow` feeds the inversion. -/
theorem iteChunk_deckung_abgeleitet (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (cnd : Expr D Γ Λ .bool)
    (t e : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ')
    (pos : Nat) (prog : List Befehl)
    (hlow : senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.ite cnd t e)
        _root_.Gabbro.Grammatik.Block.nil) = some prog) :
    Deckung pipeSummary prog.length (decodiertZu prog) := by
  obtain ⟨code, j, pt, pe, _hb, _ht, _he, _hk1, _hk2, hp⟩ :=
    iteChunk_inv_abgeleitet c L cnd t e pos prog hlow
  rw [hp]
  exact deckung_chunk_generisch _

/-- JOINT WITNESS for `iteChunk_deckung_abgeleitet`: the witness ite
    lowering is covered at its generated length, with the shared
    non-degenerate package (`PipePaket`). -/
theorem iteChunk_deckung_abgeleitet_zeuge :
    ∃ prog,
      senkBlock pwCfg pwL 0 witIte1263 = some prog ∧
      Deckung pipeSummary prog.length (decodiertZu prog) ∧
      PipePaket := by
  refine ⟨witIteProg1263, witIteLowLit1263, ?_, pipePaket_hold⟩
  exact iteChunk_deckung_abgeleitet pwCfg pwL pwCheck witIteT1263 witIteE1263 0 _
    witIteLowLit1263

/-- CHUNK COVERAGE, DERIVED (check): the lowered closed-check chunk is
    covered by the admitted pipeline summary over its own generated
    length. Every premise is used: `hlow` feeds the inversion. -/
theorem pruefChunk_deckung_abgeleitet (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (cnd : Expr D Γ Λ .bool)
    (sonst : _root_.Gabbro.Grammatik.Endblock D V l Γ Λ)
    (pos : Nat) (prog : List Befehl)
    (hlow : senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.pruefung cnd sonst
        _root_.Gabbro.Grammatik.Block.nil) = some prog) :
    Deckung pipeSummary prog.length (decodiertZu prog) := by
  obtain ⟨r, hΛ, _hr, hor⟩ :=
    pruefChunk_inv_abgeleitet c L cnd sonst pos prog hlow
  exact deckung_chunk_generisch prog

/-- JOINT WITNESS for `pruefChunk_deckung_abgeleitet`: the witness
    check lowering is covered at its generated length, with the shared
    non-degenerate package (`PipePaket`). -/
theorem pruefChunk_deckung_abgeleitet_zeuge :
    ∃ prog,
      senkBlock pwCfg pwL 0 witPruef1263 = some prog ∧
      Deckung pipeSummary prog.length (decodiertZu prog) ∧
      PipePaket := by
  refine ⟨witPruefProg1263, witPruefLowLit1263, ?_, pipePaket_hold⟩
  exact pruefChunk_deckung_abgeleitet pwCfg pwL pwCheck
    (_root_.Gabbro.Grammatik.Endblock.retGrund ⟨0, by decide⟩ pwHΛ) 0 _
    witPruefLowLit1263

/-- VALIDATOR SOUNDNESS: an accepted candidate is the Lean
    recomputation. Every premise is used: `h` drives the split and
    yields both conjuncts. -/
theorem iteCheckValidate_sound (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : iteCheckValidate c L b bytes = true) :
    ∃ prog, senkBlock c L 0 b = some prog ∧ bytes = encodeAll prog := by
  unfold iteCheckValidate at h
  cases hc : senkBlock c L 0 b with
  | none => simp [hc] at h
  | some prog =>
    simp only [hc] at h
    simp only [decide_eq_true_eq] at h
    exact ⟨prog, rfl, h⟩

/-- JOINT WITNESS for `iteCheckValidate_sound`: the witness ite chunk
    validates its own encoding, with the shared non-degenerate package
    (`PipePaket`). -/
theorem iteCheckValidate_sound_zeuge :
    ∃ prog,
      senkBlock pwCfg pwL 0 witIte1263 = some prog ∧
      iteCheckValidate pwCfg pwL witIte1263 (encodeAll prog) = true ∧
      PipePaket := by
  refine ⟨witIteProg1263, witIteLowLit1263, ?_, pipePaket_hold⟩
  unfold iteCheckValidate
  rw [witIteLowLit1263]
  decide

/-- JUMP LAYOUT (ite): the two displacements are exactly the
    `iteSprung`/`iteEnde` forms, and under the decided `sprungOk`
    checks the taken jumps land on the else-branch start and the end.
    No premise is syntax: no witness needed. -/
theorem iteChunk_sprungZiele (base preLen : Nat) (code pt pe : List Befehl)
    (j : Bedingung)
    (hk1 : sprungOk ((encodeAll pt).length + 5) = true)
    (hk2 : sprungOk (encodeAll pe).length = true) :
    iteSprung j pt = .jumpIf32 j (BitVec.ofNat 32 ((encodeAll pt).length + 5)) ∧
    iteEnde pe = .jump32 (BitVec.ofNat 32 (encodeAll pe).length) ∧
    addrOff (natAdresse base) (preLen + (encodeAll code).length + 6) +
        dispWort (BitVec.ofNat 32 ((encodeAll pt).length + 5)) =
        addrOff (natAdresse base)
          (preLen + (encodeAll code).length + 6 + (encodeAll pt).length + 5) ∧
    addrOff (natAdresse base)
        (preLen + (encodeAll code).length + 6 + (encodeAll pt).length + 5) +
        dispWort (BitVec.ofNat 32 (encodeAll pe).length) =
        addrOff (natAdresse base)
          (preLen + (encodeAll code).length + 6 + (encodeAll pt).length + 5 +
            (encodeAll pe).length) :=
  ⟨rfl, rfl, sprungOk_addr _ _ _ hk1, sprungOk_addr _ _ _ hk2⟩

/-- RELAXATION GATE: the decided `sprungOk` check is exactly the
    32-bit displacement round trip. The lowering keeps the fixed-wide
    jumps only when this holds and otherwise refuses (`none`); no
    displacement is ever silently truncated, and no short (rel8) form
    is silently substituted -- that layout lives in `ISARelax` and
    stays OPEN here. No premise is syntax: no witness needed. -/
theorem iteChunk_sprungOk_entscheidung (k : Nat) :
    sprungOk k = true ↔
      dispWort (BitVec.ofNat 32 k) = BitVec.ofNat 64 k := by
  simp [sprungOk, decide_eq_true_eq]

/-! ## 6. Closing, and the remaining refusals.

    The closing composes the validator soundness with the fetched-byte
    run (`senkBlock_korrektC` as a black box): an accepted candidate is
    the Lean recomputation, and the bytes run from the loaded image to
    the corresponding `execBlock` outcome. Loops (`traverse`; `retry`
    and `forever` are already refused in `PipeWorkBranches`) and calls
    (`Stmt.call`) stay refused with named theorems and firing poison
    probes. -/

/-- CLOSING (in the style of `pipeline_correct`): a validated
    candidate for any source block runs from the loaded image to the
    corresponding REAL `execBlock` outcome with the code region
    intact. Every premise is used. -/
theorem pipelineChunkIte_schluss (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : iteCheckValidate c L b bytes = true)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) (st : Zustand)
    (hcode : Pipeline.CodeAt st.speicher (natAdresse c.codeBase) bytes)
    (hrip : st.rip = natAdresse c.codeBase)
    (hW : WorldRep L st.speicher σ) (hE : EnvRepr ρ st.register (abbOf c)) :
    ∃ prog n st', senkBlock c L 0 b = some prog ∧ bytes = encodeAll prog ∧
      laufBytes n st = .weiter st' ∧
      Pipeline.CodeAt st'.speicher (natAdresse c.codeBase) bytes ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (0 + (encodeAll prog).length))
        (execBlock O passes R b σ ρ) st' := by
  obtain ⟨prog, hlow, hb⟩ := iteCheckValidate_sound c L b bytes hval
  obtain ⟨n, st', hrun, hcode', hent⟩ :=
    senkBlock_korrektC c L hc hsep O passes R bytes b [] [] prog
      (by exact hlow) σ ρ st hcode (by simp [hb])
      (by rw [hrip]; exact (addrOff_null _).symm) hW hE
  exact ⟨prog, n, st', hlow, hb, hrun, hcode', hent⟩

/-- JOINT WITNESS for `pipelineChunkIte_schluss`: the witness ite
    chunk validates its literal bytes, the `x = 30` fetched-byte run
    agrees with the source run, with the shared non-degenerate package
    (`PipePaket`). -/
theorem pipelineChunkIte_schluss_zeuge :
    ∃ prog n st',
      iteCheckValidate pwCfg pwL witIte1263 (encodeAll witIteProg1263) = true ∧
      senkBlock pwCfg pwL 0 witIte1263 = some prog ∧
      encodeAll witIteProg1263 = encodeAll prog ∧
      laufBytes n (iteStart1263 30) = .weiter st' ∧
      Pipeline.CodeAt st'.speicher (natAdresse pwCfg.codeBase)
        (encodeAll witIteProg1263) ∧
      Entspricht pwCfg pwL
        (addrOff (natAdresse pwCfg.codeBase) (0 + (encodeAll prog).length))
        (execBlock pwO 0 pwR witIte1263 pwSigma pwEnv30) st' ∧
      PipePaket := by
  have hval : iteCheckValidate pwCfg pwL witIte1263
      (encodeAll witIteProg1263) = true := by
    unfold iteCheckValidate
    rw [witIteLowLit1263]
    decide
  have hrip : (iteStart1263 30).rip = natAdresse pwCfg.codeBase := by rfl
  obtain ⟨prog, n, st', hlow, hb, hrun, hcode', hent⟩ :=
    pipelineChunkIte_schluss pwCfg pwL pw_cfgOk pw_layoutSep witIte1263
      (encodeAll witIteProg1263) hval pwO 0 pwR pwSigma pwEnv30 (iteStart1263 30)
      ite_code1263 hrip ite_worldRep1263 ite_envRepr30_1263
  exact ⟨prog, n, st', hval, hlow, hb, hrun, hcode', hent, pipePaket_hold⟩

/-- REFUSAL (loop): a `traverse` head has no `senkBlock` lowering at
    any position -- refused, never guessed. -/
theorem pipelineChunkIte_verweigert_traverse (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : _root_.Gabbro.Grammatik.Block D V true
      ((.index (D.count t)) :: Γ) Λ Λ)
    (rest : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ'') (pos : Nat) :
    senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.traverse t inv body) rest) =
      none := rfl

/-- The witness writes the table (both sides write everything). -/
theorem witCallHw1263 :
    ∀ t, (pwD.signatur ()).schreibt t = true → pwV.schreibt t = true :=
  fun _ _ => rfl

/-- No marks move on the witness call. -/
theorem witCallHk1263 : Untermulti
    ((pwD.signatur ()).konsumiert.map (Res.vonMarke pwD)) [] :=
  ⟨[], List.Perm.refl _, List.Sublist.refl _⟩

/-- No globals move on the witness call (no globals exist). -/
theorem witCallHg1263 :
    ∀ g : pwD.Glob, (pwD.signatur ()).gschreibt g = true → pwV.gschreibt g = true :=
  fun g => nomatch g

/-- No locks are required on the witness call (no locks exist). -/
theorem witCallHh1263 :
    ∀ L : pwD.Lock, L ∈ (pwD.signatur ()).haelt → Res.held L ∈ ([] : List (Res pwD)) :=
  fun L => nomatch L

/-- The call fitness on the witness declaration: parameterless, writes
    the table, no held locks. -/
theorem witCallHp1263 : RufPasst pwD pwV (pwD.signatur ()) [] :=
  { hw := witCallHw1263, hg := witCallHg1263, hk := witCallHk1263,
    hh := witCallHh1263 }

/-- The witness callee takes no reason channel. -/
theorem witCallHr1263 : pwD.gruende () = 0 := rfl

/-- The witness call passes no arguments. -/
def witCallArgs1263 : Args pwD pwCtx [] (pwD.params ()) := .nil

/-- REFUSAL (call): a `call` head has no `senkBlock` lowering at any
    position -- refused, never guessed. -/
theorem pipelineChunkIte_verweigert_call (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : _root_.Gabbro.Grammatik.Block D V l Γ (nach D f Λ) Λ'') (pos : Nat) :
    senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.call f args hp hr) rest) =
      none := rfl

/-- Poison probe: a `traverse` head is refused. -/
theorem gift1263_traverse :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.traverse (V := pwV) (l := false) () Expr.wahr
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV true
              ((.index (pwD.count ())) :: pwCtx) [] []))
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [])) =
      none :=
  pipelineChunkIte_verweigert_traverse _ _ _ _ _ _ _

/-- Poison probe: a `call` head is refused. -/
theorem gift1263_call :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.call (V := pwV) (l := false) (f := ()) witCallArgs1263
          witCallHp1263 witCallHr1263)
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx (nach pwD () []) [])) =
      none :=
  pipelineChunkIte_verweigert_call _ _ _ _ _ _ _ _

/-- JOINT WITNESS for the loop refusal, with the shared non-degenerate
    package (`PipePaket`). -/
theorem pipelineChunkIte_verweigert_traverse_zeuge :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.traverse (V := pwV) (l := false) () Expr.wahr
          (_root_.Gabbro.Grammatik.Block.nil :
            _root_.Gabbro.Grammatik.Block pwD pwV true
              ((.index (pwD.count ())) :: pwCtx) [] []))
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx [] [])) =
      none ∧ PipePaket :=
  ⟨gift1263_traverse, pipePaket_hold⟩

/-- JOINT WITNESS for the call refusal, with the shared non-degenerate
    package (`PipePaket`). -/
theorem pipelineChunkIte_verweigert_call_zeuge :
    senkBlock pwCfg pwL 0
      (_root_.Gabbro.Grammatik.Block.cons
        (Stmt.call (V := pwV) (l := false) (f := ()) witCallArgs1263
          witCallHp1263 witCallHr1263)
        (_root_.Gabbro.Grammatik.Block.nil :
          _root_.Gabbro.Grammatik.Block pwD pwV false pwCtx (nach pwD () []) [])) =
      none ∧ PipePaket :=
  ⟨gift1263_call, pipePaket_hold⟩

/- CUTS:
    - Proved here (generic): closed-ite lowering inversion
      (`iteChunk_inv_abgeleitet`); the witness ite lowering literally
      (`witIteProg1263`, `witIteLowLit1263`); the witness ite memory
      with code region, world representation and both environments
      (`iteMemBytes1263`/`iteCode1263`/`iteMem1263`/`iteStart1263`,
      `ite_len1263`, `ite_code1263`, `ite_worldRep1263`,
      `ite_envRepr30_1263`, `ite_envRepr70_1263`); the derived ite
      chunk run (`iteChunk_lauf_abgeleitet`, via the accepted
      `senkBlock_korrektC`); closed-check lowering inversion with the
      exit-jump landing equation (`pruefChunk_inv_abgeleitet`); the
      witness check lowering literally (`witPruefProg1263`,
      `witPruefLowLit1263`); the witness check memory with code
      region, world representation and both environments
      (`pruefMemBytes1263`/`pruefCode1263`/`pruefMem1263`/
      `pruefStart1263`, `pruef_len1263`, `pruef_code1263`,
      `pruef_worldRep1263`, `pruef_envRepr30_1263`,
      `pruef_envRepr70_1263`); the derived check chunk run, both the
      passing and the failing route (`pruefChunk_lauf_abgeleitet`,
      `pruefChunk_grund1263` is the concrete failing route); chunk
      coverage at generated length for both shapes
      (`iteChunk_deckung_abgeleitet`,
      `pruefChunk_deckung_abgeleitet`, via the accepted
      `deckung_chunk_generisch`); the recomputing validator with
      soundness (`iteCheckValidate`, `iteCheckValidate_sound`); the
      ite jump layout (`iteChunk_sprungZiele`: `iteSprung`/`iteEnde`
      displacements with the taken-jump landing facts from the decided
      `sprungOk` checks) and the relaxation gate
      (`iteChunk_sprungOk_entscheidung`: the check is exactly the
      32-bit round trip; out-of-range is refused, never truncated; the
      short rel8 layout of `ISARelax` stays OPEN); the closing in the
      style of `pipeline_correct` (`pipelineChunkIte_schluss`); two
      refusals (loop `traverse`,
      `pipelineChunkIte_verweigert_traverse`; call,
      `pipelineChunkIte_verweigert_call`) with two firing poison
      probes (`gift1263_traverse`, `gift1263_call`); joint
      non-degenerate witnesses for every syntax-premise theorem (one
      table its contract writes; reached source runs; target
      fetched-byte runs; the shared `PipePaket`) plus the concrete
      witness fitness facts (`witCallHw1263`, `witCallHg1263`,
      `witCallHk1263`, `witCallHh1263`, `witCallHp1263`,
      `witCallHr1263`, `witCallArgs1263`).
    - Reused, not duplicated: `senkBlock`/`senkBlock_ite_inv`/
      `senkPruef`/`senkBedT`/`senkVergleich`/`iteCode`/`iteSprung`/
      `iteEnde`/`sprungOk`/`sprungOk_addr`/`sprungDisp`/`exitAdr`/
      `Entspricht`/`senkBlock_korrektC`, `pipeSummary`/
      `pipeSummary_expand`, `decodiertZu`/`arbeit_decodiert`,
      `Deckung`, `deckung_chunk_generisch`, `cfgOk`/`WorldRep`/
      `LayoutSep`/`EnvRepr`/`RepSlot`/`repOk`, `addrOff_null`,
      `codeAt_von`, and the whole `pw` witness package with
      `PipePaket`/`pipePaket_hold`. No second IR, no second
      interpreter, no optimiser edit, no checker change.
    - OPEN (fragment): only closed single-ite and single-check chunks
      are derived here; `assignSlot` chains compose through lane
      1219, longer ite/check sequences through the accepted
      `senkBlock_korrektC` directly; all other shapes (`bind`,
      `bindCall*`, `narrow`, `gleit*`, `exchange`, `traverse`,
      `retry`, `forever`, calls, device/register forms) are refused
      (`none`), never guessed.
    - OPEN (relaxation): short (rel8) branch forms are not introduced;
      the fixed-wide layout with decided `sprungOk` gates is kept,
      and the iterative `ISARelax` layout stays unconnected.
    - OPEN (machine): single core, model memory, no TSO/concurrency
      claim (inherited from `Pipeline.lean`'s own CUTS); entry/image/
      ABI mapping composes through `PipelineImage`/`PipelineEntry`;
      named hardware timing stays a hardware assumption.
    - No weakened guarantee: unsupported shapes are refused, never
      guessed.
-/

#print axioms iteCheckValidate
#print axioms iteChunk_inv_abgeleitet
#print axioms iteChunk_inv_abgeleitet_zeuge
#print axioms witIteT1263
#print axioms witIteE1263
#print axioms witIte1263
#print axioms witIteLow1263
#print axioms witIteProg1263
#print axioms witIteLowLit1263
#print axioms iteMemBytes1263
#print axioms iteCode1263
#print axioms iteMem1263
#print axioms iteStart1263
#print axioms ite_len1263
#print axioms ite_code1263
#print axioms ite_worldRep1263
#print axioms ite_envRepr30_1263
#print axioms ite_envRepr70_1263
#print axioms iteChunk_lauf_abgeleitet
#print axioms iteChunk_lauf_abgeleitet_zeuge
#print axioms witPruef1263
#print axioms pruefChunk_inv_abgeleitet
#print axioms witPruefLow1263
#print axioms witPruefProg1263
#print axioms witPruefLowLit1263
#print axioms pruefChunk_inv_abgeleitet_zeuge
#print axioms pruefMemBytes1263
#print axioms pruefCode1263
#print axioms pruefMem1263
#print axioms pruefStart1263
#print axioms pruef_len1263
#print axioms pruef_code1263
#print axioms pruef_worldRep1263
#print axioms pruef_envRepr30_1263
#print axioms pruef_envRepr70_1263
#print axioms pruefChunk_lauf_abgeleitet
#print axioms pruefChunk_lauf_abgeleitet_zeuge
#print axioms pruefChunk_grund1263
#print axioms iteChunk_deckung_abgeleitet
#print axioms iteChunk_deckung_abgeleitet_zeuge
#print axioms pruefChunk_deckung_abgeleitet
#print axioms pruefChunk_deckung_abgeleitet_zeuge
#print axioms iteCheckValidate_sound
#print axioms iteCheckValidate_sound_zeuge
#print axioms iteChunk_sprungZiele
#print axioms iteChunk_sprungOk_entscheidung
#print axioms pipelineChunkIte_schluss
#print axioms pipelineChunkIte_schluss_zeuge
#print axioms pipelineChunkIte_verweigert_traverse
#print axioms witCallHw1263
#print axioms witCallHk1263
#print axioms witCallHg1263
#print axioms witCallHh1263
#print axioms witCallHp1263
#print axioms witCallHr1263
#print axioms witCallArgs1263
#print axioms pipelineChunkIte_verweigert_call
#print axioms gift1263_traverse
#print axioms gift1263_call
#print axioms pipelineChunkIte_verweigert_traverse_zeuge
#print axioms pipelineChunkIte_verweigert_call_zeuge

end Gabbro.Grammatik.X86.PipeChunkIte
