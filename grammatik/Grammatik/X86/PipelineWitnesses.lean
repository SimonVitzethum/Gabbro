/-
  File:      Grammatik/X86/PipelineWitnesses.lean
  Subject:   The joint non-degenerate witness for the end-to-end pipeline
             (`Pipeline.lean`) and its poison probes.

  One source program over the REAL syntax, taken through the WHOLE chain:
  optimiser certificate accepted (a `2 * 3` that the lowering cannot
  take is folded to `6`), candidate bytes (written out literally, as an
  untrusted producer would emit them) accepted by `validate` BY
  COMPUTATION, fetched and executed from a byte-level memory, final slot
  values equal to the REAL `execBlock` run, which changed memory. A second
  start state takes the failing-check route to the refusal exit. Poison
  probes: tampered byte, wrong certificate, unsupported statements,
  register clash, code/data overlap -- all refused.

  Reused: everything from `Pipeline.lean` and its imports; nothing here is
  on the trust path (witness only).
-/
import Grammatik.X86.Pipeline

namespace Gabbro.Grammatik.X86.PipelineWitnesses

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline

/-! ## 1. The witness declaration, contract and program -/

/-- One table of two rows with one integer field in `0 .. 1000`, written
    by the single function. -/
def pwD : Deklaration where
  Tab := Unit
  count := fun _ => 2
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 1000
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  rang := fun L => nomatch L
  maskiert := fun L => nomatch L
  Marke := Empty
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => witSig628
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The contract: writes the table, one refusal reason. -/
def pwV : Vertrag pwD :=
  { schreibt := fun _ => true
    gschreibt := fun g => nomatch g
    erg := none
    gruende := 1
    haelt := []
    produziert := []
    boden := none }

def pwO : Orakel pwD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

def pwR : ∀ f : pwD.Fn, World pwD → Env pwD (pwD.params f) → RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- One integer variable `x` in `0 .. 100`. -/
def pwCtx : Ctx := [.int 0 100]

theorem pwHw : pwV.schreibt () = true := rfl
theorem pwHL : darf pwD () [] := fun _ h => False.elim (List.not_mem_nil h)
theorem pwHΛ : ([] : List (Res pwD)).Perm pwV.ende := List.Perm.refl _

/-- Row `0` and row `1` as indices of the table. -/
def pwIdx0 : Expr pwD pwCtx [] (.index (pwD.count ())) := .weiter (by decide) (by decide) (.lit 0)
def pwIdx1 : Expr pwD pwCtx [] (.index (pwD.count ())) := .weiter (by decide) (by decide) (.lit 1)

/-- `x + 5`, widened to the field type: a VARIABLE operand. -/
def pwWert0 : Expr pwD pwCtx [] (pwD.typ () ()) :=
  .weiter (lo := 0 + 5) (hi := 100 + 5) (by decide) (by decide) (.add (.var .hier) (.lit 5))

/-- `2 * 3`, widened: a CONSTANT the lowering refuses (no multiply) and
    the optimiser folds. -/
def pwWert1 : Expr pwD pwCtx [] (pwD.typ () ()) :=
  .weiter (lo := 6) (hi := 6) (by decide) (by decide) (.mul (.lit 2) (.lit 3))

/-- The check `x < 50`. -/
def pwCheck : Expr pwD pwCtx [] .bool := .lt (.var .hier) (.lit 50)

/-- THE SOURCE PROGRAM:
    `T[0].f = x + 5; check x < 50 else reason 0; T[1].f = 2 * 3;` -/
def pwSrc : Block pwD pwV false pwCtx [] [] :=
  .cons (.assignSlot () () pwIdx0 pwWert0 pwHw pwHL)
    (.pruefung pwCheck (.retGrund ⟨0, by decide⟩ pwHΛ)
      (.cons (.assignSlot () () pwIdx1 pwWert1 pwHw pwHL) .nil))

/-- The optimiser certificate: fold the value of the second assignment
    (`rest` past the first statement, `rest` past the check, `head`). -/
def pwCerts : List (PassKind × BlockCert) :=
  [(.fold, .rest (.rest (.head (.assignSlotValue .foldInt))))]

/-- Target configuration: `x` in `r10`; `rax`/`rcx` working, `rbx` the
    address register; code at 4096; refusal exits from 12288. -/
def pwCfg : PipeCfg :=
  { regs := [.r10], dst := .rax, tmp := .rcx, adr := .rbx, codeBase := 4096,
    exitBase := 12288 }

/-- Slot layout: row 0 at 8192, row 1 at 8200. -/
def pwL : Layout pwD where
  loc := fun _ k _ => if k = 0 then some 8192 else if k = 1 then some 8200 else none

/-- THE UNTRUSTED CANDIDATE, written out as a producer would emit it. -/
def pwProg : List Befehl :=
  [ .movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 8192), .store64 .rbx .rax (BitVec.ofNat 32 0),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (BitVec.ofNat 32 8137),
    .movImm64 .rax (intWort 6), .movImm64 .rbx (natAdresse 8200),
    .store64 .rbx .rax (BitVec.ofNat 32 0) ]

def pwBytes : List Byte := encodeAll pwProg

/-! ## 2. The whole chain, by computation -/

/-- The optimiser ACCEPTS the certificate and actually rewrites. -/
theorem pw_optimiser_akzeptiert : (applyPipeline pwCerts pwSrc).isSome = true := by decide

/-- Without the optimiser the program is NOT lowerable (`2 * 3` has no
    pilot lowering): the fold is essential, not decorative. -/
theorem pw_ohne_optimiser_verweigert : compile pwCfg pwL [] pwSrc = none := by decide

/-- The compiler produces exactly the candidate. -/
theorem pw_compile : compile pwCfg pwL pwCerts pwSrc = some pwBytes := by decide

/-- THE VALIDATOR ACCEPTS the untrusted candidate, by computation. -/
theorem pw_validate : validate pwCfg pwL pwCerts pwSrc pwBytes = true := by decide

/-- The candidate decodes back to the instruction list (codec round trip). -/
theorem pw_decode : decodeAll pwBytes.length pwBytes = some pwProg := by decide

theorem pw_laenge : pwBytes.length = 82 := by decide

/-! ## 3. Start states, source world and representation -/

/-- The memory: code at `[4096, 4178)` (execute only), the two slots at
    `[8192, 8208)` holding 7 and 9 (read/write, never execute). -/
def pwMemBytes (a : Adresse) : Byte :=
  if 4096 ≤ a.toNat ∧ a.toNat < 4096 + pwBytes.length then pwBytes.getD (a.toNat - 4096) 0
  else if 8192 ≤ a.toNat ∧ a.toNat < 8200 then wortByte (BitVec.ofNat 64 7) (a.toNat - 8192)
  else if 8200 ≤ a.toNat ∧ a.toNat < 8208 then wortByte (BitVec.ofNat 64 9) (a.toNat - 8200)
  else 0

def pwCode (a : Adresse) : Bool := decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + pwBytes.length)

def pwDaten (a : Adresse) : Bool := decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

def pwMem : Speicher :=
  { bytes := pwMemBytes, lesbar := pwDaten, schreibbar := pwDaten, ausfuehrbar := pwCode }

/-- Registers: `x` in `r10`, everything else zero. -/
def pwReg (x : Int) : Register → Wort := fun q => if q = .r10 then intWort x else 0

def pwStart (x : Int) : Zustand :=
  { register := pwReg x, flags := witnessFlags, rip := natAdresse 4096, speicher := pwMem }

/-- The source world: row 0 holds 7, row 1 holds 9. -/
def pwSigma : World pwD where
  slots := fun t k f => by
    cases t; cases f
    exact if k = 0 then (⟨7, by decide, by decide⟩ : Zahl 0 1000)
      else if k = 1 then (⟨9, by decide, by decide⟩ : Zahl 0 1000)
      else (⟨0, by decide, by decide⟩ : Zahl 0 1000)
  globs := fun g => nomatch g
  spur := []

/-- The environment `x = 30` (check passes) and `x = 70` (check fails). -/
def pwEnv30 : Env pwD pwCtx := .cons (⟨30, by decide, by decide⟩ : Zahl 0 100) .nil
def pwEnv70 : Env pwD pwCtx := .cons (⟨70, by decide, by decide⟩ : Zahl 0 100) .nil

/-- A code region from a range predicate (witness helper). -/
theorem codeAt_von (m : Speicher) (base : Nat) (flat : List Byte)
    (hw : base + flat.length < 2 ^ 64)
    (h : ∀ a : Adresse, base ≤ a.toNat → a.toNat < base + flat.length →
      m.ausfuehrbar a = true ∧ m.schreibbar a = false ∧ m.bytes a = flat.getD (a.toNat - base) 0) :
    CodeAt m (natAdresse base) flat := by
  intro i b hi
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
  have hn : (addrOff (natAdresse base) i).toNat = base + i := by
    rw [addrOff_natAdresse]
    unfold natAdresse
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨h1, h2, h3⟩ := h (addrOff (natAdresse base) i) (by omega) (by omega)
  refine ⟨h1, h2, ?_⟩
  rw [h3, hn, show base + i - base = i by omega, List.getD_eq_getElem?_getD, hi]
  rfl

theorem pw_code : CodeAt pwMem (natAdresse 4096) pwBytes := by
  apply codeAt_von pwMem 4096 pwBytes (by rw [pw_laenge]; decide)
  intro a h1 h2
  have hd : ¬ (8192 ≤ a.toNat ∧ a.toNat < 8208) := by rw [pw_laenge] at h2; omega
  simp only [pwMem, pwCode, pwDaten, pwMemBytes, decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨⟨h1, h2⟩, hd, by rw [if_pos ⟨h1, h2⟩]⟩

theorem pw_layoutSep : LayoutSep pwL := by
  intro t1 k1 f1 a1 t2 k2 f2 a2 h1 h2
  cases t1; cases t2; cases f1; cases f2
  simp only [pwL] at h1 h2
  by_cases e1 : k1 = 0
  · rw [if_pos e1] at h1
    by_cases e2 : k2 = 0
    · exact Or.inl ⟨rfl, by rw [e1, e2], HEq.rfl⟩
    · rw [if_neg e2] at h2
      by_cases e3 : k2 = 1
      · rw [if_pos e3] at h2
        cases h1; cases h2
        exact Or.inr (Or.inl (by decide))
      · rw [if_neg e3] at h2; cases h2
  · rw [if_neg e1] at h1
    by_cases e4 : k1 = 1
    · rw [if_pos e4] at h1
      by_cases e2 : k2 = 0
      · rw [if_pos e2] at h2
        cases h1; cases h2
        exact Or.inr (Or.inr (by decide))
      · rw [if_neg e2] at h2
        by_cases e3 : k2 = 1
        · exact Or.inl ⟨rfl, by rw [e4, e3], HEq.rfl⟩
        · rw [if_neg e3] at h2; cases h2
    · rw [if_neg e4] at h1; cases h1

theorem pw_worldRep : WorldRep pwL pwMem pwSigma := by
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

theorem pw_envRepr30 : EnvRepr pwEnv30 (pwStart 30).register (abbOf pwCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

theorem pw_envRepr70 : EnvRepr pwEnv70 (pwStart 70).register (abbOf pwCfg) := by
  intro lo hi x
  cases x with
  | hier => rfl
  | dort x => exact nomatch x

/-! ## 4. The source runs (REAL `execBlock` of the ORIGINAL block) -/

/-- `x = 30`: both stores happen, rows become 35 and 6. -/
theorem pw_quelle30 : ∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
    (σ'.slots () 0 ()).n = 35 ∧ (σ'.slots () 1 ()).n = 6 :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- `x = 70`: the first store happens, the check fails with reason 0. -/
theorem pw_quelle70 : ∃ σ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' ⟨0, by decide⟩ ∧
    (σ'.slots () 0 ()).n = 75 ∧ (σ'.slots () 1 ()).n = 9 :=
  ⟨_, rfl, rfl, rfl⟩

/-- The source world before the run. -/
theorem pw_quelle_vorher : (pwSigma.slots () 0 ()).n = 7 ∧ (pwSigma.slots () 1 ()).n = 9 :=
  ⟨rfl, rfl⟩

/-! ## 5. The fetched byte runs, by computation -/

/-- `x = 30`: twelve fetched steps reach the end of the code with the
    slot bytes 35 and 6. -/
theorem pw_bytes30 :
    ausgangRip (laufBytes 12 (pwStart 30)) = some (natAdresse 4178) ∧
      ausgangByte (natAdresse 8192) (laufBytes 12 (pwStart 30)) = some (natByte 35) ∧
      ausgangByte (natAdresse 8200) (laufBytes 12 (pwStart 30)) = some (natByte 6) := by
  decide

/-- `x = 70`: nine fetched steps reach the refusal exit 12288 with row 0
    already 75 and row 1 untouched. -/
theorem pw_bytes70 :
    ausgangRip (laufBytes 9 (pwStart 70)) = some (natAdresse 12288) ∧
      ausgangByte (natAdresse 8192) (laufBytes 9 (pwStart 70)) = some (natByte 75) ∧
      ausgangByte (natAdresse 8200) (laufBytes 9 (pwStart 70)) = some (natByte 9) := by
  decide

/-- The target memory before the run. -/
theorem pw_bytes_vorher :
    pwMem.bytes (natAdresse 8192) = natByte 7 ∧ pwMem.bytes (natAdresse 8200) = natByte 9 := by
  decide

/-! ## 6. The joint witnesses of the closing theorems -/

/-- The witness slot type equation. -/
theorem pwHT : pwD.typ () () = .int 0 1000 := rfl

/-- A represented slot reads back its source number as a word. -/
theorem read_von_worldRep (m : Speicher) (σ : World pwD) (k : Int) (a : Nat)
    (hW : WorldRep pwL m σ) (hloc : pwL.loc () k () = some a) (n : Int)
    (hn : (σ.slots () k ()).n = n) :
    read64 m (natAdresse a) = some (BitVec.ofNat 64 n.toNat) := by
  obtain ⟨-, -, -, hrep⟩ := hW () k () a hloc
  have := hrep 0 1000 pwHT
  unfold RepSlot zahlWort at this
  rw [this]
  show some (BitVec.ofNat 64 (σ.slots () k ()).n.toNat) = _
  rw [hn]

/-- JOINT WITNESS for `pipeline_correct`: every premise holds jointly on one
    program that writes two slots (one from a variable, one from a constant
    the optimiser folds) and passes a check; the source run changes memory
    (row 0: 7 -> 35, row 1: 9 -> 6); the closing theorem then delivers a
    fetched run ending at the end of the code whose memory reads 35 and 6. -/
theorem pipeline_correct_zeuge :
    ∃ (σ' : World pwD) (ρ' : Env pwD pwCtx),
      validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧ LayoutSep pwL ∧
      CodeAt (pwStart 30).speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      (pwStart 30).rip = natAdresse pwCfg.codeBase ∧
      WorldRep pwL (pwStart 30).speicher pwSigma ∧
      EnvRepr pwEnv30 (pwStart 30).register (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ' ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 35 ∧
      (pwSigma.slots () 1 ()).n = 9 ∧ (σ'.slots () 1 ()).n = 6 ∧
      ∃ n s', laufBytes n (pwStart 30) = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.codeBase + pwBytes.length) ∧
        WorldRep pwL s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf pwCfg) ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 35) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 6) := by
  obtain ⟨σ', ρ', hsrc, h0, h1⟩ := pw_quelle30
  obtain ⟨n, s', hrun, hrip, hW, hE⟩ := pipeline_correct pwCfg pwL pwCerts pwSrc pwBytes
    pw_validate pw_layoutSep pwO 0 pwR pwSigma pwEnv30 (pwStart 30) pw_code rfl pw_worldRep
    pw_envRepr30 σ' ρ' hsrc
  refine ⟨σ', ρ', pw_validate, pw_layoutSep, pw_code, rfl, pw_worldRep, pw_envRepr30, hsrc,
    rfl, h0, rfl, h1, n, s', hrun, hrip, hW, hE, ?_, ?_⟩
  · exact read_von_worldRep _ σ' 0 8192 hW rfl 35 h0
  · exact read_von_worldRep _ σ' 1 8200 hW rfl 6 h1

/-- JOINT WITNESS for `pipeline_refuses`: with `x = 70` the check fails
    AFTER the first store; the fetched run reaches the refusal exit of
    reason 0 with row 0 already changed to 75 and row 1 untouched. -/
theorem pipeline_refuses_zeuge :
    ∃ (σ' : World pwD),
      validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧ LayoutSep pwL ∧
      CodeAt (pwStart 70).speicher (natAdresse pwCfg.codeBase) pwBytes ∧
      (pwStart 70).rip = natAdresse pwCfg.codeBase ∧
      WorldRep pwL (pwStart 70).speicher pwSigma ∧
      EnvRepr pwEnv70 (pwStart 70).register (abbOf pwCfg) ∧
      execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' ⟨0, by decide⟩ ∧
      (pwSigma.slots () 0 ()).n = 7 ∧ (σ'.slots () 0 ()).n = 75 ∧
      ∃ n s', laufBytes n (pwStart 70) = .weiter s' ∧
        s'.rip = natAdresse (pwCfg.exitBase + 0) ∧ WorldRep pwL s'.speicher σ' ∧
        read64 s'.speicher (natAdresse 8192) = some (BitVec.ofNat 64 75) ∧
        read64 s'.speicher (natAdresse 8200) = some (BitVec.ofNat 64 9) := by
  obtain ⟨σ', hsrc, h0, h1⟩ := pw_quelle70
  obtain ⟨n, s', hrun, hrip, hW⟩ := pipeline_refuses pwCfg pwL pwCerts pwSrc pwBytes
    pw_validate pw_layoutSep pwO 0 pwR pwSigma pwEnv70 (pwStart 70) pw_code rfl pw_worldRep
    pw_envRepr70 σ' ⟨0, by decide⟩ hsrc
  refine ⟨σ', pw_validate, pw_layoutSep, pw_code, rfl, pw_worldRep, pw_envRepr70, hsrc, rfl, h0,
    n, s', hrun, hrip, hW, ?_, ?_⟩
  · exact read_von_worldRep _ σ' 0 8192 hW rfl 75 h0
  · exact read_von_worldRep _ σ' 1 8200 hW rfl 9 h1

/-- JOINT WITNESS for `pipeline_ausgang`: both outcome kinds are reached
    by the same accepted program. -/
theorem pipeline_ausgang_zeuge :
    validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧
      ((∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ') ∨
        (∃ σ' r, execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .grund σ' r)) ∧
      ((∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .ok σ' ρ') ∨
        (∃ σ' r, execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' r)) ∧
      (∃ σ' ρ', execBlock pwO 0 pwR pwSrc pwSigma pwEnv30 = .ok σ' ρ') ∧
      (∃ σ' r, execBlock pwO 0 pwR pwSrc pwSigma pwEnv70 = .grund σ' r) := by
  obtain ⟨σ1, ρ1, h1, -, -⟩ := pw_quelle30
  obtain ⟨σ2, h2, -, -⟩ := pw_quelle70
  exact ⟨pw_validate,
    pipeline_ausgang pwCfg pwL pwCerts pwSrc pwBytes pw_validate pwO 0 pwR pwSigma pwEnv30,
    pipeline_ausgang pwCfg pwL pwCerts pwSrc pwBytes pw_validate pwO 0 pwR pwSigma pwEnv70,
    ⟨σ1, ρ1, h1⟩, ⟨σ2, _, h2⟩⟩

/-- The lowered optimised block (the program the validator recomputes). -/
theorem pw_senkBlock : senkBlock pwCfg pwL 0 (optimise pwCerts pwSrc) = some pwProg := by decide

theorem pw_cfgOk : cfgOk pwCfg = true := by decide

/-- JOINT WITNESS for `senkBlock_korrekt` (on the OPTIMISED block) and
    `senkBlock_ausgang`. -/
theorem senkBlock_korrekt_zeuge :
    ∃ n s', senkBlock pwCfg pwL ([] : List Byte).length (optimise pwCerts pwSrc) = some pwProg ∧
      laufBytes n (pwStart 30) = .weiter s' ∧
      Entspricht pwCfg pwL (addrOff (natAdresse pwCfg.codeBase)
        (([] : List Byte).length + (encodeAll pwProg).length))
        (execBlock pwO 0 pwR (optimise pwCerts pwSrc) pwSigma pwEnv30) s' ∧
      ((∃ σ' ρ', execBlock pwO 0 pwR (optimise pwCerts pwSrc) pwSigma pwEnv30 = .ok σ' ρ') ∨
        (∃ σ' r, execBlock pwO 0 pwR (optimise pwCerts pwSrc) pwSigma pwEnv30 = .grund σ' r)) := by
  obtain ⟨n, s', hrun, hent⟩ := senkBlock_korrekt pwCfg pwL pw_cfgOk pw_layoutSep pwO 0 pwR
    pwBytes (optimise pwCerts pwSrc) [] [] pwProg pw_senkBlock pwSigma pwEnv30 (pwStart 30)
    pw_code (by simp [pwBytes]) rfl pw_worldRep pw_envRepr30
  exact ⟨n, s', pw_senkBlock, hrun, hent,
    senkBlock_ausgang pwCfg pwL pwO 0 pwR _ 0 pwProg pw_senkBlock pwSigma pwEnv30⟩

/-- JOINT WITNESS for `validate_sound`, `validate_compile`, `optimise_sound`
    and `decodeAll_encodeAll` on the witness program. -/
theorem validate_zeuge :
    (∃ prog, cfgOk pwCfg = true ∧ senkBlock pwCfg pwL 0 (optimise pwCerts pwSrc) = some prog ∧
      pwBytes = encodeAll prog ∧ decodeAll pwBytes.length pwBytes = some prog ∧
      compile pwCfg pwL pwCerts pwSrc = some pwBytes) ∧
    validate pwCfg pwL pwCerts pwSrc pwBytes = true ∧
    BlockEquiv pwSrc (optimise pwCerts pwSrc) ∧
    decodeAll pwProg.length (encodeAll pwProg) = some pwProg :=
  ⟨validate_sound pwCfg pwL pwCerts pwSrc pwBytes pw_validate,
   validate_compile pwCfg pwL pwCerts pwSrc pwBytes pw_compile (by decide),
   optimise_sound pwCerts pwSrc,
   decodeAll_encodeAll pwProg _ (Nat.le_refl _)⟩

/-! ## 7. Poison probes: every one is REFUSED -/

/-- TAMPERED BYTE: one changed byte of the candidate is refused. -/
theorem gift_byte : validate pwCfg pwL pwCerts pwSrc (pwBytes.set 1 (natByte 0)) = false := by
  decide

/-- TAMPERED IMMEDIATE: a candidate that claims the fold gave 7 instead of
    6 (a wrong optimisation) is refused. -/
def pwProgFalschFold : List Befehl :=
  [ .movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 8192), .store64 .rbx .rax (BitVec.ofNat 32 0),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (BitVec.ofNat 32 8137),
    .movImm64 .rax (intWort 7), .movImm64 .rbx (natAdresse 8200),
    .store64 .rbx .rax (BitVec.ofNat 32 0) ]

theorem gift_falscher_fold :
    validate pwCfg pwL pwCerts pwSrc (encodeAll pwProgFalschFold) = false := by decide

/-- TAMPERED JUMP: a jump displacement that misses the refusal exit. -/
def pwProgFalschSprung : List Befehl :=
  [ .movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 8192), .store64 .rbx .rax (BitVec.ofNat 32 0),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (BitVec.ofNat 32 0),
    .movImm64 .rax (intWort 6), .movImm64 .rbx (natAdresse 8200),
    .store64 .rbx .rax (BitVec.ofNat 32 0) ]

theorem gift_falscher_sprung :
    validate pwCfg pwL pwCerts pwSrc (encodeAll pwProgFalschSprung) = false := by decide

/-- WRONG CERTIFICATE (the rule does not apply: `x + 5` is no constant):
    the optimiser refuses, the conservative route keeps `2 * 3`, which has
    no lowering -- nothing is produced and the candidate is refused. -/
def pwCertsFalsch : List (PassKind × BlockCert) :=
  [(.fold, .head (.assignSlotValue .foldInt))]

theorem gift_falsches_zertifikat :
    applyPipeline pwCertsFalsch pwSrc = none ∧ compile pwCfg pwL pwCertsFalsch pwSrc = none ∧
      validate pwCfg pwL pwCertsFalsch pwSrc pwBytes = false := by decide

/-- WRONG PASS: the right rule filed under the wrong pass is refused. -/
def pwCertsFalschePass : List (PassKind × BlockCert) :=
  [(.strength, .rest (.rest (.head (.assignSlotValue .foldInt))))]

theorem gift_falscher_pass :
    applyPipeline pwCertsFalschePass pwSrc = none ∧
      validate pwCfg pwL pwCertsFalschePass pwSrc pwBytes = false := by decide

/-- UNSUPPORTED STATEMENT (a variable index: no static slot address). -/
def pwSrcVarIdx : Block pwD pwV false [.int 0 1] [] [] :=
  .cons (.assignSlot () () (.var .hier)
    (.weiter (lo := 3) (hi := 3) (by decide) (by decide) (.lit 3)) pwHw pwHL) .nil

/-- UNSUPPORTED BLOCK FORM (a `bind`). -/
def pwSrcBind : Block pwD pwV false pwCtx [] [] :=
  .bind (.lit 1) .nil

/-- A CHECK THAT DOES NOT FIT THE REGISTERS (a `<` over a non-atom with
    the original configuration, whose only scratch register is `tmp`):
    refused, not guessed. Since the widening it is a scratch-exhaustion
    refusal: with one more scratch register the same check is lowered
    (`pw_tiefeBed_mit_frei`). -/
def pwSrcTiefeBed : Block pwD pwV false pwCtx [] [] :=
  .pruefung (.lt (.add (.var .hier) (.lit 1)) (.lit 50)) (.retGrund ⟨0, by decide⟩ pwHΛ) .nil

theorem gift_nicht_unterstuetzt :
    compile pwCfg pwL [] pwSrcVarIdx = none ∧ compile pwCfg pwL [] pwSrcBind = none ∧
      compile pwCfg pwL [] pwSrcTiefeBed = none ∧
      validate pwCfg pwL [] pwSrcVarIdx [] = false ∧
      validate pwCfg pwL [] pwSrcBind [] = false := by decide

/-- The same deep check IS lowered once the configuration lends one more
    scratch register (`frei = [rdx]`). -/
theorem pw_tiefeBed_mit_frei :
    (compile { pwCfg with frei := [.rdx] } pwL [] pwSrcTiefeBed).isSome = true := by decide

/-- REGISTER CLASH: the value register is the register of `x`. -/
def pwCfgKlash : PipeCfg := { pwCfg with dst := .r10 }

/-- STACK CLASH: the scratch register is `rsp`. -/
def pwCfgRsp : PipeCfg := { pwCfg with tmp := .rsp }

theorem gift_register :
    cfgOk pwCfgKlash = false ∧ validate pwCfgKlash pwL pwCerts pwSrc pwBytes = false ∧
      cfgOk pwCfgRsp = false ∧ validate pwCfgRsp pwL pwCerts pwSrc pwBytes = false := by
  decide

/-- CODE/DATA OVERLAP: row 0 placed inside the code region. The compiler
    still produces bytes for it -- the validator refuses them. -/
def pwLUeberlapp : Layout pwD where
  loc := fun _ k _ => if k = 0 then some 4100 else if k = 1 then some 8200 else none

def pwBytesUeberlapp : List Byte :=
  encodeAll
  [ .movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx,
    .movImm64 .rbx (natAdresse 4100), .store64 .rbx .rax (BitVec.ofNat 32 0),
    .movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx,
    .jumpIf32 .ge (BitVec.ofNat 32 8137),
    .movImm64 .rax (intWort 6), .movImm64 .rbx (natAdresse 8200),
    .store64 .rbx .rax (BitVec.ofNat 32 0) ]

theorem gift_ueberlapp :
    compile pwCfg pwLUeberlapp pwCerts pwSrc = some pwBytesUeberlapp ∧
      validate pwCfg pwLUeberlapp pwCerts pwSrc pwBytesUeberlapp = false := by decide

/-- UNREACHABLE EXIT: a refusal exit the 32-bit displacement cannot reach
    is refused by the lowering itself. -/
def pwCfgFern : PipeCfg := { pwCfg with exitBase := 2 ^ 40 }

theorem gift_ferner_ausgang : compile pwCfgFern pwL pwCerts pwSrc = none := by decide

/-- FETCHED REFUSAL: the tampered candidate placed in memory stops the
    byte run (the decoder refuses the forged opcode). -/
def pwMemFalsch : Speicher :=
  { pwMem with bytes := fun a => if a = natAdresse 4097 then natByte 0 else pwMem.bytes a }

theorem gift_lauf_verweigert :
    ausgangRip (byteschritt { pwStart 30 with speicher := pwMemFalsch }) = none := by decide

/-! ## 8. Joint witnesses of the generic helper theorems

    Every helper of `Pipeline.lean` whose premises range over syntax or
    states, instantiated jointly on the witness data above; the run
    witnesses change memory (the first chunk stores 35 at row 0). -/

/-- The first lowered chunk (`T[0].f = x + 5`). -/
def pwChunk : List Befehl := pwProg.take 5

/-- The candidate starts with the first chunk. -/
theorem pw_split : pwBytes = [] ++ encodeAll pwChunk ++ encodeAll (pwProg.drop 5) := by decide

theorem pw_chunk_gerade : pwChunk.all gerade = true := by decide

theorem pw_chunk_lauft : (lauf (pwChunk.map kanon) (pwStart 30)).isSome = true := by decide

theorem lauf_zu_laufBytes_zeuge :
    ∃ s', lauf (pwChunk.map kanon) (pwStart 30) = some s' ∧
      CodeAt (pwStart 30).speicher (natAdresse 4096) pwBytes ∧
      laufBytes pwChunk.length (pwStart 30) = .weiter s' ∧
      s'.rip = addrOff (natAdresse 4096) (([] : List Byte).length + (encodeAll pwChunk).length) ∧
      CodeAt s'.speicher (natAdresse 4096) pwBytes ∧
      s'.speicher.bytes (natAdresse 8192) = natByte 35 ∧
      (pwStart 30).speicher.bytes (natAdresse 8192) = natByte 7 := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp pw_chunk_lauft
  obtain ⟨hb, hr, hc, -, -⟩ := lauf_zu_laufBytes (natAdresse 4096) pwBytes pwChunk [] _
    (pwStart 30) s' pw_chunk_gerade hs' pw_code pw_split rfl
  have h35 : ausgangByte (natAdresse 8192) (laufBytes pwChunk.length (pwStart 30)) =
      some (natByte 35) := by decide
  rw [hb] at h35
  exact ⟨s', hs', pw_code, hb, hr, hc, Option.some.inj h35, by decide⟩

theorem byteschritt_im_code_zeuge :
    CodeAt (pwStart 30).speicher (natAdresse 4096) pwBytes ∧
      pwBytes = [] ++ encode (.movReg64 .rax .r10) ++ encodeAll (pwProg.drop 1) ∧
      byteschritt (pwStart 30) = (match schritt (kanon (.movReg64 .rax .r10)) (pwStart 30) with
        | none => .verweigert
        | some s' => .weiter s') ∧
      ausgangReg .rax (byteschritt (pwStart 30)) = some (intWort 30) := by
  have hsplit : pwBytes = [] ++ encode (.movReg64 .rax .r10) ++ encodeAll (pwProg.drop 1) := by
    decide
  exact ⟨pw_code, hsplit,
    byteschritt_im_code (pwStart 30) _ pwBytes [] _ _ pw_code hsplit rfl, by decide⟩

theorem holeFetchAux_praefix_zeuge :
    (∀ (j : Nat) (b : Byte), (encode (.movReg64 .rax .r10))[j]? = some b →
      pwMem.ausfuehrbar (addrOff (natAdresse 4096) (0 + j)) = true ∧
        pwMem.bytes (addrOff (natAdresse 4096) (0 + j)) = b) ∧
      holeFetchAux pwMem (natAdresse 4096) 0 15 = encode (.movReg64 .rax .r10) ++
        holeFetchAux pwMem (natAdresse 4096) 3 12 ∧
      ausfuehrbarN pwMem (natAdresse 4096) 3 = true := by
  have hp : ∀ (j : Nat) (b : Byte), (encode (.movReg64 .rax .r10))[j]? = some b →
      pwMem.ausfuehrbar (addrOff (natAdresse 4096) (0 + j)) = true ∧
        pwMem.bytes (addrOff (natAdresse 4096) (0 + j)) = b := by
    intro j b hj
    have hf : pwBytes[j]? = some b := by
      rw [show pwBytes = encode (.movReg64 .rax .r10) ++ encodeAll (pwProg.drop 1) by decide]
      obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.mp hj
      rw [List.getElem?_append_left hl]
      exact hj
    obtain ⟨h1, -, h3⟩ := pw_code j b hf
    rw [Nat.zero_add]
    exact ⟨h1, h3⟩
  refine ⟨hp, holeFetchAux_praefix pwMem _ _ 0 15 (by decide) hp, ?_⟩
  exact ausfuehrbarN_von pwMem _ 3 (fun j hj => by
    have hx : (encode (.movReg64 .rax .r10))[j]? = some ((encode (.movReg64 .rax .r10))[j]'(by
      have h3 : (encode (.movReg64 .rax .r10)).length = 3 := by decide
      omega)) := List.getElem?_eq_getElem _
    have := (hp j _ hx).1
    rwa [Nat.zero_add] at this)

/-- A store into row 0 of the witness memory. -/
def pwMem35 : Speicher :=
  { pwMem with bytes := writeBytes pwMem (natAdresse 8192) (BitVec.ofNat 64 35) }

theorem pw_write35 : write64 pwMem (natAdresse 8192) (BitVec.ofNat 64 35) = some pwMem35 := by
  unfold write64
  rw [if_pos (by decide)]
  rfl

theorem write64_zeuge :
    write64 pwMem (natAdresse 8192) (BitVec.ofNat 64 35) = some pwMem35 ∧
      schreibbar8 pwMem (natAdresse 8192) = true ∧
      pwMem.schreibbar (addrOff (natAdresse 8192) 7) = true ∧
      pwMem.schreibbar (natAdresse 4096) = false ∧
      pwMem35.bytes (natAdresse 4096) = pwMem.bytes (natAdresse 4096) ∧
      pwMem35.bytes (natAdresse 8192) ≠ pwMem.bytes (natAdresse 8192) := by
  have hs := write64_schreibbar _ _ _ _ pw_write35
  refine ⟨pw_write35, hs, schreibbar8_byte _ _ hs 7 (by decide), by decide,
    write64_nicht_schreibbar _ _ _ _ pw_write35 _ (by decide), by decide⟩

/-- One straight store step on the witness state. -/
def pwStoreReg : Register → Wort := fun q =>
  if q = .rbx then natAdresse 8192 else if q = .rax then BitVec.ofNat 64 35 else 0

def pwStoreZ : Zustand := { pwStart 30 with register := pwStoreReg }

theorem pw_store_lauft :
    (schritt (kanon (.store64 .rbx .rax (BitVec.ofNat 32 0))) pwStoreZ).isSome = true := by decide

theorem schritt_gerade_zeuge :
    ∃ s', schritt (kanon (.store64 .rbx .rax (BitVec.ofNat 32 0))) pwStoreZ = some s' ∧
      s'.rip = addrOff pwStoreZ.rip (encode (.store64 .rbx .rax (BitVec.ofNat 32 0))).length ∧
      s'.speicher.ausfuehrbar = pwStoreZ.speicher.ausfuehrbar ∧
      CodeAt s'.speicher (natAdresse 4096) pwBytes ∧
      s'.speicher.bytes (natAdresse 8192) = natByte 35 := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp pw_store_lauft
  obtain ⟨hr, hx, hs, -, hb⟩ := schritt_gerade _ pwStoreZ s' rfl hs'
  have h35 : (match schritt (kanon (.store64 .rbx .rax (BitVec.ofNat 32 0))) pwStoreZ with
      | some s => some (s.speicher.bytes (natAdresse 8192)) | none => none) = some (natByte 35) := by
    decide
  rw [hs'] at h35
  exact ⟨s', hs', hr, hx, codeAt_erhalten _ _ _ _ pw_code hx hs hb, Option.some.inj h35⟩

theorem laufBytes_add_zeuge :
    ∃ s1, laufBytes 5 (pwStart 30) = .weiter s1 ∧ laufBytes (5 + 7) (pwStart 30) = laufBytes 7 s1 ∧
      ausgangByte (natAdresse 8192) (laufBytes 7 s1) = some (natByte 35) := by
  have h5 : (match laufBytes 5 (pwStart 30) with | .weiter _ => true | .verweigert => false) = true := by
    decide
  cases hb : laufBytes 5 (pwStart 30) with
  | verweigert => rw [hb] at h5; cases h5
  | weiter s1 =>
    have hadd := laufBytes_add 5 7 _ _ hb
    refine ⟨s1, rfl, hadd, ?_⟩
    rw [← hadd]
    decide

theorem worldRep_store_zeuge :
    LayoutSep pwL ∧ WorldRep pwL pwMem pwSigma ∧
      write64 pwMem (natAdresse 8192)
        (zahlWort (cast (congrArg (Wert pwD) pwHT) (⟨35, by decide, by decide⟩ : Zahl 0 1000) :
          Wert pwD (.int 0 1000))) = some pwMem35 ∧
      WorldRep pwL pwMem35 (pwSigma.schreibSlot () [] 0 () (⟨35, by decide, by decide⟩ : Zahl 0 1000)) ∧
      ((pwSigma.schreibSlot () [] 0 () (⟨35, by decide, by decide⟩ : Zahl 0 1000)).slots () 0 ()).n = 35 :=
  ⟨pw_layoutSep, pw_worldRep, pw_write35,
    worldRep_store pwL pw_layoutSep pwMem pwMem35 pwSigma () 0 () 8192 rfl pw_worldRep 0 1000 pwHT
      (⟨35, by decide, by decide⟩ : Zahl 0 1000) pw_write35 [], rfl⟩

theorem repOk_zeuge :
    repOk (pwD.typ () ()) 8192 8 0 = true ∧
      (∃ lo hi, pwD.typ () () = .int lo hi ∧ 0 ≤ lo ∧ hi < 2 ^ 64 ∧ 8192 + 8 ≤ 2 ^ 64) ∧
      OhneUmbruch (natAdresse 8192) ∧ (natAdresse 8192).toNat = 8192 :=
  ⟨by decide, repOk_int _ 8192 (by decide), natAdresse_ohneUmbruch 8192 (by decide),
    natAdresse_toNat 8192 (by decide)⟩

theorem cfg_zeuge :
    cfgOk pwCfg = true ∧ (abbOf pwCfg (Γ := pwCtx) _ .hier ∈ pwCfg.regs ∨
      abbOf pwCfg (Γ := pwCtx) _ .hier = .rsp) ∧
    (abbOf pwCfg (Γ := pwCtx) _ .hier ≠ pwCfg.dst ∧ abbOf pwCfg (Γ := pwCtx) _ .hier ≠ pwCfg.tmp ∧
      abbOf pwCfg (Γ := pwCtx) _ .hier ≠ pwCfg.adr) ∧
    (pwCfg.dst ≠ pwCfg.tmp ∧ pwCfg.dst ≠ pwCfg.adr ∧ pwCfg.tmp ≠ pwCfg.adr ∧
      pwCfg.dst ≠ .rsp ∧ pwCfg.tmp ≠ .rsp ∧ pwCfg.adr ≠ .rsp) ∧
    Frisch (abbOf pwCfg (Γ := pwCtx)) pwCfg.dst pwCfg.tmp ∧
    EnvRepr pwEnv30 (regSet (pwStart 30).register .rax 0) (abbOf pwCfg) :=
  ⟨pw_cfgOk, abbOf_mem pwCfg .hier, cfgOk_frei pwCfg pw_cfgOk .hier, cfgOk_regs pwCfg pw_cfgOk,
    cfgOk_frisch pwCfg pw_cfgOk,
    envRepr_fremd pwEnv30 _ _ _ pw_envRepr30 (fun _ x => regSet_fremd _ _ _ _
      (cfgOk_frei pwCfg pw_cfgOk x).1)⟩

theorem pw_senkWert0 : senkWert (abbOf pwCfg) pwWert0 .rax .rcx =
    some [.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx] := by decide

theorem pw_wert_lauft : (lauf ([Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 5),
    .addReg64 .rax .rcx].map kanon) (pwStart 30)).isSome = true := by decide

theorem senkWert_zeuge :
    IstWert (abbOf pwCfg) .rax .rcx pwWert0
        [.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx] ∧
      [Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx].all gerade = true ∧
      ∃ s', lauf ([Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 5),
          .addReg64 .rax .rcx].map kanon) (pwStart 30) = some s' ∧
        s'.register .rax = intWort (cast (congrArg (Wert pwD) pwHT)
          (eval pwSigma pwWert0 pwSigma pwEnv30) : Wert pwD (.int 0 1000)).n ∧
        s'.register .rax = intWort 35 := by
  obtain ⟨s', hrun, hval, -, -⟩ := senkWert_korrekt (abbOf pwCfg) pwWert0 pwHT .rax .rcx pwEnv30
    pwSigma pwSigma (pwStart 30) (cfgOk_frisch pwCfg pw_cfgOk) ⟨by decide, by decide⟩
    pw_envRepr30 _ pw_senkWert0
  refine ⟨istWert_von _ _ _ _ _ pw_senkWert0, senkWert_gerade _ _ _ _ _ pw_senkWert0, s', hrun,
    hval, ?_⟩
  rw [hval]
  rfl

theorem senkFrag_gerade_zeuge :
    senkFrag (abbOf pwCfg) (Expr.add (D := pwD) (Λ := []) (.var (Γ := pwCtx) .hier) (.lit 5))
        .rax .rcx = some [.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx] ∧
      senkAtom (abbOf pwCfg) (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) .rax =
        some [.movReg64 .rax .r10] ∧
      [Befehl.movReg64 .rax .r10].all gerade = true ∧
      [Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx].all gerade =
        true := by
  have h1 : senkFrag (abbOf pwCfg) (Expr.add (D := pwD) (Λ := []) (.var (Γ := pwCtx) .hier)
      (.lit 5)) .rax .rcx =
      some [.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx] := by decide
  have h2 : senkAtom (abbOf pwCfg) (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) .rax =
      some [.movReg64 .rax .r10] := by decide
  exact ⟨h1, h2, senkAtom_gerade _ _ _ _ h2, senkFrag_gerade _ _ _ _ _ h1⟩

theorem pw_senkBed : senkBed (abbOf pwCfg) pwCheck .rax .rcx =
    some ([.movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx], .ge) := by
  decide

theorem senkBed_zeuge :
    IstBed (abbOf pwCfg) .rax .rcx pwCheck
        [.movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx] .ge ∧
      (imSigned 0 100 = true ∧ imSigned 50 50 = true ∧ Bedingung.ge = .ge ∧
        ∃ pa pb, senkAtom (abbOf pwCfg) (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) .rax =
          some pa ∧ senkAtom (abbOf pwCfg) (Expr.lit (D := pwD) (Λ := []) (Γ := pwCtx) 50) .rcx =
          some pb ∧ [Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 50), .cmpReg64 .rax .rcx] =
            pa ++ pb ++ [.cmpReg64 .rax .rcx]) ∧
      ∃ s', lauf ([Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 50),
          .cmpReg64 .rax .rcx].map kanon) (pwStart 30) = some s' ∧
        boolOf .bool (eval pwSigma pwCheck pwSigma pwEnv30) = some (!bedingung .ge s'.flags) ∧
        bedingung .ge s'.flags = false ∧
        s'.flags = (sub64 (intWort 30) (intWort 50)).2 := by
  obtain ⟨-, s', hrun, -, -, hb⟩ := senkBed_korrekt (abbOf pwCfg) pwCheck .rax .rcx _ _ pw_senkBed
    pwEnv30 pwSigma pwSigma (pwStart 30) (cfgOk_frisch pwCfg pw_cfgOk) pw_envRepr30
  obtain ⟨s'', hrun', -, -, hfl⟩ := vergleich_lauf (abbOf pwCfg)
    (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) (.lit 50) .rax .rcx [.movReg64 .rax .r10]
    [.movImm64 .rcx (intWort 50)] (by decide) (by decide) pwEnv30 pwSigma pwSigma (pwStart 30) (cfgOk_frisch pwCfg pw_cfgOk) pw_envRepr30
  simp only [List.cons_append, List.nil_append] at hrun'
  rw [hrun] at hrun'
  cases hrun'
  have hv : boolOf .bool (eval pwSigma pwCheck pwSigma pwEnv30) = some true := rfl
  rw [hv] at hb
  have hg : bedingung .ge s'.flags = false := by
    cases h : bedingung .ge s'.flags
    · rfl
    · rw [h] at hb; cases hb
  exact ⟨istBed_von _ _ _ _ _ _ pw_senkBed,
    vergleich_inv _ (Expr.var (D := pwD) (Λ := []) (Γ := pwCtx) .hier) (.lit 50) .rax .rcx .ge .ge _
      (by decide),
    s', hrun, by rw [hv, hg]; rfl, hg, hfl⟩

theorem intWort_sint_zahl_zeuge :
    imSigned (-5) 5 = true ∧ sint (intWort (⟨-3, by decide, by decide⟩ : Zahl (-5) 5).n) = -3 :=
  ⟨by decide, intWort_sint_zahl _ (by decide)⟩

theorem istWahr_zeuge :
    istWahr (Expr.wahr (D := pwD) (Γ := pwCtx) (Λ := [])) = true ∧
      boolOf .bool (eval pwSigma (Expr.wahr (D := pwD) (Γ := pwCtx) (Λ := [])) pwSigma pwEnv30) =
        some true :=
  ⟨rfl, istWahr_wahr _ rfl pwSigma pwSigma pwEnv30⟩

theorem assign_lauf_zeuge :
    ∃ s', lauf (([Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 5), .addReg64 .rax .rcx] ++
        [Befehl.movImm64 pwCfg.adr (natAdresse 8192),
          Befehl.store64 pwCfg.adr pwCfg.dst (BitVec.ofNat 32 0)]).map kanon) (pwStart 30) = some s' ∧
      write64 (pwStart 30).speicher (natAdresse 8192)
        (zahlWort (cast (congrArg (Wert pwD) pwHT) (eval pwSigma pwWert0 pwSigma pwEnv30) :
          Wert pwD (.int 0 1000))) = some s'.speicher ∧
      EnvRepr pwEnv30 s'.register (abbOf pwCfg) ∧
      s'.speicher.bytes (natAdresse 8192) ≠ (pwStart 30).speicher.bytes (natAdresse 8192) := by
  obtain ⟨s', hrun, hw, hE⟩ := assign_lauf pwCfg pw_cfgOk pwWert0 pwHT (by decide) (by decide) _
    pw_senkWert0 8192 pwEnv30 pwSigma pwSigma (pwStart 30) pw_envRepr30 (by decide)
  refine ⟨s', hrun, hw, hE, ?_⟩
  have h35 : (match lauf (([Befehl.movReg64 .rax .r10, .movImm64 .rcx (intWort 5),
      .addReg64 .rax .rcx] ++ [Befehl.movImm64 pwCfg.adr (natAdresse 8192),
      Befehl.store64 pwCfg.adr pwCfg.dst (BitVec.ofNat 32 0)]).map kanon) (pwStart 30) with
      | some s => some (s.speicher.bytes (natAdresse 8192)) | none => none) = some (natByte 35) := by
    decide
  rw [hrun] at h35
  rw [Option.some.inj h35]
  decide

/-! ## 9. Probes for the word-level facts (no syntax premises) -/

/-- Signed less across the sign boundary and with overflow. -/
theorem probe_cmp :
    bedingung .l (sub64 (intWort (-1)) (intWort 1)).2 = true ∧
      bedingung .l (sub64 (intWort (2 ^ 63 - 1)) (intWort (-1))).2 = false ∧
      bedingung .l (sub64 (intWort (-(2 ^ 63))) (intWort 1)).2 = true ∧
      bedingung .ge (sub64 (intWort 30) (intWort 50)).2 = false ∧
      bedingung .g (sub64 (intWort 50) (intWort 30)).2 = true ∧
      bedingung .ne (sub64 (intWort 7) (intWort 7)).2 = false ∧
      (sub64 (intWort 7) (intWort 8)).2.zf = false := by
  decide

theorem probe_cmp_generisch :
    bedingung .l (sub64 (intWort (-(2 ^ 63))) (intWort 1)).2 =
      decide (sint (intWort (-(2 ^ 63))) < sint (intWort 1)) ∧
    bedingung .g (sub64 (intWort 3) (intWort 4)).2 = decide (sint (intWort 4) < sint (intWort 3)) ∧
    bedingung .ge (sub64 (intWort 3) (intWort 4)).2 = !decide (sint (intWort 3) < sint (intWort 4)) ∧
    bedingung .ne (sub64 (intWort 3) (intWort 4)).2 = !decide (intWort 3 = intWort 4) ∧
    (sub64 (intWort 3) (intWort 3)).2.zf = decide (intWort 3 = intWort 3) :=
  ⟨bedingung_l_sub64 _ _, bedingung_g_sub64 _ _, bedingung_ge_sub64 _ _, bedingung_ne_sub64 _ _,
    sub64_zf_eq _ _⟩

theorem probe_codec :
    encodeAll pwProg = pwBytes ∧ pwProg.length ≤ (encodeAll pwProg).length ∧
      addrOff (addrOff (natAdresse 4096) 33) 16 = addrOff (natAdresse 4096) 49 ∧
      addrOff (natAdresse 4096) 82 = natAdresse 4178 ∧
      ripNach (natAdresse 4096) 3 = addrOff (natAdresse 4096) 3 ∧
      (sint (intWort 5) = sint (intWort 5) ↔ intWort 5 = intWort 5) :=
  ⟨rfl, length_le_encodeAll _, addrOff_addrOff _ _ _, addrOff_natAdresse _ _, ripNach_addrOff _ _,
    sint_inj _ _⟩

/-! ## CUTS (what this witness file does NOT show)

   - One program, one layout, one configuration: the witnesses instantiate
     the generic theorems of `Pipeline.lean`; they prove nothing for other
     programs by themselves.
   - The candidate bytes are written out here by hand as an untrusted
     producer would emit them; no Rust producer is run or connected.
   - The fetched runs (`pw_bytes30`, `pw_bytes70`) are computed by
     `decide` over the model `Speicher`; no hardware is involved.
   - The refusal exit 12288 is an address the run reaches; what runs there
     is outside the witness (and outside the pipeline, see `Pipeline.lean`). -/

#print axioms pw_optimiser_akzeptiert
#print axioms pw_ohne_optimiser_verweigert
#print axioms pw_compile
#print axioms pw_validate
#print axioms pw_decode
#print axioms codeAt_von
#print axioms pw_code
#print axioms pw_layoutSep
#print axioms pw_worldRep
#print axioms pw_envRepr30
#print axioms pw_envRepr70
#print axioms pw_quelle30
#print axioms pw_quelle70
#print axioms pw_bytes30
#print axioms pw_bytes70
#print axioms read_von_worldRep
#print axioms pipeline_correct_zeuge
#print axioms pipeline_refuses_zeuge
#print axioms pipeline_ausgang_zeuge
#print axioms senkBlock_korrekt_zeuge
#print axioms validate_zeuge
#print axioms gift_byte
#print axioms gift_falscher_fold
#print axioms gift_falscher_sprung
#print axioms gift_falsches_zertifikat
#print axioms gift_falscher_pass
#print axioms gift_nicht_unterstuetzt
#print axioms gift_register
#print axioms gift_ueberlapp
#print axioms gift_ferner_ausgang
#print axioms gift_lauf_verweigert
#print axioms lauf_zu_laufBytes_zeuge
#print axioms byteschritt_im_code_zeuge
#print axioms holeFetchAux_praefix_zeuge
#print axioms write64_zeuge
#print axioms schritt_gerade_zeuge
#print axioms laufBytes_add_zeuge
#print axioms worldRep_store_zeuge
#print axioms repOk_zeuge
#print axioms cfg_zeuge
#print axioms senkWert_zeuge
#print axioms senkFrag_gerade_zeuge
#print axioms pw_tiefeBed_mit_frei
#print axioms senkBed_zeuge
#print axioms intWort_sint_zahl_zeuge
#print axioms istWahr_zeuge
#print axioms assign_lauf_zeuge
#print axioms probe_cmp
#print axioms probe_cmp_generisch
#print axioms probe_codec

end Gabbro.Grammatik.X86.PipelineWitnesses

