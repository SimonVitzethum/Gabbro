/-
  File:      Grammatik/X86/PipelineBlockTables.lean
  Subject:   Block-level table READS with scaled-index addressing for the
             direct pipeline: follow-up of lane 1159 (`PipelineTables.lean`).

             Lane 1159 lowers constant-index reads/writes (absolute address
             materialisation) and block-level WRITES. What it does NOT cover:
             reads inside blocks (`Block.bind`/`assignVar` consumers) and
             variable indices (no scaled addressing in the pilot). This file
             provides both WITHOUT editing existing files: a `senkBlock`-style
             block lowering for `assignVar`-of-table-read statements with a
             VARIABLE index, where the address `B + k * Z + O` is computed at
             run time with pilot adds (scale doubling for `Z` in 1/2/4/8,
             checked by the reused `skalaOk`), plus the correctness theorem
             over fetched bytes and refusal theorems for every unsupported
             shape. Rust is out of scope.

  Reused, not duplicated:
    - anchor/layout/world: `TabAnker`, `ankerBasis/Zeile`, `feldOff`,
      `feldAdr`, `feldAdr_some`, `feldAdr_kein_oob`, `idxOk_toNat`,
      `tabLayout`, `ankerSepB`, `ankerSep_sound`, `tabWorldRep`,
      `WorldRep`, `LayoutSep` (`PipelineTables.lean`, lane 1159);
    - pipeline: `PipeCfg`, `cfgOk`, `cfgOk_frei/regs`, `abbOf`,
      `EnvRepr`, `envRepr_fremd`, `CodeAt`, `kanon`, `encodeAll`,
      `gerade`, `lauf_zu_laufBytes`, `laufBytes_add`, `Entspricht`,
      `worldRep_lese`, `repOk_int`, `natAdresse_ohneUmbruch/toNat`
      (`Pipeline.lean`); `intWort_add`, `lauf_anhang`,
      `lauf_einzeln_gleich` (`ExpressionLowering.lean`);
    - addresses: `skaliertAddr` (`EffectiveAddress.lean`); `skalaOk`,
      `basisKeinForm`, `adrOk` (`AddressEncoding.lean`);
    - machine: `schritt_movImm64/movReg64/addReg64/load64_erfolg`,
      `schrittRegister`, `regSet_gleich/fremd`,
      `schrittRegister_speicher` (`Ausfuehrung.lean`); `effAddr_null`
      (`EffectiveAddress.lean`); `intWort`, `natAdresse`, `read64`.
  No second IR, no second source interpreter, no per-program rule.
-/
import Grammatik.X86.PipelineTables
import Grammatik.X86.ExpressionLowering
import Grammatik.X86.SourceAssignmentLowering
import Grammatik.X86.SourceMemory

namespace Gabbro.Grammatik.X86.PipelineBlockTables

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineTables

variable {D : Deklaration}

/-! ## 1. Word bridges and doubling

    `intWort` of a small nonnegative number is the `Nat` address word;
    `Nat` address words add and multiply. Doubling (`verdoppeln`) scales
    by `2 ^ e` with pilot adds only. -/

/-- `intWort` of a small nonnegative number is the `Nat` address word. -/
theorem intWort_nat (v : Int) (h0 : 0 ≤ v) (h64 : v < 2 ^ 64) :
    intWort v = natAdresse v.toNat := by
  unfold intWort natAdresse
  congr 1
  have he : v % (2 ^ 64 : Int) = v := Int.emod_eq_of_lt h0 h64
  rw [he]

/-- `Nat` address words add. -/
theorem natAdresse_add (a b : Nat) :
    natAdresse (a + b) = natAdresse a + natAdresse b := by
  unfold natAdresse
  rw [BitVec.ofNat_add]

/-- `Nat` address words multiply. -/
theorem natAdresse_mul (a b : Nat) :
    natAdresse (a * b) = natAdresse a * natAdresse b := by
  unfold natAdresse
  rw [BitVec.ofNat_mul]

/-- Doubling code: `e` times `dst := dst + dst` (scale `2 ^ e`). -/
def verdoppeln (dst : Register) (e : Nat) : List Befehl :=
  List.replicate e (.addReg64 dst dst)

/-- `add64` returns the modular sum as its value. -/
theorem add64_wert (x y : Wort) : (add64 x y).1 = x + y := rfl

/-- Powers of two, definitionally (core Lean has no `pow_zero` here). -/
theorem pow2_zero : (2 : Nat) ^ 0 = 1 := rfl

/-- Powers of two, definitionally. -/
theorem pow2_succ (e : Nat) : (2 : Nat) ^ (e + 1) = 2 ^ e * 2 := rfl

/-- DOUBLING RUN: from `dst = natAdresse m`, `e` doublings leave
    `dst = natAdresse (m * 2 ^ e)`; memory and all other registers kept. -/
theorem verdoppeln_lauf (dst : Register) (e : Nat) (m : Nat) (s : Zustand)
    (h : s.register dst = natAdresse m) :
    ∃ s', lauf ((verdoppeln dst e).map kanon) s = some s' ∧
      s'.register dst = natAdresse (m * 2 ^ e) ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ dst → s'.register q = s.register q) := by
  induction e generalizing m s with
  | zero =>
    refine ⟨s, by rw [show verdoppeln dst 0 = [] from rfl, List.map_nil]; rfl, ?_, rfl, fun _ _ => rfl⟩
    have hm1 : m * 1 = m := by omega
    rw [pow2_zero, hm1]
    exact h
  | succ e ih =>
    have hstep := schritt_addReg64 (kanon (.addReg64 dst dst)) s dst dst
      (laengeOk_encode _) rfl
    let s1 := schrittRegister s (ripNach s.rip (kanon (.addReg64 dst dst)).laenge)
      (add64 (s.register dst) (s.register dst)).2 dst
      ((add64 (s.register dst) (s.register dst)).1)
    have h1 : s1.register dst = natAdresse (m + m) := by
      show regSet (s.register) dst _ dst = _
      rw [regSet_gleich, add64_wert, h, ← natAdresse_add]
    obtain ⟨s', hrun, hdst, hmem, hreg⟩ := ih (m + m) s1 h1
    have hexp : (m + m) * 2 ^ e = m * 2 ^ (e + 1) := by
      have h2 : m + m = m * 2 := by omega
      calc (m + m) * 2 ^ e = (m * 2) * 2 ^ e := by rw [h2]
        _ = m * (2 * 2 ^ e) := by rw [Nat.mul_assoc]
        _ = m * (2 ^ e * 2) := by rw [Nat.mul_comm 2 (2 ^ e)]
        _ = m * 2 ^ (e + 1) := by rw [pow2_succ]
    refine ⟨s', ?_, by rw [← hexp]; exact hdst, hmem.trans rfl, ?_⟩
    · have e1 : ((verdoppeln dst (e + 1)).map kanon) =
          [kanon (.addReg64 dst dst)] ++ (verdoppeln dst e).map kanon := by
        simp [verdoppeln, List.replicate_succ]
      rw [e1, lauf_anhang _ _ _ _ (by rw [lauf_einzeln_gleich]; exact hstep)]
      exact hrun
    · intro q hq
      rw [hreg q hq]
      show regSet (s.register) dst _ q = s.register q
      rw [regSet_fremd _ _ _ _ hq]

/-! ## 2. Scales 1/2/4/8 and the scaled address

    The admitted scales are exactly the reused `skalaOk` ones (1, 2, 4, 8:
    `AddressEncoding.lean`); every other row stride is refused downstream,
    never rounded. `skalAdresse` is the Nat-level row address
    `B + k * Z + O`, proved equal to the anchor's `feldAdr` address. -/

/-- Doubling count for an admitted SIB scale: `Z = 2 ^ skalExp Z`. -/
def skalExp : Nat → Nat
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | 8 => 3
  | _ => 0

/-- An admitted scale is a power of two with the doubling count. -/
theorem skalExp_sound (Z : Nat) (h : skalaOk Z = true) : Z = 2 ^ skalExp Z := by
  unfold skalaOk at h
  simp only [decide_eq_true_eq] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- An admitted scale is positive. -/
theorem skalaOk_pos (Z : Nat) (h : skalaOk Z = true) : 0 < Z := by
  unfold skalaOk at h
  simp only [decide_eq_true_eq] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- Inversion of an admitted scale: only 1, 2, 4, 8 pass. -/
theorem skalaOk_inv (Z : Nat) (h : skalaOk Z = true) :
    Z = 1 ∨ Z = 2 ∨ Z = 4 ∨ Z = 8 := by
  unfold skalaOk at h
  simp only [decide_eq_true_eq] at h
  exact h

/-- The scaled row address: base plus index times stride plus offset. -/
def skalAdresse (B kN Z O : Nat) : Nat := B + kN * Z + O

/-- The scaled address IS the anchor address at an in-extent index. -/
theorem skalAdresse_feldAdr (A : TabAnker D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (a : Nat) (h : PipelineTables.feldAdr A t k f = some a) :
    ∃ B Z O, PipelineTables.ankerBasis A t = some B ∧
      PipelineTables.ankerZeile A t = some Z ∧
      PipelineTables.feldOff A t f = some O ∧ skalAdresse B k.toNat Z O = a := by
  obtain ⟨B, Z, O, hB, hZ, hO, -, -, ha⟩ :=
    PipelineTables.feldAdr_some A t k f a h
  exact ⟨B, Z, O, hB, hZ, hO, by unfold skalAdresse; omega⟩

/-! ## 3. The scaled chunk

    The address `B + k * Z + O` is computed at run time with pilot
    instructions only: `dst` scales the index by doubling (`2 ^ skalExp Z`
    is the admitted stride), `adr` accumulates base and offset, and the
    pilot `load64` reads through `adr` with zero displacement (the reused
    `basisKeinForm` shape). The computed address IS the reused
    `skaliertAddr` (`EffectiveAddress.lean`) plus the offset: no second
    address model. There is no native SIB encoding/step in the pilot
    (see CUTS). -/

/-- The scaled tail: index in `idx` (untouched) to the word at
    `B + idx * Z + O` in `dst`, through `adr`. -/
def skalRest (c : PipeCfg) (idx : Register) (O Z : Nat) : List Befehl :=
  [.movReg64 c.dst idx] ++ verdoppeln c.dst (skalExp Z) ++
    [.addReg64 c.adr c.dst, .movImm64 c.dst (natAdresse O),
     .addReg64 c.adr c.dst, .load64 c.dst c.adr (BitVec.ofNat 32 0)]

/-- The full scaled chunk: materialise the base, then the tail. -/
def skalChunk (c : PipeCfg) (idx : Register) (B O Z : Nat) : List Befehl :=
  [.movImm64 c.adr (natAdresse B)] ++ skalRest c idx O Z

/-- A single successful step heads a run. -/
theorem lauf_cons (d : Decodiert) (rest : List Decodiert) (s s' : Zustand)
    (h : schritt d s = some s') : lauf (d :: rest) s = lauf rest s' := by
  simp only [lauf, h]

/-- Every doubling is straight-line code. -/
theorem verdoppeln_gerade (dst : Register) (e : Nat) :
    (verdoppeln dst e).all gerade = true := by
  induction e with
  | zero => rfl
  | succ e ih => simp [verdoppeln, List.replicate_succ, gerade]

/-- The scaled tail is straight-line code. -/
theorem skalRest_gerade (c : PipeCfg) (idx : Register) (O Z : Nat) :
    (skalRest c idx O Z).all gerade = true := by
  simp [skalRest, List.all_append, verdoppeln_gerade, gerade]

/-- The full scaled chunk is straight-line code. -/
theorem skalChunk_gerade (c : PipeCfg) (idx : Register) (B O Z : Nat) :
    (skalChunk c idx B O Z).all gerade = true := by
  simp [skalChunk, skalRest_gerade, gerade]
/-- The computed address is the reused scaled-index address plus the
    offset: `skaliertAddr` with zero displacement over the post-base
    state, plus `O`. -/
theorem skaliertAddr_natAdresse (s1 : Zustand) (b i : Register) (Z B M O : Nat)
    (hb : s1.register b = natAdresse B) (hi : s1.register i = natAdresse M) :
    skaliertAddr s1 b i Z (BitVec.ofNat 32 0) + natAdresse O =
      natAdresse (B + M * Z + O) := by
  unfold skaliertAddr
  rw [hb, hi]
  have hdz : ∀ (x : Wort), x + dispWort (BitVec.ofNat 32 0) = x := by
    intro x
    rw [dispWort_null]
    exact BitVec.add_zero x
  rw [hdz]
  have eZ : BitVec.ofNat 64 Z = natAdresse Z := rfl
  rw [eZ, ← natAdresse_mul, ← natAdresse_add, ← natAdresse_add]

/-! ## 4. The scaled tail run

    From `adr = natAdresse B` and `idx = natAdresse M` the tail leaves
    `dst` with the word at `B + M * Z + O`, `adr` with the computed
    address (the reused `skaliertAddr` plus `O`), keeps memory and every
    register but the two working ones. All address arithmetic is exact
    at the word level (`ofNat` homomorphisms); the `Nat`-level extent is
    the caller's checked bound premise. -/

/-- SCALED TAIL RUN: address computation plus the load, with the
    `skaliertAddr` equation and full framing. -/
theorem skalRest_lauf (c : PipeCfg) (hc : cfgOk c = true)
    (idx : Register) (O Z B M : Nat) (s1 : Zustand)
    (hadr : s1.register c.adr = natAdresse B)
    (hidx : s1.register idx = natAdresse M)
    (hsk : skalaOk Z = true)
    (w : Wort) (hrd : read64 s1.speicher (natAdresse (B + M * Z + O)) = some w) :
    ∃ s', lauf ((skalRest c idx O Z).map kanon) s1 = some s' ∧
      s'.register c.dst = w ∧
      s'.register c.adr = natAdresse (B + M * Z + O) ∧
      s'.register c.adr =
        skaliertAddr s1 c.adr idx Z (BitVec.ofNat 32 0) + natAdresse O ∧
      s'.speicher = s1.speicher ∧
      (∀ q, q ≠ c.dst → q ≠ c.adr → s'.register q = s1.register q) := by
  obtain ⟨hdt, hda, -, -, -, -⟩ := cfgOk_regs c hc
  have had : c.adr ≠ c.dst := fun e => hda e.symm
  have hZ : Z = 2 ^ skalExp Z := skalExp_sound Z hsk
  -- step 1: `dst := idx`
  have hmov := schritt_movReg64 (kanon (.movReg64 c.dst idx)) s1 c.dst idx
    (laengeOk_encode _) rfl
  let s2 := schrittRegister s1 (ripNach s1.rip (kanon (.movReg64 c.dst idx)).laenge)
    s1.flags c.dst (s1.register idx)
  have e2 : s2.register c.adr = natAdresse B := by
    show regSet (s1.register) c.dst (s1.register idx) c.adr = _
    rw [regSet_fremd _ _ _ _ had, hadr]
  -- step 2: doublings scale `dst` by `2 ^ skalExp Z`
  have hd2 : s2.register c.dst = natAdresse M := by
    show regSet (s1.register) c.dst (s1.register idx) c.dst = _
    rw [regSet_gleich, hidx]
  obtain ⟨s3, hr3, hd3, hm3, hp3⟩ := verdoppeln_lauf c.dst (skalExp Z) M s2 hd2
  have hd3' : s3.register c.dst = natAdresse (M * Z) := by
    rw [hZ]; exact hd3
  have e3 : s3.register c.adr = natAdresse B := by
    rw [hp3 c.adr had]; exact e2
  -- step 3: `adr := adr + dst`
  have hadd1 := schritt_addReg64 (kanon (.addReg64 c.adr c.dst)) s3 c.adr c.dst
    (laengeOk_encode _) rfl
  let s4 := schrittRegister s3 (ripNach s3.rip (kanon (.addReg64 c.adr c.dst)).laenge)
    (add64 (s3.register c.adr) (s3.register c.dst)).2 c.adr
    ((add64 (s3.register c.adr) (s3.register c.dst)).1)
  have ha4 : s4.register c.adr = natAdresse (B + M * Z) := by
    show regSet (s3.register) c.adr _ c.adr = _
    rw [regSet_gleich, add64_wert, e3, hd3', ← natAdresse_add]
  -- step 4: `dst := O`
  have hmiO := schritt_movImm64 (kanon (.movImm64 c.dst (natAdresse O))) s4 c.dst
    (natAdresse O) (laengeOk_encode _) rfl
  let s5 := schrittRegister s4 (ripNach s4.rip (kanon (.movImm64 c.dst (natAdresse O))).laenge)
    s4.flags c.dst (natAdresse O)
  have e5d : s5.register c.dst = natAdresse O := by
    show regSet (s4.register) c.dst (natAdresse O) c.dst = _
    rw [regSet_gleich]
  have e5a : s5.register c.adr = natAdresse (B + M * Z) := by
    show regSet (s4.register) c.dst (natAdresse O) c.adr = _
    rw [regSet_fremd _ _ _ _ had]
    exact ha4
  -- step 5: `adr := adr + dst`
  have hadd2 := schritt_addReg64 (kanon (.addReg64 c.adr c.dst)) s5 c.adr c.dst
    (laengeOk_encode _) rfl
  let s6 := schrittRegister s5 (ripNach s5.rip (kanon (.addReg64 c.adr c.dst)).laenge)
    (add64 (s5.register c.adr) (s5.register c.dst)).2 c.adr
    ((add64 (s5.register c.adr) (s5.register c.dst)).1)
  have ha6 : s6.register c.adr = natAdresse (B + M * Z + O) := by
    show regSet (s5.register) c.adr _ c.adr = _
    rw [regSet_gleich, add64_wert, e5a, e5d, ← natAdresse_add]
  -- step 6: the load
  have heff : effAddr s6 c.adr (BitVec.ofNat 32 0) = natAdresse (B + M * Z + O) := by
    rw [effAddr_null]; exact ha6
  have hm61 : s6.speicher = s1.speicher := by
    have r4 : s4.speicher = s3.speicher := schrittRegister_speicher _ _ _ _ _
    have r5 : s5.speicher = s4.speicher := schrittRegister_speicher _ _ _ _ _
    have r6 : s6.speicher = s5.speicher := schrittRegister_speicher _ _ _ _ _
    have r2 : s2.speicher = s1.speicher := schrittRegister_speicher _ _ _ _ _
    exact r6.trans (r5.trans (r4.trans (hm3.trans r2)))
  have hrd6 : read64 s6.speicher (effAddr s6 c.adr (BitVec.ofNat 32 0)) = some w := by
    rw [heff, hm61]; exact hrd
  have hload := schritt_load64_erfolg (kanon (.load64 c.dst c.adr (BitVec.ofNat 32 0)))
    s6 c.dst c.adr (BitVec.ofNat 32 0) w (laengeOk_encode _) rfl hrd6
  let s' := schrittRegister s6 (ripNach s6.rip
    (kanon (.load64 c.dst c.adr (BitVec.ofNat 32 0))).laenge) s6.flags c.dst w
  have ha6' : s'.register c.adr = natAdresse (B + M * Z + O) := by
    show regSet (s6.register) c.dst w c.adr = _
    rw [regSet_fremd _ _ _ _ had]; exact ha6
  have hd' : s'.register c.dst = w := regSet_gleich _ _ _
  have hmem : s'.speicher = s1.speicher :=
    (schrittRegister_speicher _ _ _ _ _).trans hm61
  have hp : ∀ q, q ≠ c.dst → q ≠ c.adr → s'.register q = s1.register q := by
    intro q hd ha
    show regSet (s6.register) c.dst w q = _
    rw [regSet_fremd _ _ _ _ hd]
    show regSet (s5.register) c.adr _ q = _
    rw [regSet_fremd _ _ _ _ ha]
    show regSet (s4.register) c.dst _ q = _
    rw [regSet_fremd _ _ _ _ hd]
    show regSet (s3.register) c.adr _ q = _
    rw [regSet_fremd _ _ _ _ ha, hp3 q hd]
    show regSet (s1.register) c.dst _ q = _
    rw [regSet_fremd _ _ _ _ hd]
  have hskal : s'.register c.adr =
      skaliertAddr s1 c.adr idx Z (BitVec.ofNat 32 0) + natAdresse O := by
    rw [ha6']
    exact (skaliertAddr_natAdresse s1 c.adr idx Z B M O hadr hidx).symm
  have h12 : lauf ([kanon (.movReg64 c.dst idx)] ++
      (verdoppeln c.dst (skalExp Z)).map kanon) s1 = some s3 := by
    rw [lauf_anhang _ _ _ s2 (by rw [lauf_einzeln_gleich]; exact hmov)]
    exact hr3
  have e1 : (skalRest c idx O Z).map kanon =
      ([kanon (.movReg64 c.dst idx)] ++ (verdoppeln c.dst (skalExp Z)).map kanon) ++
      [kanon (.addReg64 c.adr c.dst), kanon (.movImm64 c.dst (natAdresse O)),
       kanon (.addReg64 c.adr c.dst),
       kanon (.load64 c.dst c.adr (BitVec.ofNat 32 0))] := by
    simp [skalRest]
  have hrun : lauf ((skalRest c idx O Z).map kanon) s1 = some s' := by
    rw [e1, lauf_anhang _ _ _ s3 h12,
      lauf_cons _ _ _ _ hadd1, lauf_cons _ _ _ _ hmiO,
      lauf_cons _ _ _ _ hadd2, lauf_einzeln_gleich]
    exact hload
  exact ⟨s', hrun, hd', ha6', hskal, hmem, hp⟩

/-- FULL CHUNK RUN: materialise the base, then the scaled tail. -/
theorem skalChunk_lauf (c : PipeCfg) (hc : cfgOk c = true)
    (idx : Register) (hidxa : idx ≠ c.adr) (B O Z M : Nat) (s : Zustand)
    (hidx : s.register idx = natAdresse M)
    (hsk : skalaOk Z = true)
    (w : Wort) (hrd : read64 s.speicher (natAdresse (B + M * Z + O)) = some w) :
    ∃ s', lauf ((skalChunk c idx B O Z).map kanon) s = some s' ∧
      s'.register c.dst = w ∧
      s'.register c.adr = natAdresse (B + M * Z + O) ∧
      s'.speicher = s.speicher ∧
      (∀ q, q ≠ c.dst → q ≠ c.adr → s'.register q = s.register q) := by
  obtain ⟨hdt, hda, -, -, -, -⟩ := cfgOk_regs c hc
  have had : c.adr ≠ c.dst := fun e => hda e.symm
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse B))) s c.adr
    (natAdresse B) (laengeOk_encode _) rfl
  let s1 := schrittRegister s (ripNach s.rip (kanon (.movImm64 c.adr (natAdresse B))).laenge)
    s.flags c.adr (natAdresse B)
  have ha1 : s1.register c.adr = natAdresse B := regSet_gleich _ _ _
  have hi1 : s1.register idx = natAdresse M := by
    show regSet (s.register) c.adr (natAdresse B) idx = _
    rw [regSet_fremd _ _ _ _ hidxa]; exact hidx
  have hm1 : s1.speicher = s.speicher := schrittRegister_speicher _ _ _ _ _
  have hrd1 : read64 s1.speicher (natAdresse (B + M * Z + O)) = some w := by
    rw [hm1]; exact hrd
  obtain ⟨s', hrun, hd', ha', -, hmem, hp⟩ :=
    skalRest_lauf c hc idx O Z B M s1 ha1 hi1 hsk w hrd1
  have e : (skalChunk c idx B O Z).map kanon =
      [kanon (.movImm64 c.adr (natAdresse B))] ++ (skalRest c idx O Z).map kanon := by
    simp [skalChunk]
  have hrunC : lauf ((skalChunk c idx B O Z).map kanon) s = some s' := by
    rw [e, lauf_anhang _ _ _ s1 (by rw [lauf_einzeln_gleich]; exact hmi)]
    exact hrun
  have hmemC : s'.speicher = s.speicher := hmem.trans hm1
  have hpC : ∀ q, q ≠ c.dst → q ≠ c.adr → s'.register q = s.register q := by
    intro q hd ha
    rw [hp q hd ha]
    show regSet (s.register) c.adr (natAdresse B) q = _
    rw [regSet_fremd _ _ _ _ ha]
  exact ⟨s', hrunC, hd', ha', hmemC, hpC⟩

/- CUTS:
   Skeleton only: scale exponent stub. The chunk, lowering, correctness,
   refusals and witnesses are OPEN.
-/
