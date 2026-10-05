/-
  File:      Grammatik/X86/PipelineCallsExec.lean
  Subject:   Pipeline calls, real source correspondence: a callee whose body
             is one lowered straight-line assignment (`execBlock` of the real
             body, not an abstracted result write), with callee-saved
             register preservation and a memory-changing witness.

  Reused, not duplicated: `PipelineCalls` (`rufOk`, `calleeGerettet`,
  `pipeline_ruf_rahmen`, frame witnesses), `Pipeline` (`senkBlock`,
  `validate`/`validate_sound`, `senkWertT_korrekt`, `assignT_lauf`,
  `worldRep_store`, `lauf_zu_laufBytes`, `Entspricht` vocabulary),
  `PipelineWitnesses` (the concrete declaration `pwD`, contract `pwV`,
  layout `pwL`, values and memories). No second machine, no second
  loader, no source claim beyond the proved fragment.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineCalls
import Grammatik.X86.PipelineWitnesses

namespace Gabbro.Grammatik.X86.PipelineCallsExec

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineCalls
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.OptimizationRules

variable {D : Deklaration}

/-- The proved callee shape: exactly one slot assignment, then `nil`.
    Every other block form is refused, never guessed. -/
def istEinzelZuweisung {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') : Bool :=
  match b with
  | .cons (.assignSlot _ _ _ _ _ _) .nil => true
  | _ => false

/-- THE CALL-EXEC VALIDATOR: the caller frame is admitted (`rufOk`: layout
    fit, exact stack-arg count, six callee-save words, no red zone), the
    callee body has the proved single-assignment shape, and the candidate
    bytes are what the Lean pipeline recomputes from the source
    (`validate` with no optimiser certificates: a certificate could
    rewrite the body away from the proved shape). -/
def rufExecOk (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) : Bool :=
  rufOk b r nArgs benutztRot && istEinzelZuweisung body &&
    validate c L [] body bytes

/-- Working registers used nowhere near the callee-saved set: every
    callee-saved register differs from `dst` and `adr` and lies off the
    scratch stack `tmp :: frei`. Decided, never assumed. -/
def calleeFremd (c : PipeCfg) : Bool :=
  calleeGerettet.all (fun q => decide (q ≠ c.dst ∧ q ≠ c.adr ∧ q ∉ c.tmp :: c.frei))

/-- Unpacking the call-exec validator: frame, shape and recomputed bytes. -/
theorem rufExecOk_teile (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : rufExecOk b r nArgs benutztRot c L body bytes = true) :
    rufOk b r nArgs benutztRot = true ∧ istEinzelZuweisung body = true ∧
      validate c L [] body bytes = true := by
  unfold rufExecOk at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A callee-saved register lies off every working register. -/
theorem calleeFremd_mem (c : PipeCfg) (h : calleeFremd c = true) (q : Register)
    (hm : q ∈ calleeGerettet) : q ≠ c.dst ∧ q ≠ c.adr ∧ q ∉ c.tmp :: c.frei := by
  unfold calleeFremd at h
  have h2 := (List.all_eq_true.mp h) q hm
  simpa using h2

/-- RED-ZONE USE REFUSAL: no call that uses the red zone is admitted. -/
theorem rufExecOk_verweigert_rot (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte) :
    rufExecOk b r nArgs true c L body bytes = false := by
  unfold rufExecOk
  rw [pipeline_ruf_verweigert_rot]
  rfl

/-- SHAPE REFUSAL: a body that is not one assignment is refused loudly. -/
theorem rufExecOk_verweigert_form (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : istEinzelZuweisung body = false) :
    rufExecOk b r nArgs benutztRot c L body bytes = false := by
  unfold rufExecOk
  rw [h]
  cases rufOk b r nArgs benutztRot <;> rfl

/-- BYTE REFUSAL: candidate bytes the Lean pipeline does not recompute
    are refused loudly. -/
theorem rufExecOk_verweigert_bytes (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (c : PipeCfg) (L : Layout D)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (body : Block D V l Γ Λ Λ') (bytes : List Byte)
    (h : validate c L [] body bytes = false) :
    rufExecOk b r nArgs benutztRot c L body bytes = false := by
  unfold rufExecOk
  rw [h]
  cases rufOk b r nArgs benutztRot <;> cases istEinzelZuweisung body <;> rfl

/-- With no certificates the optimiser stage is the identity. -/
theorem optimise_nil {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') : optimise [] b = b := rfl

/-- SINGLE-ASSIGNMENT CHUNK RUN (the widened value lowering): the chunk
    writes the representation word of the exact source value at the slot
    address, keeps every variable register, and preserves every register
    off the working set `dst`/`adr`/`tmp :: frei` -- in particular every
    callee-saved register the disjointness check keeps off it. Every
    premise is consumed: `hc` for freshness and distinctness, `hp` for
    the value run, `hwr` for the store, `hE` for the environment. -/
theorem einzelChunk_lauf (c : PipeCfg) (hc : cfgOk c = true)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) {lo hi : Int} (hτ : τ = .int lo hi)
    (hlo : 0 ≤ lo) (hhi : hi < 2 ^ 64) (pv : List Befehl)
    (hp : senkWertT c e = some pv) (A : Nat)
    (ρ : Env D Γ) (σ₀ σ : World D) (s : Zustand)
    (hE : EnvRepr ρ s.register (abbOf c))
    (hwr : schreibbar8 s.speicher (natAdresse A) = true) :
    ∃ s', lauf ((pv ++ [Befehl.movImm64 c.adr (natAdresse A),
        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]).map kanon) s = some s' ∧
      write64 s.speicher (natAdresse A)
        (zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))) =
        some s'.speicher ∧
      EnvRepr ρ s'.register (abbOf c) ∧
      (∀ q, q ≠ c.dst → q ≠ c.adr → q ∉ c.tmp :: c.frei →
        s'.register q = s.register q) := by
  obtain ⟨-, hda, -, -, -, -⟩ := cfgOk_regs c hc
  obtain ⟨sV, hrunV, hvalV, hmemV, hregV⟩ :=
    senkWertT_korrekt c hc e hτ ρ σ₀ σ s hE pv hp
  have hword : sV.register c.dst =
      zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi)) := by
    rw [hvalV]
    exact intWort_zahlWort _ hlo hhi
  have hmi := schritt_movImm64 (kanon (.movImm64 c.adr (natAdresse A))) sV c.adr
    (natAdresse A) (laengeOk_encode _) rfl
  let s2 := schrittRegister sV (ripNach sV.rip (kanon (.movImm64 c.adr (natAdresse A))).laenge)
    sV.flags c.adr (natAdresse A)
  have hs2d : s2.register c.dst = sV.register c.dst := regSet_fremd _ _ _ _ hda
  have hs2a : s2.register c.adr = natAdresse A := regSet_gleich _ _ _
  have heff : effAddr s2 c.adr (BitVec.ofNat 32 0) = natAdresse A := by
    rw [effAddr_null, hs2a]
  let w : Wort := zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))
  let m' : Speicher := { s.speicher with bytes := writeBytes s.speicher (natAdresse A) w }
  have hw : write64 s.speicher (natAdresse A)
      (zahlWort (cast (congrArg (Wert D) hτ) (eval σ₀ e σ ρ) : Wert D (.int lo hi))) =
      some m' := by
    unfold write64
    rw [if_pos hwr]
  have hw2 : write64 s2.speicher (effAddr s2 c.adr (BitVec.ofNat 32 0)) (s2.register c.dst) =
      some m' := by
    rw [heff, hs2d, hword]
    show write64 sV.speicher _ _ = _
    rw [hmemV]
    exact hw
  have hst := schritt_store64_erfolg (kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))) s2
    c.adr c.dst (BitVec.ofNat 32 0) m' (laengeOk_encode _) rfl hw2
  let r3 : Adresse :=
    ripNach s2.rip (kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))).laenge
  have hmov : lauf [kanon (.movImm64 c.adr (natAdresse A))] sV = some s2 := by
    rw [lauf_einzeln_gleich]
    exact hmi
  have hsto : lauf [kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))] s2 =
      some { s2 with speicher := m', rip := r3 } := by
    rw [lauf_einzeln_gleich]
    exact hst
  have hcomp : lauf ((pv ++ [Befehl.movImm64 c.adr (natAdresse A),
      Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)]).map kanon) s =
      some { s2 with speicher := m', rip := r3 } := by
    rw [List.map_append, lauf_anhang _ _ _ _ hrunV]
    rw [show ([Befehl.movImm64 c.adr (natAdresse A),
        Befehl.store64 c.adr c.dst (BitVec.ofNat 32 0)].map kanon) =
        [kanon (.movImm64 c.adr (natAdresse A))] ++
        [kanon (.store64 c.adr c.dst (BitVec.ofNat 32 0))] from rfl]
    rw [lauf_anhang _ _ _ _ hmov]
    exact hsto
  refine ⟨{ s2 with speicher := m', rip := r3 }, hcomp, hw, ?_, ?_⟩
  · apply envRepr_fremd ρ (abbOf c) s.register _ hE
    intro τ' x
    obtain ⟨-, -, h3⟩ := cfgOk_frei c hc x
    obtain ⟨h1, h2⟩ := cfgOk_var_frei c hc x
    show regSet sV.register c.adr (natAdresse A) (abbOf c τ' x) = s.register (abbOf c τ' x)
    rw [regSet_fremd _ _ _ _ h3, hregV _ h1 h2]
  · intro q hqd hqa hqf
    show (regSet sV.register c.adr (natAdresse A)) q = s.register q
    rw [regSet_fremd _ _ _ _ hqa]
    exact hregV q hqd hqf

end Gabbro.Grammatik.X86.PipelineCallsExec
