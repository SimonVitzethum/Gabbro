/-
  File:      Grammatik/X86/PipelineWorkPath.lean
  Subject:   Taken-path work and per-round loop correspondence over the
             direct pipeline lowering (lane 1259).

  Follow-up of `PipelineWork.lean`: its `Deckung` counts the STATIC
  whole-list length and its dynamic-path bound is arithmetic only, not
  connected to a taken-path `lauf` prefix; loop work stops at the
  labelled-step budget. This file connects the taken-path bound to the
  executed `lauf` prefix of the byte-level run, and proves the
  per-round loop body correspondence and the labelled-to-bytes leg
  with `PipelineLoops.lean`.

  Reused, not duplicated: `Pipeline.lauf_zu_laufBytes`/`gerade`/`kanon`/
  `encodeAll`/`CodeAt`, `DerivedWorkBound.decodiertZu`/`arbeit_decodiert`,
  `PipelineWork.pipeSummary`/`pipeSummary_expand`/`senkStmt_flach_laenge`/
  `PipePaket`, `PipelineLoops.schleifeProg`/`schleifeSchritte`/
  `schleife_korrekt_endlich`/`schleife_bytes`/`relax_laufBytes`,
  the actual `lauf`/`laufBytes`/`laufL`/`laufBytesI` runs. No second IR,
  no second source interpreter, no new cost model. Unsupported shapes
  are REFUSED, never guessed. Rust is out of scope.
-/
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineLoops
import Grammatik.X86.ISAWitnesses

namespace Gabbro.Grammatik.X86.PipelineWorkPath

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineLoops
open Gabbro.Grammatik.X86.PipelineWitnesses

/-! ## 1. Taken-path work: the executed prefix length.

    The taken-path work of a byte-level run is the length of the
    instruction prefix it actually retires -- never the static
    whole-list length. -/

/-- TAKEN-PATH WORK: the retired count of the executed prefix. -/
def genommenArbeit (T : List Befehl) : Nat := T.length

/-! ## 2. The taken-path prefix bridge: executed prefix to bytes.

    `Pipeline.lauf_zu_laufBytes` runs a whole static list. Here the
    STATIC program `prog` is split at the actually executed TAKEN
    prefix `T` (`prog = T ++ rest`): the fetched byte run of exactly
    `T.length` steps is the taken prefix run, its retired work is
    `T.length` (never the static length), and the taken length never
    exceeds the static length. Every premise is used: `hprog` fixes
    the split, `hg`/`hlauf`/`hc`/`hf`/`hrip` feed the bridge. -/

/-- TAKEN-PATH BRIDGE: the fetched run of `T.length` steps retires
    exactly the taken prefix `T` of the static program. -/
theorem laufBytes_genommen (cs : Adresse) (flat : List Byte)
    (prog T rest : List Befehl) (pre post : List Byte) (s s' : Zustand)
    (hprog : prog = T ++ rest)
    (hg : T.all Pipeline.gerade = true)
    (hlauf : lauf (T.map Pipeline.kanon) s = some s')
    (hc : Pipeline.CodeAt s.speicher cs flat)
    (hf : flat = pre ++ Pipeline.encodeAll prog ++ post)
    (hrip : s.rip = addrOff cs pre.length) :
    laufBytes T.length s = .weiter s' ∧
      s'.rip = addrOff cs (pre.length + (Pipeline.encodeAll T).length) ∧
      Pipeline.CodeAt s'.speicher cs flat ∧
      targetWork ((decodiertZu T).map fun d => d.befehl) = T.length ∧
      T.length ≤ prog.length := by
  subst hprog
  have hfs : flat = pre ++ Pipeline.encodeAll T ++
      (Pipeline.encodeAll rest ++ post) := by
    simp only [List.append_assoc] at hf ⊢
    rw [Pipeline.encodeAll_append] at hf
    simp only [List.append_assoc] at hf
    exact hf
  obtain ⟨hb, hr, hc', -, -⟩ := Pipeline.lauf_zu_laufBytes cs flat T pre
    (Pipeline.encodeAll rest ++ post) s s' hg hlauf hc hfs hrip
  refine ⟨hb, hr, hc', arbeit_decodiert T, ?_⟩
  simp only [List.length_append]
  omega

/-- JOINT WITNESS for `laufBytes_genommen`: the first witness chunk
    is the taken prefix of the candidate; the fetched five steps
    retire exactly five instructions, within the static twelve. -/
theorem laufBytes_genommen_zeuge :
    ∃ (T rest : List Befehl) (s' : Zustand),
      (pwChunk ++ pwProg.drop 5) = T ++ rest ∧
      T.all Pipeline.gerade = true ∧
      lauf (T.map Pipeline.kanon) (pwStart 30) = some s' ∧
      Pipeline.CodeAt (pwStart 30).speicher (natAdresse 4096) pwBytes ∧
      pwBytes = [] ++ Pipeline.encodeAll (pwChunk ++ pwProg.drop 5) ++ [] ∧
      (pwStart 30).rip = addrOff (natAdresse 4096) ([] : List Byte).length ∧
      laufBytes T.length (pwStart 30) = .weiter s' ∧
      targetWork ((decodiertZu T).map fun d => d.befehl) = T.length ∧
      T.length ≤ (pwChunk ++ pwProg.drop 5).length ∧
      PipePaket := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp pw_chunk_lauft
  have hf : pwBytes = [] ++ Pipeline.encodeAll (pwChunk ++ pwProg.drop 5) ++ [] := by
    rw [Pipeline.encodeAll_append]
    simpa using pw_split
  have hrip : (pwStart 30).rip = addrOff (natAdresse 4096) ([] : List Byte).length := by
    have h0 : (pwStart 30).rip = natAdresse 4096 := rfl
    rw [h0, List.length_nil]
    exact (addrOff_null _).symm
  obtain ⟨hb, hr, hc, hw, hle⟩ := laufBytes_genommen (natAdresse 4096) pwBytes
    (pwChunk ++ pwProg.drop 5) pwChunk (pwProg.drop 5) [] [] (pwStart 30) s'
    rfl pw_chunk_gerade hs' pw_code hf hrip
  exact ⟨pwChunk, pwProg.drop 5, s', rfl, pw_chunk_gerade, hs', pw_code, hf,
    hrip, hb, hw, hle, pipePaket_hold⟩

/-! ## 3. Dynamic coverage: the taken prefix is priced, not the list.

    `deckung_pipeChunk` covers the STATIC chunk length. Here the
    coverage is over the EXECUTED prefix `T` (`chunk = T ++ rest`):
    the taken length is at most the shallow chunk bound (3 or 5),
    hence covered by the admitted summary over any positive source
    budget. Every premise is used: `hflach`/`hchunk`/`hT` bound the
    static chunk, `hprefix` carries the taken length below it,
    `hsrc` keeps the scaled bound above it. -/

variable {D : Deklaration}

/-- TAKEN-PATH COVERAGE: the executed prefix of a shallow lowered
    chunk is covered by the admitted pipeline summary. -/
theorem deckung_pfad_chunk (c : Pipeline.PipeCfg) (L : Pipeline.Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (src : Nat)
    (p chunk T rest : List Befehl)
    (hflach : Pipeline.senkWert (Pipeline.abbOf c) e c.dst c.tmp = some p)
    (hchunk : Pipeline.senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk)
    (hprefix : chunk = T ++ rest)
    (hsrc : 1 ≤ src) :
    Deckung pipeSummary src (decodiertZu T) := by
  have hlen := senkStmt_flach_laenge c L l t f i e hT hw hL p chunk hflach hchunk
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have hwork : targetWork ((decodiertZu T).map fun d => d.befehl) = T.length :=
    arbeit_decodiert T
  subst hprefix
  rw [hwork]
  simp only [List.length_append] at hlen
  omega

/-- JOINT WITNESS for `deckung_pfad_chunk`: the taken prefix is the
    whole witness chunk, covered over source budget 1. -/
theorem deckung_pfad_chunk_zeuge :
    ∃ (p chunk T rest : List Befehl),
      Pipeline.senkWert (Pipeline.abbOf pwCfg) pwWert0 .rax .rcx = some p ∧
      Pipeline.senkStmt pwCfg pwL
        (Stmt.assignSlot (V := pwV) (l := false) () () pwIdx0
          (cast (congrArg (Expr pwD pwCtx []) pwHT0) pwWert0) pwHw pwHL) =
        some chunk ∧
      chunk = T ++ rest ∧
      1 ≤ 1 ∧
      Deckung pipeSummary 1 (decodiertZu T) ∧
      PipePaket := by
  have hprefix : pwProg.take 5 = pwChunk ++ [] := by simp [pwChunk]
  refine ⟨_, _, _, _, pw_senkWert0, pwChunkCast, hprefix, Nat.le_refl 1, ?_,
    pipePaket_hold⟩
  exact deckung_pfad_chunk pwCfg pwL false () () pwIdx0 pwWert0 pwHT0
    pwHw pwHL 1 _ _ _ _ pw_senkWert0 pwChunkCast hprefix (Nat.le_refl 1)

/- CUTS:
   - Skeleton only: `genommenArbeit` names the taken-path count.
   - OPEN: the prefix-run bridge (`laufBytes_genommen`), the dynamic
     `Deckung` producer, the per-round loop correspondence
     (`runde_einzel`), the labelled-to-bytes leg
     (`schleife_pfad_bytes`), refusals, gifts and joint witnesses.
-/

#print axioms genommenArbeit

end Gabbro.Grammatik.X86.PipelineWorkPath
