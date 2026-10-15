/-
  File:      Grammatik/X86/ComposeProfileSelect.lean
  Subject:   Composition closing: profile-selection closing.

  Lane 844: closes backend form choice to the named CPU profile.
  The measured-trait tables stay tuning only: profile selection names a
  feature (`FeatureProfile.fallback`), the zeroing form choice
  (`Anweisungswahl.waehleNull`) is gated by flag liveness, and every
  selected byte re-decodes through the canonical decoder (`Codec.roundtrip`,
  the same decoder `ValidatorSkeleton` uses for coverage). No internals
  are re-proved; all producer facts are reused by name. No new
  interpreter, no new IR, no source/checker/Spec/goal/emitter change.
-/
import Grammatik.X86.FeatureProfile
import Grammatik.X86.InstructionSelection
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Speicher
import Grammatik.X86.Bild
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86.ComposeProfileSelect

open Gabbro.Grammatik.X86.Anweisungswahl

/-- Profile-gated zeroing instruction: the preserving 10-byte form under
    live flags, the clobbering 3-byte form under dead flags. The single
    element of `waehleNull`; the CPU profile never changes its meaning. -/
def composeInstr (flagsLive : Bool) (dst : Register) : Befehl :=
  if flagsLive then .movImm64 dst 0 else .xorReg64 dst dst

/-- Named-profile feature choice: exactly the admitted feature, the
    proven scalar path otherwise. Reuses `fallback`; tuning only. -/
def composeMerkmal (hw : HwProfil) (b : BereitProfil)
    (m : PerfMerkmal) : PerfMerkmal :=
  fallback hw b m

/-- The composed instruction is the single element of the accepted
    selector: no parallel form vocabulary is introduced. -/
theorem composeInstr_eq_waehleNull (flagsLive : Bool) (dst : Register) :
    [composeInstr flagsLive dst] = waehleNull flagsLive dst := by
  cases flagsLive <;> rfl

/-- Fail-closed profile leg: a refused feature composes to exactly the
    scalar path. Reuses `fallback_verweigert_bleibt_skalar`. -/
theorem compose_fallback_closed (hw : HwProfil) (b : BereitProfil)
    (m : PerfMerkmal) (h : waehle hw b m = none) :
    composeMerkmal hw b m = .skalar64 :=
  fallback_verweigert_bleibt_skalar hw b m h

/-- Tuning-only execution: the composed form zeroes its register through
    the canonical step at either flag liveness, hence the profile choice
    never changes the observed value. Reuses `schritt_null_mov` /
    `schritt_null_xor` with the pinned lengths `null_laengen`. -/
theorem compose_zero (s : Zustand) (flagsLive : Bool) (dst : Register) :
    (schritt ⟨composeInstr flagsLive dst,
      (encode (composeInstr flagsLive dst)).length⟩ s).map
      (fun s' => s'.register dst) = some 0 := by
  cases flagsLive with
  | true =>
    have h1 : composeInstr true dst = .movImm64 dst 0 := rfl
    have hlen := (null_laengen dst).1
    rw [h1, hlen]
    exact schritt_null_mov s dst
  | false =>
    have h1 : composeInstr false dst = .xorReg64 dst dst := rfl
    have hlen := (null_laengen dst).2
    rw [h1, hlen]
    exact schritt_null_xor s dst

/-- Every selected byte re-validated: the composed bytes decode back to
    themselves over any suffix through the canonical decoder (the same
    decoder the validator skeleton uses for coverage). Reuses
    `roundtrip`; generic over all inputs. -/
theorem compose_bytes_revalidated (flagsLive : Bool) (dst : Register)
    (suffix : List Byte) :
    decode (encode (composeInstr flagsLive dst) ++ suffix) =
      some (⟨composeInstr flagsLive dst,
        (encode (composeInstr flagsLive dst)).length⟩, suffix) :=
  roundtrip _ _

/-- Planted profile refusal: the flush-to-zero control word disarms the
    MXCSR profile, so scalar double is refused even on full silicon.
    Reuses `sse_verweigert_bei_ftz` and `waehle_verweigert_strikt`. -/
theorem compose_profil_verweigert :
    waehle basisHw ⟨0x9F80, true⟩ .sseDoppel = none :=
  waehle_verweigert_strikt _ _ _ sse_verweigert_bei_ftz

/-- Planted checker refusal through the composed step: the clobbering
    composed form under live flags is refused. Reuses
    `wahlOk_verweigert_xor_le`. -/
theorem compose_live_refuses_clobber (dst : Register) :
    wahlOk true [composeInstr false dst] = false := by
  have h1 : composeInstr false dst = .xorReg64 dst dst := rfl
  rw [h1]
  exact wahlOk_verweigert_xor_le dst

/-- Positive twin: the same composed form under dead flags is allowed.
    Reuses `wahlOk_erlaubt_tot`. -/
theorem compose_dead_allows_clobber (dst : Register) :
    wahlOk false [composeInstr false dst] = true := by
  have h1 : composeInstr false dst = .xorReg64 dst dst := rfl
  rw [h1]
  exact wahlOk_erlaubt_tot dst

/-- Closing composition over arbitrary admitted inputs: the composed
    bytes re-decode, the composed step zeroes its register (so the
    profile choice is tuning only), a refused feature falls back to the
    scalar path, and a nonzero memory-changing write/read is reached.
    Every producer fact is reused by name; nothing is re-proved. -/
theorem ComposeProfileSelect_verbindung
    (hw : HwProfil) (b : BereitProfil) (m : PerfMerkmal)
    (flagsLive : Bool) (dst : Register) (suffix : List Byte)
    (s : Zustand) :
    decode (encode (composeInstr flagsLive dst) ++ suffix) =
      some (⟨composeInstr flagsLive dst,
        (encode (composeInstr flagsLive dst)).length⟩, suffix)
    ∧ (schritt ⟨composeInstr flagsLive dst,
        (encode (composeInstr flagsLive dst)).length⟩ s).map
        (fun s' => s'.register dst) = some 0
    ∧ (waehle hw b m = none → composeMerkmal hw b m = .skalar64)
    ∧ (∃ (mm mm' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 mm a v = some mm' ∧ read64 mm' a = some v ∧
          mm.bytes a ≠ mm'.bytes a) := by
  refine ⟨compose_bytes_revalidated _ _ _,
    compose_zero _ _ _,
    fun h => compose_fallback_closed _ _ _ h,
    schreibLese_zeuge⟩

/-- Joint companion: all `verbindung` inputs jointly inhabited at
    concrete values (baseline profiles, scalar feature, dead flags,
    `rax`, empty suffix, the validator witness state), together with
    the non-degenerate source side -- a contract writing its table
    (`wit_schreibt`) and the reached memory-changing run (`wit_step`). -/
theorem ComposeProfileSelect_verbindung_zeuge :
    decode (encode (composeInstr false .rax) ++ ([] : List Byte)) =
      some (⟨composeInstr false .rax,
        (encode (composeInstr false .rax)).length⟩, ([] : List Byte))
    ∧ (schritt ⟨composeInstr false .rax,
        (encode (composeInstr false .rax)).length⟩
        valZeugeZustand).map (fun s' => s'.register .rax) = some 0
    ∧ (waehle basisHw basisBereit .skalar64 = none →
        composeMerkmal basisHw basisBereit .skalar64 = .skalar64)
    ∧ (∃ (mm mm' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 mm a v = some mm' ∧ read64 mm' a = some v ∧
          mm.bytes a ≠ mm'.bytes a)
    ∧ InvariantenOpt.wV.schreibt () = true
    ∧ (match Gabbro.Grammatik.execBlock InvariantenOpt.wO 5
        InvariantenOpt.wR InvariantenOpt.wRest InvariantenOpt.wWorld0
        Gabbro.Grammatik.Env.nil with
      | .ok σ' _ => (σ'.slots () 0 ()).n = 5
      | _ => False) := by
  obtain ⟨hdec, hexe, hfail, hmem⟩ :=
    ComposeProfileSelect_verbindung basisHw basisBereit .skalar64
      false .rax [] valZeugeZustand
  exact ⟨hdec, hexe, hfail, hmem,
    InvariantenOpt.wit_schreibt, InvariantenOpt.wit_step⟩

/- CUTS: what is not proved here.

   - No validator-image embedding: `valX86` acceptance of an image
     carrying the composed bytes is not shown here; re-validation is
     decode-level through the same canonical decoder the skeleton uses
     for coverage (`roundtrip`). Full `valX86_sound` (source
     correspondence, refinement, TSO/GX bridge) stays with owner 349.
   - No source lowering: no correspondence between a Gabbro source form
     and the selected feature; the source side appears only as the
     reused non-degeneracy witness (`wit_schreibt`, `wit_step` from
     lane 600's vocabulary). No `Ty`/Spec/checker/emitter change, no
     budget transfer for the fallback path, no call-log effect.
   - No hardware claim: bytes are model `Byte` lists, memory the model
     `Speicher`; silicon, caches, store buffers, interrupts, faults
     beyond the decoded refusal and FP control stay with their owners
     (FeatureProfile, Gleitprofil, TSO lanes).
   - No cost/time claim: shorter bytes change timing, unmodelled; the
     profile choice is tuning only for VALUES, never a speed proof.
   - Only the zeroing form family is composed (`movImm64 0` vs
     `xor dst dst`); multiply/shift/vector/LOCK and wider selection
     stay with their owners.
-/

#print axioms composeInstr_eq_waehleNull
#print axioms compose_fallback_closed
#print axioms compose_zero
#print axioms compose_bytes_revalidated
#print axioms compose_profil_verweigert
#print axioms compose_live_refuses_clobber
#print axioms compose_dead_allows_clobber
#print axioms ComposeProfileSelect_verbindung
#print axioms ComposeProfileSelect_verbindung_zeuge

end Gabbro.Grammatik.X86.ComposeProfileSelect
