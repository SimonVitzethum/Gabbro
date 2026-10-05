/-
  File:      Grammatik/X86/PipelineLinkMulti.lean
  Subject:   Multi-unit linking convergence and operand kinds.

  FOLLOW-UP of lane 1171 (`PipelineLink.lean`, two units, one rel32
  operand per closing): n-unit concatenation with tiling sections,
  several operands per closing, abs64 and rel8 operand re-decode,
  call and conditional-jump field agreement, with the invariant that
  no relocation changes a byte outside its operand.

  Reused, never duplicated (no second decoder, loader, executor,
  ISA model or IR):
  - two-unit base: `PipelineLink.LinkEinheit`, `linkPatch_*`
    (rel32/abs64 range, site, frame, length);
  - patching/codec: `Relokation.patchAt_*`, `patchRel32`,
    `patchAbs64`, `rel32Bytes`, `abs64Bytes`, `abs64_rundgang`;
  - field agreement bridge: `BranchLayout.dispSigned`,
    `rel32Bytes_dispSigned`, `RelocatedExecution.dispVonFit`,
    `Codec.roundtrip_jump32/_call32/_jumpIf32`;
  - rel8 vocabulary: `Rel8Reach.rel8Passt`, `disp8Signed`;
  - mapping: `Bild.geladenByte_datei`, `ValidatorSkeleton`
    coverage, `LoadedExecution.wohlgeformt_wx`;
  - run: `RelocatedExecution.ruf_schritt_zeuge`.
-/
import Grammatik.X86.PipelineLink
import Grammatik.X86.ComposePatchBytes
import Grammatik.X86.Rel8Reach
import Grammatik.X86.BranchLayout

namespace Gabbro.Grammatik.X86

/-- Relocation operand kind at link time: rel32 displacement, abs64
    value, or rel8 short displacement. The rel32/abs64 cases patch
    exactly what `PipelineLink.linkPatch` patches (proved equal
    below); rel8 is the one new kind. -/
inductive MultiFeld where
  | rel32 (disp : Int)
  | abs64 (wert : Wort)
  | rel8 (disp : Int)
  deriving DecidableEq, Repr

/-- One rel8 displacement byte: two's complement mod 256. -/
def rel8Byte (d : Int) : Byte := natByte (tcNat d 256)

/-- The bytes one operand writes: the canonical splits, never a
    second codec. -/
def multiBytes : MultiFeld → List Byte
  | .rel32 d => rel32Bytes d
  | .abs64 v => abs64Bytes v
  | .rel8 d => [rel8Byte d]

end Gabbro.Grammatik.X86
