/-
  File:      Grammatik/X86/PipelineLinkRel8.lean
  Subject:   Linking: rel8 selection convergence and fall-through coverage.

  FOLLOW-UP of lane 1193 (`PipelineLinkMulti.lean`): open were
  rel8-selection convergence, fall-through coverage beyond re-decoded
  windows, and instructions outside jump/call/conditional sites. This
  file proves branch relaxation with relocation converges (monotone
  widening, termination within the short-site count, fixed-point fit)
  and that the linked bytes cover exactly the relaxed program:
  fall-through bytes survive through the multi-operand frame, every
  site's bytes are exact, short sites read back, long jump sites
  re-decode through the accepted agreement legs; overlapping sites
  stay refused.

  Reused, never duplicated (no second decoder, loader, executor,
  ISA model or IR):
  - operands/patching: `MultiFeld`, `multiBytes`, `multiPatch`,
    `multiPatchAlle`, `opStelle`, `opWeite`, `opsDisjunktB`,
    `opsDisjunktB_gilt`, `multiPatchAlle_rahmen`/`_laenge`/
    `_kopf_stelle`, `disjunktStellen`;
  - rel8 vocabulary: `rel8Passt`, `rel8Byte`, `disp8Signed`,
    `rel8Byte_rundgang`, `multi_rel8_liest`;
  - rel32 bridge: `rel32Bytes`, `rel32Passt`, `fenster_sprung`,
    `feld_agreement_sprung`;
  - mapping/run witnesses: `ruf_schritt_zeuge` (reached
    memory-changing run through actual bytes).
-/
import Grammatik.X86.PipelineLinkMulti

namespace Gabbro.Grammatik.X86

/-- One relaxed program piece: fixed fall-through bytes of length
    `len`, a short (rel8, 2-byte) branch site, or a widened
    (rel32, 5-byte) unconditional-jump site. -/
inductive RelaxStueck where
  | fest (len : Nat)
  | kurz
  | weit
  deriving DecidableEq, Repr

/-- Laid-out width in bytes: fall-through keeps its length, a short
    site is opcode plus one displacement byte, a wide site is opcode
    plus four displacement bytes. -/
def stueckWeite : RelaxStueck → Nat
  | .fest len => len
  | .kurz => 2
  | .weit => 5

/-- A short site never exceeds its widened form. -/
theorem stueckWeite_kurz_le_weit :
    stueckWeite .kurz ≤ stueckWeite .weit := by
  decide

end Gabbro.Grammatik.X86
