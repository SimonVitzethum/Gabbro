/-
  File:      stage0/Stage0/Senke/Ausdruck/Arithmetik/Wide/Literal/Probe.lean
  Subject:   Joint witness for the multiword literal on actual code and actual memory.

  Code at 2048, frame at 4096 with 24 slots, the literal in slots 8 and 9 (slot 10 is scratch). The
  value `-(2^100 + 12345)` needs the four-digit path for both limbs and its high limb is all ones in
  the top bits, so both the digit materialization and the limb split are exercised.
-/
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Probe
import Stage0.Senke.Ausdruck.Arithmetik.Wide.Literal.Wide

namespace Gabbro.Stage0.Senke.LiteralProbe
open Runner.IR Runner.Mem Gabbro.Stage0.Senke.WideProbe

abbrev litCode : List II := wideLitC 2 8 (-1267650600228229401496703217721)

theorem litCode_length : litCode.length = 34 := by decide +kernel

def litMem : Runner.Mem := probeMem litCode [0, 0, 0]

theorem wideLit_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ litMem ⟨2048 + BitVec.ofNat 64 (16 * 34), 4096⟩ m' ∧
      Agree 4096 8 24 litMem m' ∧
      WordsAt m' 4096 8 [18446744073709539271, 18446744004990074879] := by
  have far : CodeFar 2048 litCode.length 4096 24 := by rw [litCode_length]; unfold CodeFar; decide
  obtain ⟨m', run, agree, res⟩ := wideLit_run (m := litMem) (pc := 2048) (fp := 4096) (K := 24) (k := 2) (a := 8)
    (-1267650600228229401496703217721) (probe_frame _ _) (by decide) (by decide)
    (probe_code litCode _ (by decide +kernel) (by decide +kernel)) far
  rw [litCode_length] at run
  refine ⟨m', run, agree, ?_⟩
  have e : integerEncoding 2 (-1267650600228229401496703217721) =
      [18446744073709539271, 18446744004990074879] := by decide +kernel
  rw [e] at res; exact res

end Gabbro.Stage0.Senke.LiteralProbe
