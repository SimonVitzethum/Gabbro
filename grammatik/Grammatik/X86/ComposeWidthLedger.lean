/-
  File:      Grammatik/X86/ComposeWidthLedger.lean
  Subject:   Width-ledger closing: every width conversion to its exactness lemma.

  Lane 841: skeleton only. Composes accepted NarrowOps/NarrowCodec rows over
  the canonical Wort/Speicher/Ausfuehrung vocabulary. No new machine.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.NarrowOps
import Grammatik.X86.NarrowCodec

namespace Gabbro.Grammatik.X86

/-- Width conversion ledger: every known conversion names its width;
    unknown widths carry a code and fall back loudly (`none`). -/
inductive WidthConv where
  | zeroExt (b : Breite)
  | signExt (b : Breite)
  | truncTo (b : Breite)
  | mergeTo (b : Breite)
  | unknown (code : Nat)
  deriving DecidableEq, Repr

/-- Ledger application reusing the canonical `trunc`/`sext` and the
    accepted `mergeRegNarrow`. Unknown widths answer `none`. -/
def convApply (c : WidthConv) (oldVal newVal : Wort) : Option Wort :=
  match c with
  | .zeroExt b => some (trunc b newVal)
  | .signExt b => some (sext b newVal)
  | .truncTo b => some (trunc b newVal)
  | .mergeTo b => some (mergeRegNarrow b oldVal newVal)
  | .unknown _ => none

/- CUTS:
   Skeleton: ledger type and application only. Exactness lemmas,
   composed step connection, witnesses and refusals are open.
-/

#print axioms convApply

end Gabbro.Grammatik.X86
