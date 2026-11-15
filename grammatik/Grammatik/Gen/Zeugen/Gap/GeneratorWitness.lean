/- Explicit record classes keep fragment findings outside accepted M and wrong N. -/
module

public import Grammatik.Gen.Abdeckung.ZellenSammeln
import all Init.Core
import all Init.Prelude
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

set_option maxRecDepth 2048

namespace Gabbro.Grammatik.Gen.Zeugen.Gap.GeneratorWitness

/-- Metadata stems are independent of the source module's directory. -/
def finding : Summe := ({} : Summe).zeile "LGAP\tfinding\t\tok"

theorem gap_class_zeuge : finding.leanG = [] ∧ finding.leanB = [] ∧
    finding.leanGap = [("finding", [], true)] := by cbv

/-- All three nonempty classes coexist without promoting a fragment finding. -/
def mixed : Summe :=
  (finding.zeile "LG\taccepted\t\tok").zeile "LB\twrong\t\t\tok"

theorem mixed_classes_zeuge : mixed.leanG = [("accepted", [], true)] ∧
    mixed.leanB = [("wrong", [], [], true)] ∧
    mixed.leanGap = [("finding", [], true)] := by cbv

end Gabbro.Grammatik.Gen.Zeugen.Gap.GeneratorWitness
