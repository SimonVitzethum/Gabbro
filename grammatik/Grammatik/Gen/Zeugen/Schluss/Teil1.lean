module

public import Grammatik.Gen.Zeugen.Erreicht
public import Grammatik.Gen.Zeugen.Reset
public import Grammatik.Gen.Zeugen.Gap.M99_824
public import Grammatik.Gen.Zeugen.Gap.M99_825
public import Grammatik.Gen.Zeugen.Gap.M47_549
public import Grammatik.Gen.Zeugen.Gap.M169_350
public import Grammatik.Gen.Zeugen.M.M16_13
public import Grammatik.Gen.Zeugen.Gap.M49_50
public import Grammatik.Gen.Zeugen.Gap.M103_803
public import Grammatik.Gen.Zeugen.Gap.M103_131
public import Grammatik.Gen.Zeugen.N.N16_5
public import Grammatik.Gen.Zeugen.N.N18_0
public import Grammatik.Gen.Zeugen.N.N18_4
public import Grammatik.Gen.Zeugen.N.N19_0
public import Grammatik.Gen.Zeugen.N.N19_2
public import Grammatik.Gen.Zeugen.N.N19_5
public import Grammatik.Gen.Zeugen.N.N19_7
public import Grammatik.Gen.Zeugen.N.N20_1
public import Grammatik.Gen.Zeugen.N.N23_4
public import Grammatik.Gen.Zeugen.N.N24_0
public import Grammatik.Gen.Zeugen.N.N3_0
public import Grammatik.Gen.Zeugen.N.N47_P
public import Grammatik.Gen.Zeugen.N.N47_45
public import Grammatik.Gen.Abdeckung.Satz.Neutral
public import Grammatik.Gen.Abdeckung.Satz.Unmoeglich
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


set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Gabbro.Grammatik.Gen.Zeugen

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz

theorem zellAlle_liste : zellAlle = [
    ⟨0, 0, true, [false, false, false]⟩,
    ⟨0, 0, true, [true, false, false]⟩,
    ⟨0, 0, true, [false, true, false]⟩,
    ⟨0, 0, true, [true, true, false]⟩,
    ⟨0, 0, true, [false, false, true]⟩,
    ⟨0, 0, true, [true, false, true]⟩,
    ⟨0, 0, true, [false, true, true]⟩,
    ⟨0, 0, true, [true, true, true]⟩,
    ⟨1, 0, true, [false, false, false]⟩,
    ⟨1, 0, true, [true, false, false]⟩,
    ⟨1, 0, true, [false, true, false]⟩,
    ⟨1, 0, true, [true, true, false]⟩,
    ⟨1, 0, true, [false, false, true]⟩,
    ⟨1, 0, true, [true, false, true]⟩,
    ⟨1, 0, true, [false, true, true]⟩,
    ⟨1, 0, true, [true, true, true]⟩,
    ⟨2, 0, true, [false, false, false, false]⟩,
    ⟨2, 0, true, [true, false, false, false]⟩,
    ⟨2, 0, true, [false, true, false, false]⟩,
    ⟨2, 0, true, [true, true, false, false]⟩,
    ⟨2, 0, true, [false, false, true, false]⟩,
    ⟨2, 0, true, [true, false, true, false]⟩,
    ⟨2, 0, true, [false, true, true, false]⟩,
    ⟨2, 0, true, [true, true, true, false]⟩,
    ⟨2, 0, true, [false, false, false, true]⟩,
    ⟨2, 0, true, [true, false, false, true]⟩,
    ⟨2, 0, true, [false, true, false, true]⟩,
    ⟨2, 0, true, [true, true, false, true]⟩,
    ⟨2, 0, true, [false, false, true, true]⟩,
    ⟨2, 0, true, [true, false, true, true]⟩,
    ⟨2, 0, true, [false, true, true, true]⟩,
    ⟨2, 0, true, [true, true, true, true]⟩,
    ⟨2, 1, true, [false, false]⟩,
    ⟨2, 1, true, [true, false]⟩,
    ⟨2, 1, true, [false, true]⟩,
    ⟨2, 1, true, [true, true]⟩,
    ⟨2, 2, false, [false, false, false]⟩,
    ⟨2, 2, false, [true, false, false]⟩,
    ⟨2, 2, false, [false, true, false]⟩,
    ⟨2, 2, false, [true, true, false]⟩,
    ⟨2, 2, false, [false, false, true]⟩,
    ⟨2, 2, false, [true, false, true]⟩,
    ⟨2, 2, false, [false, true, true]⟩,
    ⟨2, 2, false, [true, true, true]⟩,
    ⟨2, 3, false, [false, false, false]⟩,
    ⟨2, 3, false, [true, false, false]⟩,
    ⟨2, 3, false, [false, true, false]⟩,
    ⟨2, 3, false, [true, true, false]⟩,
    ⟨2, 3, false, [false, false, true]⟩,
    ⟨2, 3, false, [true, false, true]⟩,
    ⟨2, 3, false, [false, true, true]⟩,
    ⟨2, 3, false, [true, true, true]⟩,
    ⟨3, 0, true, [false, false]⟩,
    ⟨3, 0, true, [true, false]⟩,
    ⟨3, 0, true, [false, true]⟩,
    ⟨3, 0, true, [true, true]⟩,
    ⟨4, 0, true, [false, false]⟩,
    ⟨4, 0, true, [true, false]⟩,
    ⟨4, 0, true, [false, true]⟩,
    ⟨4, 0, true, [true, true]⟩,
    ⟨5, 0, true, [false, false]⟩,
    ⟨5, 0, true, [true, false]⟩,
    ⟨5, 0, true, [false, true]⟩,
    ⟨5, 0, true, [true, true]⟩,
    ⟨6, 0, true, [false, false, false]⟩,
    ⟨6, 0, true, [true, false, false]⟩,
    ⟨6, 0, true, [false, true, false]⟩,
    ⟨6, 0, true, [true, true, false]⟩,
    ⟨6, 0, true, [false, false, true]⟩,
    ⟨6, 0, true, [true, false, true]⟩,
    ⟨6, 0, true, [false, true, true]⟩,
    ⟨6, 0, true, [true, true, true]⟩,
    ⟨6, 1, true, [false, false, false, false]⟩,
    ⟨6, 1, true, [true, false, false, false]⟩,
    ⟨6, 1, true, [false, true, false, false]⟩,
    ⟨6, 1, true, [true, true, false, false]⟩,
    ⟨6, 1, true, [false, false, true, false]⟩,
    ⟨6, 1, true, [true, false, true, false]⟩,
    ⟨6, 1, true, [false, true, true, false]⟩,
    ⟨6, 1, true, [true, true, true, false]⟩,
    ⟨6, 1, true, [false, false, false, true]⟩,
    ⟨6, 1, true, [true, false, false, true]⟩,
    ⟨6, 1, true, [false, true, false, true]⟩,
    ⟨6, 1, true, [true, true, false, true]⟩,
    ⟨6, 1, true, [false, false, true, true]⟩,
    ⟨6, 1, true, [true, false, true, true]⟩,
    ⟨6, 1, true, [false, true, true, true]⟩,
    ⟨6, 1, true, [true, true, true, true]⟩,
    ⟨7, 0, true, [false, false]⟩,
    ⟨7, 0, true, [true, false]⟩,
    ⟨7, 0, true, [false, true]⟩,
    ⟨7, 0, true, [true, true]⟩,
    ⟨7, 1, false, [false, false, false]⟩,
    ⟨7, 1, false, [true, false, false]⟩,
    ⟨7, 1, false, [false, true, false]⟩,
    ⟨7, 1, false, [true, true, false]⟩,
    ⟨7, 1, false, [false, false, true]⟩,
    ⟨7, 1, false, [true, false, true]⟩,
    ⟨7, 1, false, [false, true, true]⟩,
    ⟨7, 1, false, [true, true, true]⟩,
    ⟨8, 0, true, [false, false, false]⟩,
    ⟨8, 0, true, [true, false, false]⟩,
    ⟨8, 0, true, [false, true, false]⟩,
    ⟨8, 0, true, [true, true, false]⟩,
    ⟨8, 0, true, [false, false, true]⟩,
    ⟨8, 0, true, [true, false, true]⟩,
    ⟨8, 0, true, [false, true, true]⟩,
    ⟨8, 0, true, [true, true, true]⟩,
    ⟨9, 0, true, [false, false, false, false]⟩,
    ⟨9, 0, true, [true, false, false, false]⟩,
    ⟨9, 0, true, [false, true, false, false]⟩,
    ⟨9, 0, true, [true, true, false, false]⟩,
    ⟨9, 0, true, [false, false, true, false]⟩,
    ⟨9, 0, true, [true, false, true, false]⟩,
    ⟨9, 0, true, [false, true, true, false]⟩,
    ⟨9, 0, true, [true, true, true, false]⟩,
    ⟨9, 0, true, [false, false, false, true]⟩,
    ⟨9, 0, true, [true, false, false, true]⟩,
    ⟨9, 0, true, [false, true, false, true]⟩,
    ⟨9, 0, true, [true, true, false, true]⟩,
    ⟨9, 0, true, [false, false, true, true]⟩,
    ⟨9, 0, true, [true, false, true, true]⟩,
    ⟨9, 0, true, [false, true, true, true]⟩,
    ⟨9, 0, true, [true, true, true, true]⟩,
    ⟨10, 0, true, [false]⟩,
    ⟨10, 0, true, [true]⟩] := by decide


end Gabbro.Grammatik.Gen.Zeugen
