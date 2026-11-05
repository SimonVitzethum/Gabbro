module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Fragments

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
namespace Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning
set_option maxRecDepth 100000

-- Separate each small numeric certificate from later multi-fragment inputs.
scoped macro "bound_fragment " fragment:ident : command => do
  let bound := Lean.mkIdentFrom fragment (fragment.getId.appendAfter "_bounded")
  `(command| theorem $bound :
      decide (($fragment : Chunk).steps ≤ ($fragment : Chunk).characters.length) = true := by
        cbv)

open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
namespace Inputs

bound_fragment cut0
bound_fragment cut1
bound_fragment cut2
bound_fragment cut3
bound_fragment cut4
bound_fragment cut5
bound_fragment cut6
bound_fragment cut7
bound_fragment cut8
bound_fragment cut9
bound_fragment cut10
bound_fragment cut11
bound_fragment cut12
bound_fragment cut13
bound_fragment cut14
bound_fragment cut15
bound_fragment cut16
bound_fragment cut17
bound_fragment cut18
bound_fragment cut19
bound_fragment cut20
bound_fragment cut21
bound_fragment cut22
bound_fragment cut23
bound_fragment cut24
bound_fragment cut25
bound_fragment cut26
bound_fragment cut27
bound_fragment cut28
bound_fragment cut29
bound_fragment cut30
bound_fragment cut31
bound_fragment cut32
bound_fragment cut33
bound_fragment cut34
bound_fragment cut35
bound_fragment cut36
bound_fragment cut37
bound_fragment cut38
bound_fragment cut39
bound_fragment cut40
bound_fragment cut41
bound_fragment cut42
bound_fragment cut43
bound_fragment cut44
bound_fragment cut45
bound_fragment cut46
bound_fragment cut47
bound_fragment cut48
bound_fragment cut49
bound_fragment cut50
bound_fragment cut51
bound_fragment cut52
bound_fragment cut53
bound_fragment cut54
bound_fragment cut55
bound_fragment cut56
bound_fragment cut57
bound_fragment cut58
bound_fragment cut59
bound_fragment cut60
bound_fragment cut61
bound_fragment cut62
bound_fragment cut63
bound_fragment cut64
bound_fragment cut65
bound_fragment cut66
bound_fragment cut67
bound_fragment cut68
bound_fragment cut69
bound_fragment cut70
bound_fragment cut71
bound_fragment cut72
bound_fragment cut73
bound_fragment cut74
bound_fragment cut75
bound_fragment cut76
bound_fragment cut77
bound_fragment cut78
bound_fragment cut79
bound_fragment cut80
bound_fragment cut81
bound_fragment cut82
bound_fragment cut83
bound_fragment cut84
bound_fragment cut85
bound_fragment cut86
bound_fragment cut87
bound_fragment cut88
bound_fragment cut89
bound_fragment cut90
bound_fragment cut91
bound_fragment cut92
bound_fragment cut93
bound_fragment cut94
bound_fragment cut95
bound_fragment cut96
bound_fragment cut97
bound_fragment cut98
bound_fragment cut99
bound_fragment cut100
bound_fragment cut101
bound_fragment cut102

end Inputs
end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
