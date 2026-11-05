/-
  File:      Grammatik/Parser/Elab/UebersetzeProben3.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects of wall 7 (`entry` roots), split from
             `UebersetzeProben2` so that each file stays small. Kernel probes of one file share one memory budget (measured 2026-09-30:
             the first file alone passed 7 GB).
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3Lexical
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben3

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-! WALL 7 (2026-09-30): `entry ... dispatch f;` -- the dispatch target is a THREAD ROOT of the unit
    (`UProg.wurzeln`, `Einheit.starts` in the bridge). An entry with a handler word (`via`) is a root AND a
    handler (`UProg.handler`, `Programm.unterbricht`); one that dispatches to a function with parameters, and
    one that names no function of the unit, are refused. `concurrent` members are roots too (first).
    The sources are SHORT on purpose: the kernel lexes them (2.7 GB for a 300-character text). -/

theorem entry1_ok_stufe : stufe entry1_ok = "OK" := by decide +kernel

theorem entry_two_ok_stufe : stufe entry_two_ok = "OK" := by decide +kernel

theorem entry_via_ok_stufe : stufe entry_via_ok = "OK" := by decide +kernel

theorem entry_params_refused_stufe : stufe entry_params_refused = "elab: dispatch names a function with parameters: no start-argument form: p" := by decide +kernel

theorem entry_unknown_refused_stufe : stufe entry_unknown_refused = "elab: dispatch names an unknown function: nix" := by decide +kernel

theorem via_is_root_and_handler : roots entry_via_ok = some (["w"], ["w"]) := by decide +kernel
theorem plain_entry_is_no_handler : roots entry1_ok = some (["w"], []) := by decide +kernel


theorem conc_ok_roots : roots conc_ok = some (["w", "v"], []) := by decide +kernel

theorem concurrent_roots_come_first : roots conc_first = some (["w", "v"], []) := by decide +kernel

/-- A start with its arguments (`concurrent { m::f(a, b) }`): one value per parameter. -/
theorem conc_args_ok_roots : roots conc_args_ok = some (["p"], []) := by decide +kernel

/-- A start without the arguments its function needs. -/
theorem conc_params_refused_stufe :
    stufe conc_params_refused = "elab: concurrent member with 0 arguments for 1 parameters: p" := by
  decide +kernel

/-- A start argument outside its parameter's range. -/
theorem conc_arg_range_refused_stufe :
    stufe conc_arg_range_refused = "elab: concurrent member with an argument outside its parameter's type: p" := by
  decide +kernel

/-- A pointer parameter is started with `&T`, the one pointer to the carrier its type names. -/
theorem conc_ptr_ok_roots : roots conc_ptr_ok = some (["p"], []) := by decide +kernel

/-- Twin: `&U` for a pointer into `T` is refused. -/
theorem conc_ptr_refused_stufe :
    stufe conc_ptr_refused = "elab: concurrent member with an argument outside its parameter's type: p" := by
  decide +kernel

theorem conc_unknown_refused_stufe :
    stufe conc_unknown_refused = "elab: concurrent member names an unknown function: nix" := by decide +kernel

/-! `masks irqs` on a lock is `D.maskiert`: the lock of the elaborated program says so, and any other mask
    word is refused. -/


theorem mask_irqs_is_read : maskFlags mask_src = some [true] := by decide +kernel
theorem mask_irqs_lowers : stufe mask_src = "OK" := by decide +kernel
theorem lock_without_mask : maskFlags locks_plain = some [false] := by decide +kernel
theorem other_mask_refused :
    stufe "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks nmi; }"
      = "elab: lock masks something but irqs: no G form" := by decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben3
