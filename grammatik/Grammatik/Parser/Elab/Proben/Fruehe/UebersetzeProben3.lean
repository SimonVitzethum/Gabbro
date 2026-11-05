/-
  File:      Grammatik/Parser/Elab/UebersetzeProben3.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects of wall 7 (`entry` roots), split from
             `UebersetzeProben2` so that each file stays small. Kernel probes of one file share one memory budget (measured 2026-09-30:
             the first file alone passed 7 GB).
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3Frontend
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

theorem entry1_ok_stufe : stufe entry1_ok = "OK" :=
  stufe_after (source := entry1_ok) (characters := entry1_ok_characters)
    (tokens := entry1_ok_tokens) (items := entry1_ok_items) (unit := entry1_ok_unit)
    entry1_ok_text entry1_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry1_ok_tokens) entry1_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry1_ok_items)) entry1_ok_elaborated) entry1_ok_lowered

theorem entry_two_ok_stufe : stufe entry_two_ok = "OK" :=
  stufe_after (source := entry_two_ok) (characters := entry_two_ok_characters)
    (tokens := entry_two_ok_tokens) (items := entry_two_ok_items) (unit := entry_two_ok_unit)
    entry_two_ok_text entry_two_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry_two_ok_tokens) entry_two_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry_two_ok_items)) entry_two_ok_elaborated) entry_two_ok_lowered

theorem entry_via_ok_stufe : stufe entry_via_ok = "OK" :=
  stufe_after (source := entry_via_ok) (characters := entry_via_ok_characters)
    (tokens := entry_via_ok_tokens) (items := entry_via_ok_items) (unit := entry_via_ok_unit)
    entry_via_ok_text entry_via_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry_via_ok_tokens) entry_via_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry_via_ok_items)) entry_via_ok_elaborated) entry_via_ok_lowered

theorem entry_params_refused_stufe : stufe entry_params_refused = "elab: dispatch names a function with parameters: no start-argument form: p" :=
  stufe_elab_error (source := entry_params_refused) (characters := entry_params_refused_characters)
    (tokens := entry_params_refused_tokens) (items := entry_params_refused_items)
    entry_params_refused_text entry_params_refused_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry_params_refused_tokens) entry_params_refused_parsed) entry_params_refused_elaborated

theorem entry_unknown_refused_stufe : stufe entry_unknown_refused = "elab: dispatch names an unknown function: nix" :=
  stufe_elab_error (source := entry_unknown_refused) (characters := entry_unknown_refused_characters)
    (tokens := entry_unknown_refused_tokens) (items := entry_unknown_refused_items)
    entry_unknown_refused_text entry_unknown_refused_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry_unknown_refused_tokens) entry_unknown_refused_parsed) entry_unknown_refused_elaborated

theorem via_is_root_and_handler : roots entry_via_ok = some (["w"], ["w"]) :=
  roots_after (source := entry_via_ok) (characters := entry_via_ok_characters)
    (tokens := entry_via_ok_tokens) (items := entry_via_ok_items) (unit := entry_via_ok_unit)
    entry_via_ok_text entry_via_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry_via_ok_tokens) entry_via_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry_via_ok_items)) entry_via_ok_elaborated) entry_via_ok_metadata.2.2.2
theorem plain_entry_is_no_handler : roots entry1_ok = some (["w"], []) :=
  roots_after (source := entry1_ok) (characters := entry1_ok_characters)
    (tokens := entry1_ok_tokens) (items := entry1_ok_items) (unit := entry1_ok_unit)
    entry1_ok_text entry1_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry1_ok_tokens) entry1_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry1_ok_items)) entry1_ok_elaborated) entry1_ok_metadata.2.2.2


theorem conc_ok_roots : roots conc_ok = some (["w", "v"], []) :=
  roots_after (source := conc_ok) (characters := conc_ok_characters)
    (tokens := conc_ok_tokens) (items := conc_ok_items) (unit := conc_ok_unit)
    conc_ok_text conc_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_ok_tokens) conc_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_ok_items)) conc_ok_elaborated) conc_ok_metadata

theorem concurrent_roots_come_first : roots conc_first = some (["w", "v"], []) :=
  roots_after (source := conc_first) (characters := conc_first_characters)
    (tokens := conc_first_tokens) (items := conc_first_items) (unit := conc_first_unit)
    conc_first_text conc_first_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_first_tokens) conc_first_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_first_items)) conc_first_elaborated) conc_first_metadata

/-- A start with its arguments (`concurrent { m::f(a, b) }`): one value per parameter. -/
theorem conc_args_ok_roots : roots conc_args_ok = some (["p"], []) :=
  roots_after (source := conc_args_ok) (characters := conc_args_ok_characters)
    (tokens := conc_args_ok_tokens) (items := conc_args_ok_items) (unit := conc_args_ok_unit)
    conc_args_ok_text conc_args_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_args_ok_tokens) conc_args_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_args_ok_items)) conc_args_ok_elaborated) conc_args_ok_metadata

/-- A start without the arguments its function needs. -/
theorem conc_params_refused_stufe :
    stufe conc_params_refused = "elab: concurrent member with 0 arguments for 1 parameters: p" :=
  stufe_elab_error (source := conc_params_refused) (characters := conc_params_refused_characters)
    (tokens := conc_params_refused_tokens) (items := conc_params_refused_items)
    conc_params_refused_text conc_params_refused_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_params_refused_tokens) conc_params_refused_parsed) conc_params_refused_elaborated

/-- A start argument outside its parameter's range. -/
theorem conc_arg_range_refused_stufe :
    stufe conc_arg_range_refused = "elab: concurrent member with an argument outside its parameter's type: p" :=
  stufe_elab_error (source := conc_arg_range_refused) (characters := conc_arg_range_refused_characters)
    (tokens := conc_arg_range_refused_tokens) (items := conc_arg_range_refused_items)
    conc_arg_range_refused_text conc_arg_range_refused_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_arg_range_refused_tokens) conc_arg_range_refused_parsed) conc_arg_range_refused_elaborated

/-- A pointer parameter is started with `&T`, the one pointer to the carrier its type names. -/
theorem conc_ptr_ok_roots : roots conc_ptr_ok = some (["p"], []) :=
  roots_after (source := conc_ptr_ok) (characters := conc_ptr_ok_characters)
    (tokens := conc_ptr_ok_tokens) (items := conc_ptr_ok_items) (unit := conc_ptr_ok_unit)
    conc_ptr_ok_text conc_ptr_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_ptr_ok_tokens) conc_ptr_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_ptr_ok_items)) conc_ptr_ok_elaborated) conc_ptr_ok_metadata

/-- Twin: `&U` for a pointer into `T` is refused. -/
theorem conc_ptr_refused_stufe :
    stufe conc_ptr_refused = "elab: concurrent member with an argument outside its parameter's type: p" :=
  stufe_elab_error (source := conc_ptr_refused) (characters := conc_ptr_refused_characters)
    (tokens := conc_ptr_refused_tokens) (items := conc_ptr_refused_items)
    conc_ptr_refused_text conc_ptr_refused_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_ptr_refused_tokens) conc_ptr_refused_parsed) conc_ptr_refused_elaborated

theorem conc_unknown_refused_stufe :
    stufe conc_unknown_refused = "elab: concurrent member names an unknown function: nix" :=
  stufe_elab_error (source := conc_unknown_refused) (characters := conc_unknown_refused_characters)
    (tokens := conc_unknown_refused_tokens) (items := conc_unknown_refused_items)
    conc_unknown_refused_text conc_unknown_refused_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief conc_unknown_refused_tokens) conc_unknown_refused_parsed) conc_unknown_refused_elaborated

/-! `masks irqs` on a lock is `D.maskiert`: the lock of the elaborated program says so, and any other mask
    word is refused. -/


theorem mask_irqs_is_read : maskFlags mask_src = some [true] :=
  masks_after (source := mask_src) (characters := mask_src_characters)
    (tokens := mask_src_tokens) (items := mask_src_items) (unit := mask_src_unit)
    mask_src_text mask_src_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief mask_src_tokens) mask_src_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 mask_src_items)) mask_src_elaborated) mask_src_metadata.2.2.2
theorem mask_irqs_lowers : stufe mask_src = "OK" :=
  stufe_after (source := mask_src) (characters := mask_src_characters)
    (tokens := mask_src_tokens) (items := mask_src_items) (unit := mask_src_unit)
    mask_src_text mask_src_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief mask_src_tokens) mask_src_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 mask_src_items)) mask_src_elaborated) mask_src_lowered
theorem lock_without_mask : maskFlags locks_plain = some [false] :=
  masks_after (source := locks_plain) (characters := locks_plain_characters)
    (tokens := locks_plain_tokens) (items := locks_plain_items) (unit := locks_plain_unit)
    locks_plain_text locks_plain_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief locks_plain_tokens) locks_plain_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_plain_items)) locks_plain_elaborated) locks_plain_metadata
theorem other_mask_refused :
    stufe "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks nmi; }"
      = "elab: lock masks something but irqs: no G form" :=
  stufe_elab_error (source := "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks nmi; }") (characters := other_mask_characters)
    (tokens := other_mask_tokens) (items := other_mask_items)
    other_mask_text other_mask_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief other_mask_tokens) other_mask_parsed) other_mask_elaborated

end Gabbro.Grammatik.Parser.UebersetzeProben3
