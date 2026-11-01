/-
  File:      Grammatik/SchablonenOhneLibc.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-TRANSLATION-VALIDATION.md), the two templates
             of a program without a C library (C-free lane, 2026-09-30).

  Rows of `crates/gabbro-check/src/schablonen.rs`:

  * `tor.nie` -- the `_Noreturn` stub of a `-> never` gate
    (`emit.rs::syscall_stumpf`, `Antwort::Nie`): `static _Noreturn void g(…)`,
    the `syscall` instruction, then `__builtin_unreachable()`. SEMANTICS-TIED:
    over the real block semantics (`execBlock`, Semantik.lean), a call of an
    axiom whose declared answer is `never` never runs what stands behind it --
    under EVERY oracle, so no assumption about the machine is spent on it --
    and the head it stops at is the goal theorem's named stop `nieZurueck`
    (`KopfHalt`, Zielsatz/Spec.lean). That is exactly what the C promises
    with `_Noreturn` and `__builtin_unreachable()`: the code behind the call
    is dead in G as in the C.
    **Witness:** the real certified program `beispiele/174` (its gate
    `exit_group`, `Schablonen/ZeugeTorModell.lean`, a frozen export).

  * `start.nolibc` -- the generated process entry of a `nolibc` program
    (`bau.rs::prozess_start`): `xor %ebp,%ebp; and $-16,%rsp; call main; ud2`.
    An ABSTRACT CORE like the rows of SchablonenT5.lean: machine G has no
    process entry (the loader and the thread start are the runtime premise
    (d), `Laufzeit`), so the core is stated over a small model of the three
    instructions -- NOT tied to `execBlock`. It proves the two things the
    stub is for: the stack pointer `main` sees meets the x86_64 SysV entry
    alignment and the return address lands BELOW the kernel's stack pointer
    (argc stays intact), and the trailing `ud2` is reached only if `main`
    returns -- which the entry rule and `S009` exclude.

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness
  instantiating ALL its premises jointly.
-/
module

public import Grammatik.Bausteine.Schablonen.SchablonenOhneLibc.Teil1
public import Grammatik.Bausteine.Schablonen.SchablonenOhneLibc.Teil2
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
