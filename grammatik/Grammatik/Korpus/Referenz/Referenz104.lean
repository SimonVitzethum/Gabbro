/-
  File:      Grammatik/Referenz104.lean
  Subject:   `beispiele/0104-referenz.gab`, TRANSLATED BY HAND into the Lean
             syntax, run on machine G, and checked against the premises of
             `ziel_ort_voll`.

  ## The translation, construct by construct

  | surface (0104-referenz.gab)                    | Lean form here                                  |
  |-----------------------------------------------|-------------------------------------------------|
  | `module beispiel::referenz { … }`             | NO FORM (a namespace; this file)                |
  | `const NKONTO : u32 = 2;`                     | inlined: `count := fun _ => 2`                  |
  | `type Betrag = u32 in 0 .. 10;`               | `Ty.int 0 10` (the carrier width `u32`: NO FORM)|
  | `type Stand = u32 in 0 .. 100;`               | `Ty.int 0 100` (width: NO FORM)                 |
  | `table Konto count NKONTO { slot { stand } }` | `Tab := Unit`, `count 2`, `Feld := Unit`,       |
  |                                               | `typ := .int 0 100`, `tabNr 0 = some ()`        |
  | `lock M protects { stand } rank 0`            | `Lock := Unit`, `rang 0`, `braucht := [.inl M]` |
  | `held <= 50 ops` (lock hold budget)           | NO FORM (no hold budget in `Deklaration`)       |
  | `impl fn einzahlen(k : ptr<normal, rw> Konto, | params `[.ptr 0 true, .index 2, .int 0 10]`;    |
  |   i : index into Konto, b : Betrag)`          | the address space `normal`: NO FORM             |
  | `requires Held(M)`                            | `haelt := [M]`, `requires := .tru`             |
  | `ensures old(k.slots[i].stand) <=             | `.le (.oldS Konto stand i) (.thru k … i)`;  |
  |   k.slots[i].stand`                           | `old(p->…)` has no pointer form (`altDurch`):   |
  |                                               | written `altSlot` of the table the type names   |
  | `effects { reads k.slots, writes k.slots,     | `schreibt := true`; `reads`: NO FORM (reads are |
  |   locks M }`                                  | the computed footprint); `locks M`: `haelt`     |
  | `costs <= 16 ops` / `<= 8 ops`                | `r4Decl` with `kostenPasst` (`KostenG.lean`)    |
  | `k.slots[i].stand = 100;`                     | `.assignThru (.var k) Konto rfl stand (.var i) |
  |                                               |   100 rfl hL`                                   |
  | `lies(k, i);`                                 | `.call lies [ptrOf Konto false, var i] hp rfl`: |
  |                                               | a `rw` pointer passed as `r` has no coercion    |
  |                                               | form; `ptrOf` of the same table (a pointer's    |
  |                                               | value is `()`, the denotation is identical)     |
  | end of `einzahlen` (falls off)                | `.ret .empty perm` (an `Endblock` must end)     |
  | `impl fn lies(k : ptr<normal, r> Konto,       | params `[.ptr 0 false, .index 2]`,              |
  |   i : index into Konto) -> Stand`             | `erg := some (.int 0 100)`                      |
  | `ensures result == k.slots[i].stand`          | `.eq (.var .here) (.thru k … i)`               |
  | `effects { reads k.slots, locks M }`          | `schreibt := false`, `haelt := [M]`             |
  | `return k.slots[i].stand;`                    | `.ret (.val (.thru (.var k) … (.var i))) perm`|

  NOT in the file, added and flagged: the driver `treiber` (the file's
  header says the C driver runs `einzahlen` then `lies`; in Lean it is a
  function holding `M` by signature: `einzahlen(&Konto, 0, 7);
  lies(&Konto, 0); return`) and the idle function `ruhe` for every other
  thread (G starts every thread in some function).

  ## The finding

  Every premise of `ziel_ort_voll` holds on this translation EXCEPT the user
  obligation of `einzahlen` (`r4_einzahlen_nicht_V`): its `ensures
  old(stand) <= stand` is not provable from the body triple, because the
  call `lies(k, i)` sits between the write and the return, and the handler
  class of the obligation (`RespektiertVertraege`) constrains a callee only
  by its `ensures` -- NOT by its declared frame (`lies` writes nothing). A
  contract-respecting handler may answer `lies` with a world where the
  slot is `0` (and result `0`, meeting `lies`'s `ensures`), and the caller's
  `ensures` fails. The machine's `lies` writes nothing, and on the reached
  run the contracts hold at every logged event (`r4_vertragAmOrt_lauf`,
  checked directly) -- the goal theorem just cannot deliver it. The repair
  is the callee analogue of `RahmenO`: handlers that also respect the
  callee's declared writes.
-/
module

public import Grammatik.Korpus.Referenz.Referenz104.Teil1
public import Grammatik.Korpus.Referenz.Referenz104.Teil2
