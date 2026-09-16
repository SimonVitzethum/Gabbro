/-
  File:      Grammatik/CText104Zeuge.lean
  Subject:   The NEGATIVE WITNESSES of the A2 pin of `beispiele/104`
             (CText104.lean): a text that is not the emitted one is a
             different program, or none at all.

  A pin a parser can satisfy by accepting anything is no pin. Every text
  below is `zeilen104` with ONE line replaced -- one token changed --,
  and `parseC` answers

  * with a DIFFERENT program, which the correspondence check `korrOk`
    then REFUSES against the parsed Gabbro program (the value stored, the
    table's slot count: the layout numbers `2 4 0` are READ FROM THE
    TEXT, not transcribed), or
  * with `none` (a missing prelude pin, a field the slot record does not
    declare).

  The refusals of forms OUTSIDE the subset (`if`, arithmetic, `let`,
  volatile) are probed in `CParser/CProben.lean`, on short texts.
-/
import Grammatik.CText104

namespace Gabbro.Grammatik.CText104

open Gabbro.Grammatik Gabbro.Grammatik.CParser Gabbro.Grammatik.Kette104

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## 1. The mutated texts: `zeilen104` with one line replaced -/

/-- Line 38, the store, with `100` changed to `99`. -/
def ctext104_wert : List Char :=
  zusammen (zeilen104.set 39 "    k->slots[i].stand = 99;\n".toList)

/-- Line 18, `#define NKONTO 2u` changed to `3u` -- one token, and the
    table's geometry is a different one. -/
def ctext104_anzahl : List Char :=
  zusammen (zeilen104.set 19 "#define NKONTO 3u\n".toList)

/-- Line 16, the second `_Static_assert` pin, deleted. -/
def ctext104_ohnePin : List Char := zusammen (zeilen104.set 17 [])

/-- Line 44, the read in `lies`, at a field the slot record does not
    declare. -/
def ctext104_feld : List Char :=
  zusammen (zeilen104.set 44 "    return k->slots[i].fehlt;\n".toList)

/-! ## 2. What `parseC` answers -/

/-- The certificate of `ctext104_wert`: `99` for `100`
    (`SchlusssatzZeuge.lean` plants the same defect by hand). -/
def zert104_wert : KCert D4 :=
  [{ params := [(0, .ptr), (1, .int false .w32), (2, .int false .w32)], locals := [],
     rows := [GRow.void 2, GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 99),
       GRow.call 1 [.var 0, .var 1] none], vm := [0, 1, 2], pp := [], ks := [] },
   { params := [(0, .ptr), (1, .int false .w32)], locals := [],
     rows := [GRow.ret (some ((.int false .w32),
       (.ld (.slotA (.var 0) (.var 1) 2 4 0) (.int false .w32))))],
     vm := [0, 1], pp := [], ks := [] }]

/-- The certificate of `ctext104_anzahl`: a table of THREE slots. -/
def zert104_anzahl : KCert D4 :=
  [{ params := [(0, .ptr), (1, .int false .w32), (2, .int false .w32)], locals := [],
     rows := [GRow.void 2, GRow.storeSlot 0 (.var 1) 3 4 0 (.int false .w32) (.lit 100),
       GRow.call 1 [.var 0, .var 1] none], vm := [0, 1, 2], pp := [], ks := [] },
   { params := [(0, .ptr), (1, .int false .w32)], locals := [],
     rows := [GRow.ret (some ((.int false .w32),
       (.ld (.slotA (.var 0) (.var 1) 3 4 0) (.int false .w32))))],
     vm := [0, 1], pp := [], ks := [] }]

/-- **THE PIN IS NOT SATISFIED BY A PARSER THAT ACCEPTS ANYTHING.** -/
theorem a2_104_gegenprobe_programm :
    parseC ctext104_wert = some (kFuns zert104_wert) ∧
    parseC ctext104_anzahl = some (kFuns zert104_anzahl) :=
  ⟨rfl, rfl⟩

/-- ... and the different programs are REFUSED by the correspondence
    check against the Gabbro program the source parses to. -/
theorem a2_104_gegenprobe_korr :
    korrOk EL4 fnNr zert104_wert P4 fsA.1 = false ∧
    korrOk EL4 fnNr zert104_anzahl P4 fsA.1 = false := by
  constructor <;> decide

/-- A missing prelude pin and an undeclared field are `none`. -/
theorem a2_104_gegenprobe_keine :
    parseC ctext104_ohnePin = none ∧ parseC ctext104_feld = none :=
  ⟨rfl, rfl⟩

#print axioms Gabbro.Grammatik.CText104.a2_104_gegenprobe_programm
#print axioms Gabbro.Grammatik.CText104.a2_104_gegenprobe_korr
#print axioms Gabbro.Grammatik.CText104.a2_104_gegenprobe_keine

end Gabbro.Grammatik.CText104
