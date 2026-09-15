/-
  File:      Grammatik/SchlusssatzZeuge.lean
  Subject:   Witnesses (rule 13) of the generic stage-(a) theorems:
             `korrOk_fnCorr`/`korrOk_jeder_lauf` (KorrespondenzAllg.lean),
             `einfaden_ziel` and `schlusssatz` (Schlusssatz.lean) -- each with
             its premises jointly satisfied on a program whose run MOVES
             memory (104: `einzahlen` writes `100`), and the check seen
             FAILING on wrong certificates (a sieve nobody has seen fail is a
             decoration).
-/
import Grammatik.Kette104Satz
import Grammatik.Kette108

namespace Gabbro.Grammatik

open Kette104 Zielsatz

/-! ## 1. The correspondence check -/

/-- **WITNESS of `korrOk_jeder_lauf`**: the check holds on 104's parsed
    program and printed certificate, and the conclusion is a C run of
    `einzahlen` that moves the C cell `0 -> 100` (through the closing theorem,
    `kette_104_zeuge`). -/
theorem korrOk_zeuge :
    korrOk EL4 fnNr zert104 P4 fsA.1 = true ∧
    ∃ σ' : World D4, rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok σ' () ∧
      (σ'.slots t4 0 f4).n = 100 ∧
      ∀ st' rv, CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 0 refSt0 einArgs st' rv →
        st'.mem (.tab 0) 0 = .int 100 := by
  obtain ⟨σ', hR, _, h100, _, _, hall⟩ := kette_104_zeuge
  exact ⟨zert104_ok, σ', hR, h100, fun st' rv hC => (hall st' rv hC).1⟩

/-- The printed rows with a WRONG layout number (field offset `1`): refused. -/
def zert104_versatz : KCert D4 :=
  [{ params := [(0, .ptr), (1, .int false .w32), (2, .int false .w32)], locals := [], rows := [GRow.void 2, GRow.storeSlot 0 (.var 1) 2 4 1 (.int false .w32) (.lit 100), GRow.call 1 [.var 0, .var 1] none], vm := [0, 1, 2], pp := [], ks := [] },
   { params := [(0, .ptr), (1, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.var 0) (.var 1) 2 4 0) (.int false .w32))))], vm := [0, 1], pp := [], ks := [] }]

/-- The printed rows with a WRONG stored value (`99` for `100`): refused. -/
def zert104_wert : KCert D4 :=
  [{ params := [(0, .ptr), (1, .int false .w32), (2, .int false .w32)], locals := [], rows := [GRow.void 2, GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 99), GRow.call 1 [.var 0, .var 1] none], vm := [0, 1, 2], pp := [], ks := [] },
   { params := [(0, .ptr), (1, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.var 0) (.var 1) 2 4 0) (.int false .w32))))], vm := [0, 1], pp := [], ks := [] }]

/-- `refD`'s index-fixed map (lane 164's printer, `ks = [(1, 0)]`): refused
    at the call site -- the model of the source has `i` as a variable. -/
def zert104_refD : KCert D4 :=
  [{ params := [(0, .ptr), (1, .int false .w32), (2, .int false .w32)], locals := [], rows := [GRow.void 2, GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 100), GRow.call 1 [.var 0, .var 1] none], vm := [2], pp := [(0, t4)], ks := [(1, 0)] },
   { params := [(0, .ptr), (1, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.var 0) (.var 1) 2 4 0) (.int false .w32))))], vm := [], pp := [(0, t4)], ks := [(1, 0)] }]

/-- A certificate that forgets the call row: refused. -/
def zert104_ohneRuf : KCert D4 :=
  [{ params := [(0, .ptr), (1, .int false .w32), (2, .int false .w32)], locals := [], rows := [GRow.void 2, GRow.storeSlot 0 (.var 1) 2 4 0 (.int false .w32) (.lit 100)], vm := [0, 1, 2], pp := [], ks := [] },
   { params := [(0, .ptr), (1, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w32), (.ld (.slotA (.var 0) (.var 1) 2 4 0) (.int false .w32))))], vm := [0, 1], pp := [], ks := [] }]

/-- **THE CHECK FALLS** on each planted defect: layout, value, map, a missing
    row -- and on 108's certificate against 104's program. -/
theorem korrOk_faellt :
    korrOk EL4 fnNr zert104_versatz P4 fsA.1 = false ∧
    korrOk EL4 fnNr zert104_wert P4 fsA.1 = false ∧
    korrOk EL4 fnNr zert104_refD P4 fsA.1 = false ∧
    korrOk EL4 fnNr zert104_ohneRuf P4 fsA.1 = false := by
  decide

/-! ## 2. The machine with one active thread -/

/-- **WITNESS of `einfaden_ziel`**: its premises hold jointly on 104 with
    thread `0` running `einzahlen(k, 0, 7)` -- a function that holds the lock
    `M` by signature and writes the table, which the goal theorem's runtime
    premise (d) would refuse as a start (`wurzelnB`) --, and the conclusion
    speaks about that thread: at the start machine it stands in
    `einzahlen`'s body, holding `M`. -/
theorem einfaden_ziel_zeuge :
    AkzeptiertSpec E4.P E4.S fsA.1 E4.ws ∧ NutzerPflicht E4 ∧ HardwareAnnahmen O4 E4.Q ∧
    EinFadenStart E4 (speicherR E4.sp0) init4 ∧
    ((RufStartG E4.P.mitRuhe (speicherR E4.sp0) init4).faeden 0).kopf.f = some ein4 ∧
    ∀ (passes : Nat) (M : RufMaschineG D4.mitRuhe),
      RufErreichbarG E4.P.mitRuhe O4.mitRuhe passes (RufStartG E4.P.mitRuhe (speicherR E4.sp0) init4) M →
        SpurInv M ∧ VertragAmOrtG E4.P.mitRuhe M ∧ StartEndeG E4.P.mitRuhe M := by
  have hA := akzeptiert_pruefer.korrekt E4 fsA lsA csA akzeptiert4
  refine ⟨hA, nutzer4, hw4, start4, rfl, fun passes M hr => ?_⟩
  have h := einfaden_ziel E4 fsA hA nutzer4 O4 hw4 _ init4 start4 passes M hr
  exact ⟨h.1, h.2.1.1.1, h.2.2.1⟩

/-! ## 3. The closing theorem -/

/-- **WITNESS of `schlusssatz`** (every premise jointly, a run that moves
    memory): `kette_104_zeuge` (Kette104Satz.lean) -- restated here under
    the theorem's name. -/
theorem schlusssatz_zeuge :
    ∃ σ' : World D4, rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok σ' () ∧
      ((sp4.welt []).slots t4 0 f4).n = 0 ∧ (σ'.slots t4 0 f4).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧
      (∃ st' rv, CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 0 refSt0 einArgs st' rv) ∧
      ∀ st' rv, CallAt EL4.lay tvOrc tvXR (kProg zert104) 2 0 refSt0 einArgs st' rv →
        st'.mem (.tab 0) 0 = .int 100 ∧ rv = none :=
  kette_104_zeuge

#print axioms Gabbro.Grammatik.korrOk_zeuge
#print axioms Gabbro.Grammatik.korrOk_faellt
#print axioms Gabbro.Grammatik.einfaden_ziel_zeuge
#print axioms Gabbro.Grammatik.schlusssatz_zeuge

end Gabbro.Grammatik
