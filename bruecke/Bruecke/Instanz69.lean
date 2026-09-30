import Bruecke.Quelle
import Duty.Duty69IntegerConversion

/-! BRIDGE-GENERIC beispiele/69-integer-conversion.gab nutzer

    P4: the bridge instance of `beispiele/69-integer-conversion.gab` THROUGH THE GENERIC THEOREM (`Quelle.lean`): the
    template `gabbro prove --template --source` writes (source pinned as pieces, stage outputs as
    hints the kernel checks, statements COMPUTED by Lean) with every owed proof filled by a proof
    against GabbroV's `Body` (the `gabbro_auto2` script of the duty files). The duty printer of
    `lean.rs` REFUSES the conversion and limit-word forms by name (`call-not-compositional`,
    `carrier-not-a-table`), so those duties are stated here from the computed statement. -/

namespace Gabbro.Bruecke.I69

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

-- SRC-BEGIN quelle
/-- THE SOURCE, byte for byte, as pieces (the guardians read this block). -/
def zeilen : List (List Char) :=
  ["-- 69 -- **`u64(a)` -- the integer conversion `SYNTAX.md` al".toList,
   "ways promised and the reader never\n".toList,
   "-- let through.** The pass test for the «K3» §4.1 repair.\n".toList,
   "--\n".toList,
   "-- `dokumente/SYNTAX.md`:588 marks `primary` \"G9: kein `cast".toList,
   "`\" and :656-659 gives the reason:\n".toList,
   "-- \"a call whose path names a type IS the conversion -- the ".toList,
   "distinction is a name resolution,\n".toList,
   "-- not a syntax question.\" Until 2026-09-04 the reader refus".toList,
   "ed the token before that rule\n".toList,
   "-- could ever apply (`P002`, reproduced against the unchange".toList,
   "d checker in\n".toList,
   "-- `messung/K3-BEFUND.md` §4.1); no corpus site had ever nee".toList,
   "ded one, which is exactly why a\n".toList,
   "-- form that was documented and unreachable could stand this".toList,
   " long.\n".toList,
   "--\n".toList,
   "-- «K3»'s `test_func` needed two, on its two most ordinary l".toList,
   "ines: `(u64) ktime_us_delta(...)`\n".toList,
   "-- and `(u64) test_repeat_count`. This file builds the same ".toList,
   "shape from a `u32` counter, since\n".toList,
   "-- that is the width the reader actually widens.\n".toList,
   "\n".toList,
   "module beispiel::umwandlung {\n".toList,
   "\n".toList,
   "-- **A widening conversion, used exactly the way «K3» needed".toList,
   " one.** `M1` gives the result the\n".toList,
   "-- FULL range of the target type rather than carrying the na".toList,
   "rrower source range through --\n".toList,
   "-- the same conservative answer this checker already gives f".toList,
   "loat arithmetic that mixes\n".toList,
   "-- widths and an `opaque` carrier's hidden representation: a".toList,
   " silent guess would be a promise.\n".toList,
   "--\n".toList,
   "-- The two conversions are combined with `|`, not `+`: the S".toList,
   "UM of two full-range `u64`\n".toList,
   "-- values leaves the width (`M104`, correctly -- the checker".toList,
   " cannot know the two halves stay\n".toList,
   "-- small), and this file is meant to check clean, not to re-".toList,
   "demonstrate M1's own overflow\n".toList,
   "-- rule on a value this pass deliberately widened to its ful".toList,
   "l range.\n".toList,
   "impl fn kombiniert(a : u32, b : u32) -> u64\n".toList,
   "    effects { pure }\n".toList,
   "    costs   <= 5 ops\n".toList,
   "{\n".toList,
   "    return u64(a) | u64(b);\n".toList,
   "}\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END quelle

def quelle : String := String.ofList zeilen.flatten

def toks : List Token := [Gabbro.Grammatik.Parser.Token.wort "module", Gabbro.Grammatik.Parser.Token.ident "beispiel", Gabbro.Grammatik.Parser.Token.zeichen "::", Gabbro.Grammatik.Parser.Token.ident "umwandlung", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.ident "kombiniert", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.ident "a", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.wort "u32", Gabbro.Grammatik.Parser.Token.zeichen ",", Gabbro.Grammatik.Parser.Token.ident "b", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.wort "u32", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.wort "u64", Gabbro.Grammatik.Parser.Token.wort "effects", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "pure", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "costs", Gabbro.Grammatik.Parser.Token.zeichen "<=", Gabbro.Grammatik.Parser.Token.zahl 5, Gabbro.Grammatik.Parser.Token.wort "ops", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.wort "u64", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.ident "a", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "|", Gabbro.Grammatik.Parser.Token.wort "u64", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.ident "b", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.ende]

def items : List SItemTief := [Gabbro.Grammatik.Parser.SItemTief.modulT "beispiel::umwandlung" [Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "kombiniert", params := [("a", Gabbro.Grammatik.Parser.STyp.atom "u32"), ("b", Gabbro.Grammatik.Parser.STyp.atom "u32")], ergebnis := some (Gabbro.Grammatik.Parser.STyp.atom "u64"), fehler := none, klauseln := [Gabbro.Grammatik.Parser.SKlausel.wirkung [Gabbro.Grammatik.Parser.SEffekt.rein], Gabbro.Grammatik.Parser.SKlausel.kosten (Gabbro.Grammatik.Parser.SExpr.lit 5)] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.bin "|" (Gabbro.Grammatik.Parser.SExpr.ruf "u64" [Gabbro.Grammatik.Parser.SExpr.variable "a"]) (Gabbro.Grammatik.Parser.SExpr.ruf "u64" [Gabbro.Grammatik.Parser.SExpr.variable "b"]))))))]]

def u : UProg := { tabellen := [], sperren := [], fns := [{ name := "kombiniert", params := [("a", Gabbro.Grammatik.Ty.int 0 4294967295), ("b", Gabbro.Grammatik.Ty.int 0 4294967295)], parten := [Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int, Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int], ergebnis := some (0, 18446744073709551615), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.bor (Gabbro.Grammatik.Parser.Uebersetze.USide.conv 0 18446744073709551615 (Gabbro.Grammatik.Parser.Uebersetze.USide.param "a")) (Gabbro.Grammatik.Parser.Uebersetze.USide.conv 0 18446744073709551615 (Gabbro.Grammatik.Parser.Uebersetze.USide.param "b"))) }] }

set_option maxHeartbeats 4000000 in
theorem lex_ok : lexL zeilen.flatten = .ok toks := by decide +kernel

theorem parse_ok : parseTopTief toks = .ok items := rfl

theorem elab_ok : elabU (pre108 items) = .ok u := rfl

theorem low_ok : (lowerAllg u).toOption.isSome = true := by decide +kernel

/-- PARSE FIDELITY: the pinned text is the program `u`. -/
theorem uebersetzt : uebersetzeAllg quelle =
    .ok ⟨u, ((lowerAllg u).toOption.get low_ok).1, ((lowerAllg u).toOption.get low_ok).2⟩ :=
  uebersetzeAllg_von_zeichen lex_ok parse_ok elab_ok (except_ok_get low_ok)

theorem verankert : uOf quelle = some u := uOf_eq uebersetzt

theorem null : nullB u = true := by decide
theorem stimmig : stimmigB u = true := by decide
theorem rang : rangB u (rangAuto u) = true := by decide

open GabbroDuty.Duty69IntegerConversion

theorem shape_eq : shapeOf = shapeOfU u := by
  funext p
  rcases p with ⟨c, i, f⟩ | ⟨c, n⟩ | n <;> simp [shapeOf, shapeOfU, slotShape, u]

theorem wfU_eq : wfU u = wellFormed := by
  funext s; unfold wfU wellFormed; rw [shape_eq]

def kombiniert_body : List Gabbro.Body.Stmt :=
  [(.ret (some (.bin .bor (.name "a") (.name "b"))))]

def kombiniert_meets_statement : Prop :=
  ∀ (ρ : Gabbro.Body.Env) (s : Gabbro.Body.State) (hwf : wellFormed s)
    (hpre : Gabbro.Body.eval s kombiniert_pre = some (.bool true)),
    ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ kombiniert_body s) = some s'
        ∧ kombiniert_post s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρ kombiniert_body s))

open Gabbro.Body in
theorem kombiniert_meets : kombiniert_meets_statement := by
  unfold kombiniert_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ (and_left _ _ _ hpre)
  obtain ⟨w_b, e_b, lo_b, hi_b⟩ := shape_intIn s "b" _ _ (and_right _ _ _ hpre)
  have hall := hpre
  gabbro_simp_at hall [kombiniert_pre, e_a, e_b]
  gabbro_auto2 [kombiniert_body, kombiniert_pre, kombiniert_post, wellFormed, e_a, e_b, hall] [kombiniert_body, kombiniert_pre, kombiniert_post, wellFormed, e_a, e_b] using shapeOf

def kombiniert : UFn := u.fns[0]'(by decide)

example : zuBody u kombiniert = some kombiniert_body := rfl
example : preExpr kombiniert = kombiniert_pre := rfl
example : kombiniert.schreibt = kombiniert_writes := rfl
example : (fun s s' r => (postU u wellFormed kombiniert s s' r).getD False) = kombiniert_post := rfl
example : meetsU u wellFormed kombiniert ((zuBody u kombiniert).getD []) = kombiniert_meets_statement := rfl

/-- The duty of `kombiniert`: the computed statement, closed by a proof against GabbroV's `Body`. -/
theorem pflicht_0 : ∃ body, zuBody u (fnAt u ⟨0, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨0, by decide⟩) body :=
  ⟨kombiniert_body, rfl, by rw [wfU_eq]; exact kombiniert_meets⟩

theorem pflichten : Pflichten quelle :=
  ⟨u, verankert, null, stimmig, rang, fun c => match c with
  | ⟨0, _⟩ => pflicht_0
  | ⟨_ + 1, h⟩ => absurd h
      (by have hl : u.fns.length = 1 := by decide
          omega)⟩

/-- PREMISE (b) OF THE GOAL THEOREM for the unit the front end builds from `quelle`. -/
theorem nutzer {u' : UProg} {P : Gabbro.Grammatik.Programm (declOf u')}
    {fs : List (declOf u').Fn} (h : Gabbro.Grammatik.uebersetzeAllg quelle = .ok ⟨u', P, fs⟩) :
    ∃ hn : nullB u' = true, Gabbro.Grammatik.Zielsatz.NutzerPflicht (einheitAllg u' P hn) :=
  nutzer_aus_quelle pflichten h

/-! CHAIN-GENERIC beispiele/69-integer-conversion.gab kette_69

    P4: the closed translation-validation chain of `beispiele/69-integer-conversion`, assembled by the GENERIC `ketteAllg`
    (`Quelle.lean`): no tables, so the emitter's layout is empty; premise (b) is `nutzer_aus_quelle`.
    The instance adds WITNESS data only: the checker's Bool (a computation) and the certificate literal
    `gabbro corr-lean` prints, checked by `korrOk` (its `weiter` arm accepts the explicit conversion
    `(T)(e)` since 2026-09-30). -/

def P69 : Gabbro.Grammatik.Programm (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u) :=
  ((lowerAllg u).toOption.get low_ok).1

theorem ht : u.tabellen = [] := rfl

/-- Pasted from `gabbro corr-lean beispiele/69-integer-conversion.gab`, generic section. -/
def zert69 : KCert (declOf u) :=
  [{ params := [(0, .int false .w32), (1, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w64), (.bin .bor CIT.u64 (.cast CIT.u64 (.var 0)) (.cast CIT.u64 (.var 1)))))], vm := [0, 1], pp := [], ks := [] }]

theorem akz69 : akzeptiert_pruefer.akzeptiert (einheitAllg u P69 (pflichten_null pflichten uebersetzt))
    (aufzFn u).1 (aufzLock u).1 (aufzTraegerLeer u ht).1 = true := by decide

theorem zert69_ok : korrOk (emitLayLeer u ht) fnNr zert69 P69 (aufzFn u).1 = true := by decide

/-- **THE CLOSED CHAIN OF `beispiele/69-integer-conversion`**: source text, checker Bool, GabbroV's duties, the
    correspondence to the C -- every field a theorem. -/
def kette_69 : Kette quelle := ketteAllg pflichten uebersetzt ht zert69 akz69 zert69_ok

#print axioms pflichten
#print axioms nutzer
#print axioms kette_69

end Gabbro.Bruecke.I69
