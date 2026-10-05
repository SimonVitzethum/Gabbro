import Bruecke.Quelle
import Duty.Duty130DerivedContractPure

/-! BRIDGE-GENERIC beispiele/130-derived-contract-pure.gab nutzer

    P4: the bridge instance of `beispiele/130` THROUGH THE GENERIC THEOREM (`Quelle.lean`). The file
    is the template `gabbro prove --template --source` writes (the source pinned as pieces, the
    stage outputs as hints the kernel checks, the statements COMPUTED by Lean), with the one owed
    proof filled by GabbroV's own duty proof `add_meets` (`Duty130DerivedContractPure.lean`, closed
    by `gabbro_auto2`). The `example`s tie the computed statement to the printed duty by `rfl`. -/

namespace Gabbro.Bruecke.I130

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

-- SRC-BEGIN quelle
/-- THE SOURCE, byte for byte, as pieces (the guardians read this block). -/
def zeilen : List (List Char) :=
  ["-- 130 -- **Lane 191: the omitted clause is derived, not dem".toList,
   "anded.**\n".toList,
   "--\n".toList,
   "-- `add` declares neither `effects` nor `costs`. The checker".toList,
   " derives both\n".toList,
   "-- from the body — `effects { pure }` and the price of one a".toList,
   "ddition — and\n".toList,
   "-- treats them exactly like written lines (`gabbro abgeleite".toList,
   "t` prints them,\n".toList,
   "-- `gabbro kosten` counts them). A written bound stays the e".toList,
   "nforced bound:\n".toList,
   "-- promising less than the body costs still falls with `K001".toList,
   "`.\n".toList,
   "module beispiel130 {\n".toList,
   "\n".toList,
   "impl fn add(a : u32 in 0 .. 1000, b : u32 in 0 .. 1000) -> u".toList,
   "32 in 0 .. 2000 {\n".toList,
   "    return a + b;\n".toList,
   "}\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END quelle

def quelle : String := String.ofList zeilen.flatten

def toks : List Token := [Gabbro.Grammatik.Parser.Token.wort "module", Gabbro.Grammatik.Parser.Token.ident "beispiel130", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.wort "add", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.ident "a", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.wort "u32", Gabbro.Grammatik.Parser.Token.wort "in", Gabbro.Grammatik.Parser.Token.zahl 0, Gabbro.Grammatik.Parser.Token.zeichen "..", Gabbro.Grammatik.Parser.Token.zahl 1000, Gabbro.Grammatik.Parser.Token.zeichen ",", Gabbro.Grammatik.Parser.Token.ident "b", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.wort "u32", Gabbro.Grammatik.Parser.Token.wort "in", Gabbro.Grammatik.Parser.Token.zahl 0, Gabbro.Grammatik.Parser.Token.zeichen "..", Gabbro.Grammatik.Parser.Token.zahl 1000, Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.wort "u32", Gabbro.Grammatik.Parser.Token.wort "in", Gabbro.Grammatik.Parser.Token.zahl 0, Gabbro.Grammatik.Parser.Token.zeichen "..", Gabbro.Grammatik.Parser.Token.zahl 2000, Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.ident "a", Gabbro.Grammatik.Parser.Token.zeichen "+", Gabbro.Grammatik.Parser.Token.ident "b", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.ende]

def items : List SItemTief := [Gabbro.Grammatik.Parser.SItemTief.modulT "beispiel130" [Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "add", params := [("a", Gabbro.Grammatik.Parser.STyp.bereich (Gabbro.Grammatik.Parser.STyp.atom "u32") (Gabbro.Grammatik.Parser.SExpr.lit 0) (Gabbro.Grammatik.Parser.SExpr.lit 1000) false), ("b", Gabbro.Grammatik.Parser.STyp.bereich (Gabbro.Grammatik.Parser.STyp.atom "u32") (Gabbro.Grammatik.Parser.SExpr.lit 0) (Gabbro.Grammatik.Parser.SExpr.lit 1000) false)], ergebnis := some (Gabbro.Grammatik.Parser.STyp.bereich (Gabbro.Grammatik.Parser.STyp.atom "u32") (Gabbro.Grammatik.Parser.SExpr.lit 0) (Gabbro.Grammatik.Parser.SExpr.lit 2000) false), fehler := none, klauseln := [] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.bin "+" (Gabbro.Grammatik.Parser.SExpr.variable "a") (Gabbro.Grammatik.Parser.SExpr.variable "b"))))))]]

def u : UProg := { tabellen := [], sperren := [], fns := [{ name := "add", params := [("a", Gabbro.Grammatik.Ty.int 0 1000), ("b", Gabbro.Grammatik.Ty.int 0 1000)], parten := [Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int, Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int], ergebnis := some (0, 2000), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.add (Gabbro.Grammatik.Parser.Uebersetze.USide.param "a") (Gabbro.Grammatik.Parser.Uebersetze.USide.param "b")) }] }

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

open GabbroDuty.Duty130DerivedContractPure

theorem shape_eq : shapeOf = shapeOfU u := by
  funext p
  rcases p with ⟨c, i, f⟩ | ⟨c, n⟩ | n <;> simp [shapeOf, shapeOfU, slotShape, u]

theorem wfU_eq : wfU u = wellFormed := by
  funext s; unfold wfU wellFormed; rw [shape_eq]

def add : UFn := u.fns[0]'(by decide)

example : zuBody u add = some add_body := rfl
example : preExpr add = add_pre := rfl
example : add.schreibt = add_writes := rfl
example : (fun s s' r => (postU u wellFormed add s s' r).getD False) = add_post := rfl
example : preProp wellFormed add = add_requires := rfl
example : meetsU u wellFormed add ((zuBody u add).getD []) = add_meets_statement := rfl

/-- The duty of `add`: the computed statement, closed by GabbroV's proof. -/
theorem pflicht_0 : ∃ body, zuBody u (fnAt u ⟨0, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨0, by decide⟩) body :=
  ⟨add_body, rfl, by rw [wfU_eq]; exact add_meets⟩

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

/-! CHAIN-GENERIC beispiele/130-derived-contract-pure.gab kette_130

    P4: the closed translation-validation chain of `beispiele/130`, assembled by the GENERIC
    `ketteAllg` (`Quelle.lean`): no tables, so the emitter's layout is empty; premise (b) is
    `nutzer_aus_quelle`. What the instance adds is WITNESS data only: the checker's Bool (a
    computation) and the certificate literal `gabbro corr-lean` printed (checked by `korrOk`). -/

def P130 : Gabbro.Grammatik.Programm (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u) :=
  ((lowerAllg u).toOption.get low_ok).1

theorem ht : u.tabellen = [] := rfl

/-- Pasted from `gabbro corr-lean beispiele/130-derived-contract-pure.gab`, generic section. -/
def zert130 : KCert (declOf u) :=
  [{ params := [(0, .int false .w32), (1, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w32), (.bin .add CIT.u32 (.var 0) (.var 1))))], vm := [0, 1], pp := [], ks := [] }]

theorem akz130 : akzeptiert_pruefer.akzeptiert (einheitAllg u P130 (pflichten_null pflichten uebersetzt))
    (aufzFn u).1 (aufzLock u).1 (aufzTraegerLeer u ht).1 = true := by decide

theorem zert130_ok : korrOk (emitLayLeer u ht) fnNr zert130 P130 (aufzFn u).1 = true := by decide

/-- **THE CLOSED CHAIN OF `beispiele/130`**: source text, checker Bool, GabbroV's duties, the
    correspondence to the C -- every field a theorem. -/
def kette_130 : Kette quelle := ketteAllg pflichten uebersetzt ht zert130 akz130 zert130_ok

#print axioms pflichten
#print axioms nutzer
#print axioms kette_130

end Gabbro.Bruecke.I130
