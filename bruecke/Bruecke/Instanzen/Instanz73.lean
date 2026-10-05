import Bruecke.Quelle
import Duty.Duty73SugarWidths

/-! BRIDGE-GENERIC beispiele/73-sugar-widths.gab nutzer

    P4: the bridge instance of `beispiele/73-sugar-widths.gab` THROUGH THE GENERIC THEOREM (`Quelle.lean`): the
    template `gabbro prove --template --source` writes (source pinned as pieces, stage outputs as
    hints the kernel checks, statements COMPUTED by Lean) with every owed proof filled: by GabbroV's
    own duty proof where `lean.rs` printed one, and by a proof against `Body` (the `gabbro_auto2`
    script of the duty files) where it REFUSED the form by name (`call-not-compositional` for the
    conversion `u13(a)`, `carrier-not-a-table` for the limit word `u13::max`). -/

namespace Gabbro.Bruecke.I73

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

-- SRC-BEGIN quelle
/-- THE SOURCE, byte for byte, as pieces (the guardians read this block). -/
def zeilen : List (List Char) :=
  ["-- 72 -- **`uN`/`iN` sugar (PLAN-BITS §1): storage, range an".toList,
   "d limit in one unit.**\n".toList,
   "--\n".toList,
   "-- `u13` is `u16 in 0 .. 8191`; `i37` is `i64 in -2^36 .. 2^".toList,
   "36 - 1`. The storage\n".toList,
   "-- is the next standard width, and the emitted C uses it -- ".toList,
   "never `_BitInt`.\n".toList,
   "-- The range is the exact one: 8191 stays, 8192 would fall (".toList,
   "`gift/798`), and\n".toList,
   "-- `u13::max` lowers the exact bound. `u1` is the narrowest ".toList,
   "sugar; `u64` beside\n".toList,
   "-- it shows the standard words keep their full-width meaning".toList,
   " exactly.\n".toList,
   "module beispiel::zuckerbreiten {\n".toList,
   "\n".toList,
   "-- The narrowest sugar and the flag position beside it: both".toList,
   " stay silent.\n".toList,
   "impl fn eins(x : u1) -> u8 effects { pure } costs <= 2 ops {".toList,
   "\n".toList,
   "    return x;\n".toList,
   "}\n".toList,
   "\n".toList,
   "-- Thirteen bits in a sixteen-bit word: the range, the conve".toList,
   "rsion, the limit.\n".toList,
   "impl fn dreizehn(x : u13) -> u16 effects { pure } costs <= 2".toList,
   " ops {\n".toList,
   "    return x;\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn wandle(a : u32 in 0 .. 100) -> u13 effects { pure } ".toList,
   "costs <= 4 ops {\n".toList,
   "    return u13(a);\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn grenze() -> u64 effects { pure } costs <= 2 ops {\n".toList,
   "    return u13::max;\n".toList,
   "}\n".toList,
   "\n".toList,
   "-- Thirty-seven bits in a sixty-four-bit word, signed: stays".toList,
   " silent at its word.\n".toList,
   "impl fn minus(x : i37) -> i64 effects { pure } costs <= 2 op".toList,
   "s {\n".toList,
   "    return x;\n".toList,
   "}\n".toList,
   "\n".toList,
   "-- The standard word beside the sugar: full width, unchanged".toList,
   " meaning.\n".toList,
   "impl fn voll(x : u64) -> u64 effects { pure } costs <= 2 ops".toList,
   " {\n".toList,
   "    return x;\n".toList,
   "}\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END quelle

def quelle : String := String.ofList zeilen.flatten

def toks : List Token := [Gabbro.Grammatik.Parser.Token.wort "module", Gabbro.Grammatik.Parser.Token.ident "beispiel", Gabbro.Grammatik.Parser.Token.zeichen "::", Gabbro.Grammatik.Parser.Token.ident "zuckerbreiten", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.ident "eins", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.ident "u1", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.wort "u8", Gabbro.Grammatik.Parser.Token.wort "effects", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "pure", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "costs", Gabbro.Grammatik.Parser.Token.zeichen "<=", Gabbro.Grammatik.Parser.Token.zahl 2, Gabbro.Grammatik.Parser.Token.wort "ops", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.ident "dreizehn", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.ident "u13", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.wort "u16", Gabbro.Grammatik.Parser.Token.wort "effects", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "pure", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "costs", Gabbro.Grammatik.Parser.Token.zeichen "<=", Gabbro.Grammatik.Parser.Token.zahl 2, Gabbro.Grammatik.Parser.Token.wort "ops", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.ident "wandle", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.ident "a", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.wort "u32", Gabbro.Grammatik.Parser.Token.wort "in", Gabbro.Grammatik.Parser.Token.zahl 0, Gabbro.Grammatik.Parser.Token.zeichen "..", Gabbro.Grammatik.Parser.Token.zahl 100, Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.ident "u13", Gabbro.Grammatik.Parser.Token.wort "effects", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "pure", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "costs", Gabbro.Grammatik.Parser.Token.zeichen "<=", Gabbro.Grammatik.Parser.Token.zahl 4, Gabbro.Grammatik.Parser.Token.wort "ops", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.ident "u13", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.ident "a", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.ident "grenze", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.wort "u64", Gabbro.Grammatik.Parser.Token.wort "effects", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "pure", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "costs", Gabbro.Grammatik.Parser.Token.zeichen "<=", Gabbro.Grammatik.Parser.Token.zahl 2, Gabbro.Grammatik.Parser.Token.wort "ops", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.ident "u13", Gabbro.Grammatik.Parser.Token.zeichen "::", Gabbro.Grammatik.Parser.Token.wort "max", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.ident "minus", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.ident "i37", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.wort "i64", Gabbro.Grammatik.Parser.Token.wort "effects", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "pure", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "costs", Gabbro.Grammatik.Parser.Token.zeichen "<=", Gabbro.Grammatik.Parser.Token.zahl 2, Gabbro.Grammatik.Parser.Token.wort "ops", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "impl", Gabbro.Grammatik.Parser.Token.wort "fn", Gabbro.Grammatik.Parser.Token.ident "voll", Gabbro.Grammatik.Parser.Token.zeichen "(", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ":", Gabbro.Grammatik.Parser.Token.wort "u64", Gabbro.Grammatik.Parser.Token.zeichen ")", Gabbro.Grammatik.Parser.Token.zeichen "->", Gabbro.Grammatik.Parser.Token.wort "u64", Gabbro.Grammatik.Parser.Token.wort "effects", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "pure", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.wort "costs", Gabbro.Grammatik.Parser.Token.zeichen "<=", Gabbro.Grammatik.Parser.Token.zahl 2, Gabbro.Grammatik.Parser.Token.wort "ops", Gabbro.Grammatik.Parser.Token.zeichen "{", Gabbro.Grammatik.Parser.Token.wort "return", Gabbro.Grammatik.Parser.Token.wort "x", Gabbro.Grammatik.Parser.Token.zeichen ";", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.zeichen "}", Gabbro.Grammatik.Parser.Token.ende]

def items : List SItemTief := [Gabbro.Grammatik.Parser.SItemTief.modulT "beispiel::zuckerbreiten" [Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "eins", params := [("x", Gabbro.Grammatik.Parser.STyp.atom "u1")], ergebnis := some (Gabbro.Grammatik.Parser.STyp.atom "u8"), fehler := none, klauseln := [Gabbro.Grammatik.Parser.SKlausel.wirkung [Gabbro.Grammatik.Parser.SEffekt.rein], Gabbro.Grammatik.Parser.SKlausel.kosten (Gabbro.Grammatik.Parser.SExpr.lit 2)] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.variable "x"))))), Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "dreizehn", params := [("x", Gabbro.Grammatik.Parser.STyp.atom "u13")], ergebnis := some (Gabbro.Grammatik.Parser.STyp.atom "u16"), fehler := none, klauseln := [Gabbro.Grammatik.Parser.SKlausel.wirkung [Gabbro.Grammatik.Parser.SEffekt.rein], Gabbro.Grammatik.Parser.SKlausel.kosten (Gabbro.Grammatik.Parser.SExpr.lit 2)] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.variable "x"))))), Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "wandle", params := [("a", Gabbro.Grammatik.Parser.STyp.bereich (Gabbro.Grammatik.Parser.STyp.atom "u32") (Gabbro.Grammatik.Parser.SExpr.lit 0) (Gabbro.Grammatik.Parser.SExpr.lit 100) false)], ergebnis := some (Gabbro.Grammatik.Parser.STyp.atom "u13"), fehler := none, klauseln := [Gabbro.Grammatik.Parser.SKlausel.wirkung [Gabbro.Grammatik.Parser.SEffekt.rein], Gabbro.Grammatik.Parser.SKlausel.kosten (Gabbro.Grammatik.Parser.SExpr.lit 4)] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.ruf "u13" [Gabbro.Grammatik.Parser.SExpr.variable "a"]))))), Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "grenze", params := [], ergebnis := some (Gabbro.Grammatik.Parser.STyp.atom "u64"), fehler := none, klauseln := [Gabbro.Grammatik.Parser.SKlausel.wirkung [Gabbro.Grammatik.Parser.SEffekt.rein], Gabbro.Grammatik.Parser.SKlausel.kosten (Gabbro.Grammatik.Parser.SExpr.lit 2)] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.feld (Gabbro.Grammatik.Parser.SExpr.variable "u13") "max"))))), Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "minus", params := [("x", Gabbro.Grammatik.Parser.STyp.atom "i37")], ergebnis := some (Gabbro.Grammatik.Parser.STyp.atom "i64"), fehler := none, klauseln := [Gabbro.Grammatik.Parser.SKlausel.wirkung [Gabbro.Grammatik.Parser.SEffekt.rein], Gabbro.Grammatik.Parser.SKlausel.kosten (Gabbro.Grammatik.Parser.SExpr.lit 2)] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.variable "x"))))), Gabbro.Grammatik.Parser.SItemTief.funktionT { art := "impl", name := "voll", params := [("x", Gabbro.Grammatik.Parser.STyp.atom "u64")], ergebnis := some (Gabbro.Grammatik.Parser.STyp.atom "u64"), fehler := none, klauseln := [Gabbro.Grammatik.Parser.SKlausel.wirkung [Gabbro.Grammatik.Parser.SEffekt.rein], Gabbro.Grammatik.Parser.SKlausel.kosten (Gabbro.Grammatik.Parser.SExpr.lit 2)] } (Gabbro.Grammatik.Parser.SAnw.block [] (some (Gabbro.Grammatik.Parser.SEnde.ret (some (Gabbro.Grammatik.Parser.SExpr.variable "x")))))]]

def u : UProg := { tabellen := [], sperren := [], fns := [{ name := "eins", params := [("x", Gabbro.Grammatik.Ty.int 0 1)], parten := [Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int], ergebnis := some (0, 255), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.param "x") }, { name := "dreizehn", params := [("x", Gabbro.Grammatik.Ty.int 0 8191)], parten := [Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int], ergebnis := some (0, 65535), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.param "x") }, { name := "wandle", params := [("a", Gabbro.Grammatik.Ty.int 0 100)], parten := [Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int], ergebnis := some (0, 8191), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.conv 0 8191 (Gabbro.Grammatik.Parser.Uebersetze.USide.param "a")) }, { name := "grenze", params := [], parten := [], ergebnis := some (0, 18446744073709551615), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.lit 8191) }, { name := "minus", params := [("x", Gabbro.Grammatik.Ty.int (-68719476736) 68719476735)], parten := [Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int], ergebnis := some (-9223372036854775808, 9223372036854775807), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.param "x") }, { name := "voll", params := [("x", Gabbro.Grammatik.Ty.int 0 18446744073709551615)], parten := [Gabbro.Grammatik.Parser.Uebersetze.UParamArt.int], ergebnis := some (0, 18446744073709551615), held := [], schreibt := [], sichert := [], saetze := [], rueck := Gabbro.Grammatik.Parser.Uebersetze.URet.wert (Gabbro.Grammatik.Parser.Uebersetze.USide.param "x") }] }

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

open GabbroDuty.Duty73SugarWidths

theorem shape_eq : shapeOf = shapeOfU u := by
  funext p
  rcases p with ⟨c, i, f⟩ | ⟨c, n⟩ | n <;> simp [shapeOf, shapeOfU, slotShape, u]

theorem wfU_eq : wfU u = wellFormed := by
  funext s; unfold wfU wellFormed; rw [shape_eq]

/-! The two duties the printer of `lean.rs` REFUSES by name: stated from the computed statement,
    proved against `Body` by the script of the duty files. -/

def wandle_body : List Gabbro.Body.Stmt :=
  [(.ret (some (.name "a")))]

def wandle_meets_statement : Prop :=
  ∀ (ρ : Gabbro.Body.Env) (s : Gabbro.Body.State) (hwf : wellFormed s)
    (hpre : Gabbro.Body.eval s wandle_pre = some (.bool true)),
    ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ wandle_body s) = some s'
        ∧ wandle_post s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρ wandle_body s))

open Gabbro.Body in
theorem wandle_meets : wandle_meets_statement := by
  unfold wandle_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  obtain ⟨w_a, e_a, lo_a, hi_a⟩ := shape_intIn s "a" _ _ hpre
  have hall := hpre
  gabbro_simp_at hall [wandle_pre, e_a]
  gabbro_auto2 [wandle_body, wandle_pre, wandle_post, wellFormed, e_a, hall] [wandle_body, wandle_pre, wandle_post, wellFormed, e_a] using shapeOf

def grenze_body : List Gabbro.Body.Stmt :=
  [(.ret (some (.lit (.int 8191))))]

def grenze_meets_statement : Prop :=
  ∀ (ρ : Gabbro.Body.Env) (s : Gabbro.Body.State) (hwf : wellFormed s)
    (hpre : Gabbro.Body.eval s grenze_pre = some (.bool true)),
    ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ grenze_body s) = some s'
        ∧ grenze_post s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρ grenze_body s))

open Gabbro.Body in
theorem grenze_meets : grenze_meets_statement := by
  unfold grenze_meets_statement
  intro ρ s hwf hpre
  simp only [wellFormed] at hwf ⊢
  gabbro_auto2 [grenze_body, grenze_pre, grenze_post, wellFormed] [grenze_body, grenze_pre, grenze_post, wellFormed] using shapeOf

def eins_f : UFn := u.fns[0]'(by decide)
def dreizehn_f : UFn := u.fns[1]'(by decide)
def wandle_f : UFn := u.fns[2]'(by decide)
def grenze_f : UFn := u.fns[3]'(by decide)
def minus_f : UFn := u.fns[4]'(by decide)
def voll_f : UFn := u.fns[5]'(by decide)

example : zuBody u eins_f = some eins_body := rfl
example : zuBody u dreizehn_f = some dreizehn_body := rfl
example : zuBody u wandle_f = some wandle_body := rfl
example : zuBody u grenze_f = some grenze_body := rfl
example : zuBody u minus_f = some minus_body := rfl
example : zuBody u voll_f = some voll_body := rfl
example : preExpr wandle_f = wandle_pre := rfl
example : preExpr grenze_f = grenze_pre := rfl
example : meetsU u wellFormed eins_f ((zuBody u eins_f).getD []) = eins_meets_statement := rfl
example : meetsU u wellFormed dreizehn_f ((zuBody u dreizehn_f).getD []) = dreizehn_meets_statement := rfl
example : meetsU u wellFormed wandle_f ((zuBody u wandle_f).getD []) = wandle_meets_statement := rfl
example : meetsU u wellFormed grenze_f ((zuBody u grenze_f).getD []) = grenze_meets_statement := rfl
example : meetsU u wellFormed minus_f ((zuBody u minus_f).getD []) = minus_meets_statement := rfl
example : meetsU u wellFormed voll_f ((zuBody u voll_f).getD []) = voll_meets_statement := rfl

/-- The duty of `eins`: the computed statement, closed by GabbroV's proof. -/
theorem pflicht_0 : ∃ body, zuBody u (fnAt u ⟨0, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨0, by decide⟩) body :=
  ⟨eins_body, rfl, by rw [wfU_eq]; exact eins_meets⟩

/-- The duty of `dreizehn`: the computed statement, closed by GabbroV's proof. -/
theorem pflicht_1 : ∃ body, zuBody u (fnAt u ⟨1, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨1, by decide⟩) body :=
  ⟨dreizehn_body, rfl, by rw [wfU_eq]; exact dreizehn_meets⟩

/-- The duty of `wandle`: the computed statement, closed by GabbroV's proof. -/
theorem pflicht_2 : ∃ body, zuBody u (fnAt u ⟨2, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨2, by decide⟩) body :=
  ⟨wandle_body, rfl, by rw [wfU_eq]; exact wandle_meets⟩

/-- The duty of `grenze`: the computed statement, closed by GabbroV's proof. -/
theorem pflicht_3 : ∃ body, zuBody u (fnAt u ⟨3, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨3, by decide⟩) body :=
  ⟨grenze_body, rfl, by rw [wfU_eq]; exact grenze_meets⟩

/-- The duty of `minus`: the computed statement, closed by GabbroV's proof. -/
theorem pflicht_4 : ∃ body, zuBody u (fnAt u ⟨4, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨4, by decide⟩) body :=
  ⟨minus_body, rfl, by rw [wfU_eq]; exact minus_meets⟩

/-- The duty of `voll`: the computed statement, closed by GabbroV's proof. -/
theorem pflicht_5 : ∃ body, zuBody u (fnAt u ⟨5, by decide⟩) = some body ∧
    meetsU u (wfU u) (fnAt u ⟨5, by decide⟩) body :=
  ⟨voll_body, rfl, by rw [wfU_eq]; exact voll_meets⟩

theorem pflichten : Pflichten quelle :=
  ⟨u, verankert, null, stimmig, rang, fun c => match c with
  | ⟨0, _⟩ => pflicht_0
  | ⟨1, _⟩ => pflicht_1
  | ⟨2, _⟩ => pflicht_2
  | ⟨3, _⟩ => pflicht_3
  | ⟨4, _⟩ => pflicht_4
  | ⟨5, _⟩ => pflicht_5
  | ⟨_ + 6, h⟩ => absurd h
      (by have hl : u.fns.length = 6 := by decide
          omega)⟩

/-- PREMISE (b) OF THE GOAL THEOREM for the unit the front end builds from `quelle`. -/
theorem nutzer {u' : UProg} {P : Gabbro.Grammatik.Programm (declOf u')}
    {fs : List (declOf u').Fn} (h : Gabbro.Grammatik.uebersetzeAllg quelle = .ok ⟨u', P, fs⟩) :
    ∃ hn : nullB u' = true, Gabbro.Grammatik.Zielsatz.NutzerPflicht (einheitAllg u' P hn) :=
  nutzer_aus_quelle pflichten h

/-! CHAIN-GENERIC beispiele/73-sugar-widths.gab kette_73

    P4: the closed translation-validation chain of `beispiele/73-sugar-widths`, assembled by the GENERIC `ketteAllg`
    (`Quelle.lean`): no tables, so the emitter's layout is empty; premise (b) is `nutzer_aus_quelle`.
    The instance adds WITNESS data only: the checker's Bool (a computation) and the certificate literal
    `gabbro corr-lean` prints, checked by `korrOk` (its `weiter` arm accepts the explicit conversion
    `(T)(e)` since 2026-09-30). -/

def P73 : Gabbro.Grammatik.Programm (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf u) :=
  ((lowerAllg u).toOption.get low_ok).1

theorem ht : u.tabellen = [] := rfl

/-- Pasted from `gabbro corr-lean beispiele/73-sugar-widths.gab`, generic section. -/
def zert73 : KCert (declOf u) :=
  [{ params := [(0, .int false .w8)], locals := [], rows := [GRow.ret (some ((.int false .w8), (.var 0)))], vm := [0], pp := [], ks := [] },
   { params := [(0, .int false .w16)], locals := [], rows := [GRow.ret (some ((.int false .w16), (.var 0)))], vm := [0], pp := [], ks := [] },
   { params := [(0, .int false .w32)], locals := [], rows := [GRow.ret (some ((.int false .w16), (.cast CIT.u16 (.var 0))))], vm := [0], pp := [], ks := [] },
   { params := [], locals := [], rows := [GRow.ret (some ((.int false .w64), (.lit 8191)))], vm := [], pp := [], ks := [] },
   { params := [(0, .int true .w64)], locals := [], rows := [GRow.ret (some ((.int true .w64), (.var 0)))], vm := [0], pp := [], ks := [] },
   { params := [(0, .int false .w64)], locals := [], rows := [GRow.ret (some ((.int false .w64), (.var 0)))], vm := [0], pp := [], ks := [] }]

theorem akz73 : akzeptiert_pruefer.akzeptiert (einheitAllg u P73 (pflichten_null pflichten uebersetzt))
    (aufzFn u).1 (aufzLock u).1 (aufzTraegerLeer u ht).1 = true := by decide

theorem zert73_ok : korrOk (emitLayLeer u ht) fnNr zert73 P73 (aufzFn u).1 = true := by decide

/-- **THE CLOSED CHAIN OF `beispiele/73-sugar-widths`**: source text, checker Bool, GabbroV's duties, the
    correspondence to the C -- every field a theorem. -/
def kette_73 : Kette quelle := ketteAllg pflichten uebersetzt ht zert73 akz73 zert73_ok

#print axioms pflichten
#print axioms nutzer
#print axioms kette_73

end Gabbro.Bruecke.I73
