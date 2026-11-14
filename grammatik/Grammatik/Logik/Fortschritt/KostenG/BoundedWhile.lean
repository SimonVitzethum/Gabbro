module

public import Grammatik.Logik.Fortschritt.KostenG.T1
public import Grammatik.Kern.Syntax.Extensions.Extraktion.T2
public import Grammatik.Kern.Syntax.Satz.T3

public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Retry's static multiplier is inherited unchanged. The extra unit at each
    test is the explicitly represented boolean negation, never an uncharged op. -/
theorem kostenStmt_wloop (ep : Nat) (cost : D.Fn → Nat) (passes n : Nat)
    (c : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) :
    kostenStmt ep cost passes (.wloop n c body ueberlauf) =
      2 + n * (kostenBlock ep cost passes body + (1 + kostenExpr c) + 2) +
        (2 + (1 + kostenExpr c) + kostenBlock ep cost passes ueberlauf) := rfl

/-- Complementing the test adds no read and drops no body or handler place. -/
theorem wloop_orte (n : Nat) (c : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueberlauf : Block D V l Γ Λ Λ) :
    Extraktion.stmtOrte (.wloop n c body ueberlauf) =
      c.orte ++ Extraktion.blockOrte body ++ Extraktion.blockOrte ueberlauf := rfl

/-- The scope component of acceptance applies exactly retry's body and handler
    checks. All other syntax consumers likewise see the same core statement. -/
theorem wloop_scopesOk (held : List D.Lock) (floor : Option Int) (n : Nat)
    (c : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) :
    (Stmt.wloop n c body ueberlauf).scopesOk held floor =
      (body.scopesOk held floor && ueberlauf.scopesOk held floor) := rfl

/-- Call-graph admission checks both blocks, with precisely retry's gates. -/
theorem rufeS_wloop (calls : D.Fn → Bool) (indirect : Nat → Bool) (forever : Bool)
    (n : Nat) (c : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) :
    rufeS calls indirect forever (.wloop n c body ueberlauf) =
      (rufeB calls indirect forever body && rufeB calls indirect forever ueberlauf) := rfl

end Gabbro.Grammatik
