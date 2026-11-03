module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil4a

@[expose] public section
namespace Gabbro.Grammatik.Parser.CallElseProben

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def named : SAnw := .callElse "rd" [.lit 1] "reason" (.block [] (some (.ret none)))
def unnamed : SAnw := .callElse "rd" [.lit 1] "" (.block [] (some (.ret none)))

def statementText (text : String) : Except String SAnw := do
  match lex text with
  | .ok tokens => parseTopStmt tokens
  | .error _ => .error "statement does not lex"

theorem named_source_zeuge :
    beqTopStmt (statementText "rd(1) else (reason) { return; };") (.ok named) = true := by decide +kernel

theorem unnamed_source_zeuge :
    beqTopStmt (statementText "rd(1) else { return; };") (.ok unnamed) = true := by decide +kernel

theorem missing_semicolon_zeuge :
    (statementText "rd(1) else { return; }").toOption.isNone = true := by decide +kernel

theorem malformed_reason_binder_zeuge :
    (statementText "rd(1) else (reason { return; };").toOption.isNone = true := by decide +kernel

theorem named_roundtrip_zeuge :
    beqTopStmt (parseTopStmt (druckAnw named ++ [.ende])) (.ok named) = true := by decide +kernel

theorem unnamed_roundtrip_zeuge :
    beqTopStmt (parseTopStmt (druckAnw unnamed ++ [.ende])) (.ok unnamed) = true := by decide +kernel

end Gabbro.Grammatik.Parser.CallElseProben
