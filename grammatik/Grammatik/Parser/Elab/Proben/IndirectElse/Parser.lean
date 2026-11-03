module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil4a

@[expose] public section
namespace Gabbro.Grammatik.Parser.IndirectElseProben

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def named : SAnw := .callIndElse (.variable "p") [.lit 1] "reason"
  (.block [] (some (.ret none)))
def unnamed : SAnw := .callIndElse (.fnref "read") [.lit 1] ""
  (.block [] (some (.ret none)))

def statementText (text : String) : Except String SAnw := do
  parseTopStmt (← lex text)

theorem named_source_zeuge :
    beqTopStmt (statementText "(p)(1) else (reason) { return; };") (.ok named) = true := by decide +kernel

theorem unnamed_source_zeuge :
    beqTopStmt (statementText "(&read)(1) else { return; };") (.ok unnamed) = true := by decide +kernel

theorem missing_semicolon_zeuge :
    (statementText "(p)(1) else { return; }").toOption.isNone = true := by decide +kernel

theorem malformed_reason_binder_zeuge :
    (statementText "(p)(1) else (reason { return; };").toOption.isNone = true := by decide +kernel

theorem named_roundtrip_zeuge :
    beqTopStmt (parseTopStmt (druckAnw named ++ [.ende])) (.ok named) = true := by decide +kernel

theorem unnamed_roundtrip_zeuge :
    beqTopStmt (parseTopStmt (druckAnw unnamed ++ [.ende])) (.ok unnamed) = true := by decide +kernel

/-- This fixture also exercises the generic printability derivation. -/
theorem named_printable_zeuge : AnwGut .anw named := by
  apply AnwGut.callIndElse
  · decide
  · decide
  · exact .block [] (some (.ret none)) (by intro s h; cases h) trivial (by intro h; cases h)

end Gabbro.Grammatik.Parser.IndirectElseProben
