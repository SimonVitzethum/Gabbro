/- Exact foreign-gate unit values. Source.lean checks each against the actual
   elaborator; the explicit values keep dependent checker access inexpensive. -/
module
public import Grammatik.Parser.Elab.Uebersetze.Kontext.Scopes
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The ordinary entry, Boolean probe and reporter shared by both sources. -/
def foreignGatePrefix : List UFn :=
  [{ name := "g", params := [], kinds := [], res := none, held := [], puts := [],
     gives := [], body := [], ret := .empty },
   { name := "p#probe", params := [], kinds := [], res := none, resBool := true,
     held := [], puts := [], gives := [],
     body := [.bindB "#checkVerdict" .tru,
       .bindCall "#checkReport" "p#report#0"
         [.bval (.cmp ">=" (.lit 2) (.lit 1)), .bval (.var "#checkVerdict")]],
     ret := .bool (.var "#checkReport"), nimmt := ["p#duty"], gibt := ["p#duty"] },
   { name := "p#report#0", params := [("f0", .bool), ("v", .bool)],
     kinds := [.bool, .bool], res := none, resBool := true, held := [], puts := [],
     gives := [], body := [], ret := .bool (.and (.var "v") (.var "f0")),
     checkReturn := some { check := "p", point := 0, samples := [("x", none)],
       floorStart := 0, floorCount := 1 } }]

/-- The exact elaborated check, including its real Duty and foreign gate. -/
def foreignGateCheck : UCheck :=
  { name := "p", claim := "c", misst := [.variable "x"], tore := ["f"],
    boeden := [.cmp ">=" (.lit 2) (.lit 1)], sonde := none, testbau := false,
    probe := "p#probe", duty := "p#duty" }

/-- The infallible source value retains its source-export refusal as metadata. -/
def uFremd : UProg where
  tabs := []
  locks := []
  fns := foreignGatePrefix ++
    [{ name := "p#tor#f", params := [], kinds := [], res := none, held := [],
       puts := [], gives := [], body := [.axCall "f" []], ret := .empty,
       nimmt := ["p#duty"], gibt := ["p#duty"] }]
  axs := [{ name := "f", params := [], kinds := [], res := none }]
  exportGate := .error "source export: SItemTief.axiomT: type/provider/proof duties lack a checked source binding"
  checks := [foreignGateCheck]
  marken := ["p#duty"]

/-- The fallible source value preserves both reason rethrows and the Duty. -/
def uFremdFallible : UProg where
  tabs := []
  locks := []
  fns := foreignGatePrefix ++
    [{ name := "p#tor#f", params := [], kinds := [], res := some (0, 18446744073709551615),
       gruende := 1, held := [], puts := [], gives := [],
       body := [.bindAxElse "ans" "f" [] "e", .matchWhyBeg "e", .ret (.why 0),
         .blkEnd, .ret (.why 0), .blkEnd], ret := .val (.param "ans"),
       nimmt := ["p#duty"], gibt := ["p#duty"] }]
  axs := [{ name := "f", params := [], kinds := [],
    res := some (.int 0 18446744073709551615), gruende := 1 }]
  whys := [{ name := "R", cases := ["A"],
    descriptor := some { name := 0, codes := [0], closed := true, distinct := by decide } }]
  checks := [foreignGateCheck]
  marken := ["p#duty"]

end Gabbro.Grammatik.Parser.Uebersetze
