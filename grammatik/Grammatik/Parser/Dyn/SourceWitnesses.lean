module

import Grammatik.Parser.TaggedDispatch.Frontend
import Grammatik.Parser.Print.Item

namespace Gabbro.Grammatik.Parser.Dyn
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def source : String :=
  "table Circles count 4 { slot { r: u64, } } " ++
  "table Rects count 4 { slot { r: u64, } } " ++
  "spec Shape[T; effects E] { fn area(s: T) -> u64 " ++
  "ensures result >= 1 effects { E } costs <= 50 ops; } " ++
  "impl Shape[index into Circles; effects { reads Circles }] { " ++
  "fn area(s: index into Circles) -> u64 ensures result >= 1 " ++
  "effects { reads Circles } costs <= 20 ops { return 1; } } " ++
  "impl Shape[index into Rects; effects { reads Rects }] { " ++
  "fn area(s: index into Rects) -> u64 ensures result >= 1 " ++
  "effects { reads Rects } costs <= 20 ops { return 1; } } " ++
  "table Scene count 256 { slot { s: dyn Shape effects { reads Circles, reads Rects }, } } " ++
  "impl fn draw(c: index into Circles, i: index into Scene, j: index into Scene) -> u64 " ++
  "effects { reads Circles, reads Rects, reads Scene, writes Scene } costs <= 100 ops { " ++
  "Scene[i].s = dyn Shape(c); let a = Shape::area(Scene[j].s); return a; }"

private def parsed : Except String (List SItemTief) := do
  parseTopTief (← lex source)

private def expanded : Except String (List SItemTief) := do
  exportDeclarationUnit (← parsed)

/-- Source text, lexer, parser and the actual front-end expansion agree on the closed cases. -/
public theorem dyn_source_scene_zeuge :
    (expanded.map fun items => items.filterMap fun
      | .typeT ["tagged"] n [] [] (some (.raw raw)) => some (n, raw)
      | _ => none) =
    .ok [("#dyn0", "{ GabbroDyn0Case0(index into Circles), GabbroDyn0Case1(index into Rects) }")] := rfl

public theorem dyn_producer_parser_zeuge :
    (parseTop [ .wort "dyn", .ident "Shape", .zeichen "(", .ident "c", .zeichen ")", .ende]) =
    .ok (.ext .dyn ["Shape"] [.variable "c"]) := rfl

public theorem dyn_type_parser_zeuge :
    (parseTyp 100 [.wort "dyn", .ident "Shape", .wort "effects", .zeichen "{",
      .wort "reads", .ident "Circles", .zeichen "}", .ende]) =
    .ok (.dyn "Shape" (some "reads Circles } "), [.ende]) := rfl

end Gabbro.Grammatik.Parser.Dyn
