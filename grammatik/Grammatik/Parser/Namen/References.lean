module
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Namen.Gebunden
@[expose] public section
namespace Gabbro.Grammatik.Parser.Oeffentlich

/-- Whether a name is a local here. -/
def lokal (lok : List String) (s : String) : Bool := lok.any (strEq · s)

mutual
/-- **The names an expression writes**, outside the locals: place heads, called functions, function
    values, reason heads and two-segment paths, quantifier domains. -/
def namenA (lok : List String) : SExpr → List String
  | .variable s => if lokal lok s then [] else [s]
  | .field x _ => namenA lok x
  | .index x i => namenA lok x ++ namenA lok i
  | .arrow x _ => namenA lok x
  | .un _ x => namenA lok x
  | .bin _ x y => namenA lok x ++ namenA lok y
  | .call f xs => (if lokal lok f then [] else [f]) ++ namenL lok xs
  | .fnref p => if lokal lok p then [] else [p]
  | .built _ xs => namenL lok xs
  | .old x => namenA lok x
  | .why g f => if lokal lok g then [] else [g, g ++ "::" ++ f]
  | .ext .all (x :: _ :: ns) xs => ns ++ namenL (x :: lok) xs
  | .ext .any (x :: _ :: ns) xs => ns ++ namenL (x :: lok) xs
  | .ext .count (x :: _ :: ns) xs => ns ++ namenL (x :: lok) xs
  | .ext .mem (_ :: ns) xs => ns ++ namenL lok xs
  | .ext _ _ xs => namenL lok xs
  | _ => []
def namenL (lok : List String) : List SExpr → List String
  | [] => []
  | x :: xs => namenA lok x ++ namenL lok xs
end

/-- The names of an optional expression. -/
def namenO (lok : List String) : Option SExpr → List String
  | some e => namenA lok e
  | none => []

/-- **The names a type writes**: named types, paths, the table of an `index into`, and the names in
    range bounds and array lengths. -/
def namenT : STyp → List String
  | .dyn n raw => n :: (raw.toList.flatMap fun raw =>
      match lex raw with
      | .error _ => []
      | .ok ts => ts.filterMap fun | .ident name => some name | _ => none)
  | .atom s => [s]
  | .path ps => ["::".intercalate ps]
  | .ptr _ _ t => namenT t
  | .index _ t => [t]
  | .range b lo hi _ => namenT b ++ namenA [] lo ++ namenA [] hi
  | .array t n => namenT t ++ namenA [] n
  | .wrap t => namenT t
  | .embed b _ x => namenT b ++ namenO [] x
  | .str e => namenA [] e
  | .entry _ (some t) => namenT t
  | _ => []

/-- The names of an optional type. -/
def namenTO : Option STyp → List String
  | some t => namenT t
  | none => []

/-- The names an effect writes. -/
def namenE (lok : List String) : SEffekt → List String
  | .reads e | .writes e | .locks _ e | .takes e | .posts e => namenA lok e
  | .masks n | .allocs n => [n]
  | .instanceEffects n ts => n :: ts.flatMap namenT
  | _ => []

/-- The names a contract clause writes. -/
def namenK (lok : List String) : SKlausel → List String
  | .needs e | .gives e | .cost e | .drops e => namenA lok e
  | .refs ns | .keeps ns => ns
  | .load p => ["::".intercalate p]
  | .effs es => es.flatMap (namenE lok)
  | _ => []

/-- The names a function head writes: parameter and result types, the reason, every clause (the
    parameters are locals there). -/
def namenSig (s : FnSig) : List String :=
  let lok := s.generics.map SGenericParam.name ++ s.params.map Prod.fst
  (s.generics.flatMap fun | .type _ bounds => bounds | _ => []) ++
    s.params.flatMap (fun p => namenT p.2) ++ namenTO s.res ++ s.fehler.toList ++
    s.klauseln.flatMap (namenK lok)
  |>.filter (fun name => !(s.generics.map SGenericParam.name).contains name)

end Gabbro.Grammatik.Parser.Oeffentlich
