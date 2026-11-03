module

public import Grammatik.Parser.Item.ElementTief

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The texts of the pointer types a surface type list names (`fn (` raw types). -/
def uZeigerTexte : List STyp → List String
  | [] => []
  | .raw r :: rest => if r.startsWith "fn (" then r :: uZeigerTexte rest else uZeigerTexte rest
  | _ :: rest => uZeigerTexte rest

/-- The pointer types written at a `let` of a body. -/
def uZeigerAnw : Nat → SAnw → List String
  | 0, _ => []
  | f + 1, a => match a with
    | .bind _ _ (some t) _ => uZeigerTexte [t]
    | .bindElse _ (some t) _ _ b => uZeigerTexte [t] ++ uZeigerAnw f b
    | .callElse _ _ _ b => uZeigerAnw f b
    | .bindElse _ none _ _ b => uZeigerAnw f b
    | .bindQ _ _ (some t) _ | .bindAxiomOpt _ (some t) _ => uZeigerTexte [t]
    | .bindAxiomOptElse _ ty _ _ b => uZeigerTexte ty.toList ++ uZeigerAnw f b
    | .await _ ty _ _ | .swap _ ty _ _ | .allocVon _ _ ty _ => uZeigerTexte ty.toList
    | .cond _ t es e => uZeigerAnw f t ++ (es.flatMap (uZeigerAnw f)) ++ (match e with | some b => uZeigerAnw f b | none => [])
    | .elsif _ b => uZeigerAnw f b
    | .cases _ as => as.flatMap (uZeigerAnw f)
    | .arm _ _ b => uZeigerAnw f b
    | .each _ _ _ _ _ _ _ b => uZeigerAnw f b
    | .retry _ b => uZeigerAnw f b
    | .loop _ b => uZeigerAnw f b
    | .waive _ b => uZeigerAnw f b
    | .trim _ _ b => uZeigerAnw f b
    | .locks _ _ b => uZeigerAnw f b
    | .watch _ b => uZeigerAnw f b
    | .alloc _ _ ty _ _ body => uZeigerTexte ty.toList ++ (body.map (uZeigerAnw f) |>.getD [])
    | .grow _ _ b => uZeigerAnw f b
    | .child b => uZeigerAnw f b
    | .block as _ => as.flatMap (uZeigerAnw f)
    | _ => []

end Gabbro.Grammatik.Parser.Uebersetze
