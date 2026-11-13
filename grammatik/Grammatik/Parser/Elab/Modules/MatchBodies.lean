/- Shared body traversal for source match rewrites. No expressions or model rules change. -/
module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
@[expose] public section

namespace Gabbro.Grammatik.Parser.MatchBodies

/-- A match may become several ordinary statements. The lexical locals are supplied so a
    rewrite can distinguish a frame-local scrutinee from a mutable global read. -/
abbrev Rewrite := List String → Nat → SExpr → List SAnw →
  Except String (List SAnw × Nat)

/-- The walk used by both match sugars. Rewrite a match before visiting its resulting bodies,
    including copied tagged arms. Thread fresh names in source order and flatten generated
    statement sequences into their enclosing block (a bare block is not a G statement). -/
def walk (rewrite : Rewrite) : Nat → List String → Nat → SAnw →
    Except String (List SAnw × Nat)
  | 0, _, nr, s => .ok ([s], nr)
  | n + 1, locals, nr, s => do
    let (statements, nr) ← match s with
      | .cases e arms => rewrite locals nr e arms
      | _ => pure ([s], nr)
    let body : List String → Nat → SAnw → Except String (SAnw × Nat) := fun extra nr b => do
      let (ss, nr) ← walk rewrite n (extra ++ locals) nr b
      let result := match ss with | [one] => one | many => .block many none
      pure (result, nr)
    let bodies : Nat → List SAnw → Except String (List SAnw × Nat) := fun nr ss =>
      ss.foldlM (fun (acc : List SAnw × Nat) t => do
        let r ← body [] acc.2 t
        pure (acc.1 ++ [r.1], r.2)) ([], nr)
    statements.foldlM (fun (acc : List SAnw × Nat) statement => do
      let nr := acc.2
      let r : SAnw × Nat ← match statement with
        | .cond c t eis otherwise => do
          let rt ← body [] nr t
          let re ← bodies rt.2 eis
          match otherwise with
          | none => pure (.cond c rt.1 re.1 none, re.2)
          | some b => do
            let rb ← body [] re.2 b
            pure (.cond c rt.1 re.1 (some rb.1), rb.2)
        | .elsif c b => do
          let r ← body [] nr b
          pure (.elsif c r.1, r.2)
        | .cases e arms => do
          let r ← bodies nr arms
          pure (.cases e r.1, r.2)
        | .arm name binder b => do
          let r ← body binder.toList nr b
          pure (.arm name binder r.1, r.2)
        | .each a b c d m raw inv bdy => do
          let r ← body [a] nr bdy
          pure (.each a b c d m raw inv r.1, r.2)
        | .retry h b => do
          let r ← body [] nr b
          pure (.retry h r.1, r.2)
        | .loop h b => do
          let r ← body [] nr b
          pure (.loop h r.1, r.2)
        | .waive ns b => do
          let r ← body [] nr b
          pure (.waive ns r.1, r.2)
        | .trim o t b => do
          let r ← body [] nr b
          pure (.trim o t r.1, r.2)
        | .locks g o b => do
          let r ← body [] nr b
          pure (.locks g o r.1, r.2)
        | .watch d b => do
          let r ← body [] nr b
          pure (.watch d r.1, r.2)
        | .block ss ending => do
          let r ← ss.foldlM (fun (acc : List SAnw × Nat × List String) t => do
            let r ← walk rewrite n acc.2.2 acc.2.1 t
            pure (acc.1 ++ r.1, r.2, ExportMetadata.binders t ++ acc.2.2)) ([], nr, locals)
          pure (.block r.1 ending, r.2.1)
        | .bindElse x ty e g b => do
          let r ← body [g] nr b
          pure (.bindElse x ty e g r.1, r.2)
        | .callElse f args g b => do
          let r ← body [g] nr b
          pure (.callElse f args g r.1, r.2)
        | .callIndElse p args g b => do
          let r ← body [g] nr b
          pure (.callIndElse p args g r.1, r.2)
        | .bindAxiomOptElse x ty e g b => do
          let r ← body [g] nr b
          pure (.bindAxiomOptElse x ty e g r.1, r.2)
        | .alloc mu x ty arena count failure => do
          match failure with
          | none => pure (statement, nr)
          | some b => do
            let r ← body [] nr b
            pure (.alloc mu x ty arena count (some r.1), r.2)
        | .grow arena count b => do
          let r ← body [] nr b
          pure (.grow arena count r.1, r.2)
        | .child b => do
          let r ← body [] nr b
          pure (.child r.1, r.2)
        | _ => pure (statement, nr)
      pure (acc.1 ++ [r.1], r.2)) ([], nr)

end Gabbro.Grammatik.Parser.MatchBodies
