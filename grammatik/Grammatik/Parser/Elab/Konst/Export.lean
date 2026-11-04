module

public import Grammatik.Parser.Elab.Konst.Ableitung
public import Grammatik.Kern.Syntax.Konst.Zertifikat
public import Grammatik.Kern.Syntax.Konst.Rang
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-! ## Certified const-block evaluation at the exporter.

  Stage 4 of the C17 const-block design, exporter side: every non-value
  `ConstCallResult` keeps a named refusal, and block-bodied const functions
  are dispatched through the certified vocabulary instead of the stage-3
  placeholder. Full value delivery through this hook awaits `elabConstProgram`
  (a later slice builds `ConstProgram` values with their source derivations
  from surface items); until then block bodies are refused as unresolved
  dependencies naming the function, while expression bodies keep the
  existing `uKonstWert` path unchanged. `const_source_call_sound` ties a
  source-derived call to the generic meaning theorem. -/

/-- The four failure kinds of a checked const call, with source identity. -/
inductive ConstBlockFehlerArt where
  | vertrag : ConstBlockFehlerArt
  | bereich : ConstBlockFehlerArt
  | abhaengigkeit : ConstBlockFehlerArt
  | erschoepfung : Nat → Nat → ConstBlockFehlerArt

/-- One named refusal per failure kind. -/
@[expose] def constBlockFehler (name : String) : ConstBlockFehlerArt → String
  | .vertrag => "const contract violated at `" ++ name ++ "`: certified requires/ensures failed"
  | .bereich => "const range failure at `" ++ name ++ "`: certified evaluation found no value in range"
  | .abhaengigkeit => "const unresolved dependency at `" ++ name ++ "`: certified evaluation needs its callees"
  | .erschoepfung gebraucht limit => "const resource exhaustion at `" ++ name ++ "`: certified work bound exceeded (used " ++ toString gebraucht ++ " of " ++ toString limit ++ ")"

/-- Project a checked result onto its failure kind, if any. -/
@[expose] def constErgebnisArt (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f)) :
    ConstCallResult c f args → Option ConstBlockFehlerArt
  | .value _ => none
  | .contract _ => some .vertrag
  | .range _ => some .bereich
  | .dependency _ => some .abhaengigkeit
  | .exhausted gebraucht limit => some (.erschoepfung gebraucht limit)

/-- The refusal sentence for a checked result, if it failed. -/
@[expose] def constErgebnisFehler (name : String) (r : ConstCallResult c f args) : Option String :=
  (constErgebnisArt c f args r).map (constBlockFehler name)

/-- Refuse a block-bodied const function through the certified vocabulary.
    Until `elabConstProgram` supplies certificates, the applicable kind is
    the unresolved dependency naming the function. -/
@[expose] def constBlockVerweigerung (k : Uebersetze.UKonstFn) : Except String Uebersetze.UProg :=
  .error (constBlockFehler k.name .abhaengigkeit)

/-- The exporter hook for one const function: expression bodies keep the
    existing checked `uKonstWert` path (unknown shapes and non-integer
    results defer to the surrounding pipeline); block bodies take the
    certified refusal above. -/
@[expose] def constFnWert (fns : List Uebersetze.UKonstFn) (k : Uebersetze.UKonstFn) :
    Except String (Option Int) :=
  match k.rumpf with
  | .block [] (some (.ret (some e))) =>
    match k.erg with
    | .int lo hi => .ok (Uebersetze.uKonstWert lo hi fns [] 64 e)
    | _ => .ok none
  | _ => .error (constBlockFehler k.name .abhaengigkeit)

/-- Source meaning theorem: a jointly source-derived call with a successful
    checked evaluation denotes through the generic call theorem. The
    elaboration ties this call to its source derivation; admissibility
    covers the callees reached during evaluation. -/
theorem const_source_call_sound (c : ConstProgram) (f : c.D.Fn) (args : Env c.D (c.D.params f))
    (cert : ConstCallCertificate c f args) (hadm : ConstAdmissible c) (n : Nat)
    (hterm : ConstTermination c n)
    {items : List SItemTief} {scope : ConstScope c.D} {item : SItemTief}
    (helab : ConstElaborates items scope item f) :
    ∀ (σ : World c.D) (O : Orakel c.D) (passes depth : Nat),
      max cert.bound (n + 1) ≤ depth →
      ∃ σ', rufAt c.P O passes depth f σ args = RufAusgang.ok σ' cert.value ∧ σ'.slots = σ.slots ∧ σ'.globs = σ.globs := by
  have _ := helab.rein
  intro σ O passes depth hdepth
  exact const_call_sound c f args cert hadm n hterm σ O passes depth hdepth

/-- Control witness: an expression-bodied const function evaluates through
    the existing exporter path. -/
@[expose] def fnExprDrei : Uebersetze.UKonstFn := { name := "drei", params := [], erg := .int 0 10, rumpf := .block [] (some (.ret (some (.lit 3)))), signature := { art := "const", name := "drei", params := [], res := some (.atom "u8"), fehler := none, klauseln := [] } }

/-- The control value arrives through the hook. -/
theorem fnExprWert_zeuge : constFnWert [] fnExprDrei = .ok (some 3) := by decide

/-- Block-bodied witness for the refusal path. -/
@[expose] def fnBlockWert : Uebersetze.UKonstFn := { name := "blockiert", params := [], erg := .int 0 10, rumpf := .block [.bind false "x" none (.lit 1)] (some (.ret (some (.lit 2)))), signature := { art := "const", name := "blockiert", params := [], res := some (.atom "u8"), fehler := none, klauseln := [] } }

/-- A block body is refused with its named sentence. -/
theorem fnBlockVerweigerung_zeuge : constFnWert [] fnBlockWert = .error (constBlockFehler "blockiert" .abhaengigkeit) := by decide

end Gabbro.Grammatik.Parser
