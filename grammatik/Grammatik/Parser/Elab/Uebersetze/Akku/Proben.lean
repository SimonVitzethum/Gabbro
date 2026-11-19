/- C15: witnesses for the accumulator use export -- every generated name,
   the query head, the merge fragments, the use-site expansion and its
   narrow refusals, and the elaborated unit carrying the generated
   functions. Phase certificates use the actual canonical producers: a resolved
   count, the exact query head, the neutral literal, the narrow range text,
   the expanded update call and sampled fold, the refused bare read, and
   the elaborated unit with its query, update and reduction. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Akku.Expand
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases

-- Proof-only access to the canonical phase owners; no production visibility changes.
import all Grammatik.Parser.Elab.Uebersetze.Akku.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Akku.Expand
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil6
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil17
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Init.Data.Int.Repr
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

-- Select the actual decimal scanner step without expanding its numeric fuel.
private theorem digits_select (base fuel n : Nat) (digits : List Char) :
    Nat.toDigitsCore base fuel n digits = match fuel with
      | 0 => digits
      | rest + 1 =>
        let digit := Nat.digitChar (n % base)
        let next := n / base
        if next = 0 then digit :: digits
        else Nat.toDigitsCore base rest next (digit :: digits) := by
  cases fuel <;> rfl

attribute [local cbv_opaque] Nat.toDigitsCore
attribute [local cbv_eval] digits_select Nat.log2_def

/-- The plan of the probe accumulator: `s#kern`, `s#aktualisiere`, `s#falte`. -/
def probenAkku : AkkuPlan :=
  uAkkuPlan "s" 2

/-- A nested read is refused: reads go through the sampled fold under the
    cell locks, never bare. -/
theorem unsyncLesen_abgelehnt :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.block [.set (.variable "x") "=" (.bin "+" (.variable "s") (.lit 1))] none) =
      .error "accumulator read without G form: reads go through the sampled fold under the cell locks, never bare" := by cbv

/-- A compound update is refused: only plain assignment merges. -/
theorem akkuPlusZuweisung_abgelehnt :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.set (.variable "s") "+=" (.variable "t")) =
      .error "accumulator compound update without G form: only plain assignment merges" := by cbv

/-- A shadowed accumulator name is refused up front. -/
theorem akkuSchatten_abgelehnt :
    uAkkuKeinSchatten [probenAkku]
      [({
          art := "impl"
          name := "f"
          params := [("s", .atom "u32")]
          res := none
          fehler := none
          klauseln := []
          generics := [] },
        .block [] none)] =
      .error "accumulator name bound as a local without G form: s" := by cbv

/-! ## The elaborated unit -/

/-- The probe accumulator: two unsigned `add` cells over `0 .. 255`. -/
def probenAccT : SItemTief :=
  .accT "s" (.atom "u32") "add" (some (.lit 2)) none

/-- The probe update use: merge the argument. -/
def probenMelde : SItemTief :=
  .fnT {
    art := "impl"
    name := "melde"
    params := [("t", .atom "u32")]
    res := none
    fehler := none
    klauseln := [.effs [.writes (.variable "s")]]
    generics := [] }
    (.block [.set (.variable "s") "=" (.variable "t")] none)

/-- The probe read use: return the sampled fold. -/
def probenLies : SItemTief :=
  .fnT {
    art := "impl"
    name := "lies"
    params := []
    res := some (.atom "u32")
    fehler := none
    klauseln := []
    generics := [] }
    (.block [] (some (.ret (some (.variable "s")))))

-- The source frontend preserves this ordinary AST. Certify it separately from
-- storage generation and function-body elaboration, which consume its output.
private theorem prepared_uses :
    expandU [probenAccT, probenMelde, probenLies] =
      .ok ([probenAccT, probenMelde, probenLies], []) := by cbv

-- The generated u32 narrowing uses this exact decimal word. Keep both the
-- decimal conversion and the range reader out of later body certificates.
private theorem generated_range_text :
    uAkkuBereichText 0 4294967295 = "0 .. 4294967295" := by cbv

private theorem generated_range (ctx : UCtx) :
    uNarrowBereich ctx "0 .. 4294967295" = .ok (0, 4294967295) := by cbv

attribute [local cbv_eval] generated_range_text generated_range

-- Retain the actual post-pass values in the certified unit. These witnesses
-- inspect names, so the transitive call-floor computation can remain symbolic.
attribute [local cbv_opaque] floorOf

-- uBindWert builds floatTarget with uFloatTy even for the unannotated integer
-- and call binders below. Preserve its unused canonical bound symbolically;
-- the actual operand/type dispatch and all selected checks still run.
attribute [local cbv_opaque] uFloatLimit

attribute [local cbv_opaque] uAnwReihe uAnwReiheCore
attribute [local cbv_eval] row_nil row_cons core_bind core_trim core_locks
  core_call core_set core_cond

-- Bound the other canonical callbacks crossed by the same actual unit run.
attribute [local cbv_opaque] uAkkuBinder uZeigerAnw uStartNamen elabKlauseln
  expandReturnCall expandFoldEnd uSondenFns uTorHuellen
attribute [local cbv_eval] bound_names_select pointer_source_select start_source_select
  clauses_nil clauses_effect clauses_cost clauses_effect_cost
  return_none return_empty return_variable fold_end_none fold_end_empty fold_end_variable
  sonden_nil wrappers_nil

-- Infer the complete unit from the actual successful producer, then inspect
-- only its two name projections. No hand-built UProg replaces elaboration.
private theorem elaborated_uses :
    ∃ unit : UProg,
      elabU [probenAccT, probenMelde, probenLies] = .ok unit ∧
      unit.fns.map (·.name) = ["melde", "lies", "s#aktualisiere", "s#falte", "s#query"] ∧
      unit.axs.map (·.name) = ["s#kern"] := by
  refine ⟨?unit, ?elaborated, ?functions, ?foreignNames⟩
  case elaborated =>
    unfold elabU
    rw [prepared_uses]
    dsimp only [bind, Except.bind]
    cbv <;> exact Eq.refl _
  case functions => cbv
  case foreignNames => cbv

/-- The probe read gone wrong: a nested read is refused at elaboration. -/
def probenSchlecht : SItemTief :=
  .fnT {
    art := "impl"
    name := "schlecht"
    params := []
    res := some (.atom "u32")
    fehler := none
    klauseln := []
    generics := [] }
    (.block [] (some (.ret (some (.bin "+" (.variable "s") (.lit 1))))))

private theorem prepared_bad_read :
    expandU [probenAccT, probenSchlecht] = .ok ([probenAccT, probenSchlecht], []) := by cbv

-- This refusal is already in the canonical use-site phase, before any body
-- can be elaborated. The complete unit must retain that same error.
private theorem bad_read_expansion :
    uAkkuExpandUnit [probenAkku]
      [({
          art := "impl"
          name := "schlecht"
          params := []
          res := some (.atom "u32")
          fehler := none
          klauseln := []
          generics := [] },
        .block [] (some (.ret (some (.bin "+" (.variable "s") (.lit 1))))))] [] =
      .error "accumulator read without G form: reads go through the sampled fold under the cell locks, never bare" := by
  cbv

attribute [local cbv_eval] bad_read_expansion

/-- A unit with an unsynchronized read is refused. -/
theorem akkuVerwendung_abgelehnt :
    (elabU [probenAccT, probenSchlecht]).isOk = false := by
  unfold elabU
  rw [prepared_bad_read]
  dsimp only [bind, Except.bind]
  cbv

end Gabbro.Grammatik.Parser.Uebersetze
