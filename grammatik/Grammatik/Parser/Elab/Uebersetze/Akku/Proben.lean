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

/-- The generated names are the accumulator name with `#kern`, `#aktualisiere`, `#falte`. -/
theorem akkuPlanNamen_zeuge : probenAkku =
    { name := "s", frage := "s#kern", akt := "s#aktualisiere",
      falt := "s#falte", kernZahl := 2 } := by cbv

/-- The query head answers `0 .. 1` with no parameters, no channel, no writes. -/
theorem akkuFrageKopf_zeuge : uAkkuFrageKopf probenAkku =
    { name := "s#kern", names := [], kinds := [], types := [],
      res := some (0, 1), held := [], ext := true } := by cbv

/-- The neutral element as a surface literal, both signs. -/
theorem akkuNeutralExpr_zeuge : uAkkuNeutralExpr 0 = .lit 0 ∧
    uAkkuNeutralExpr (-5) = .un "-" (.lit 5) := by
  exact ⟨rfl, rfl⟩

/-- The narrow range text of the value type. -/
theorem akkuBereichText_zeuge : uAkkuBereichText 0 255 = "0 .. 255" := by cbv

/-- The update arm merges and narrows required: an overflowing merge stops
    with `Logik.kapazitaet`, the contribution is never dropped. -/
theorem akkuAktArm_zeuge :
    uAkkuAktArm probenAkku 0 255 "add" 0 =
      .locks false (.variable "s#sperre0") (.block
        [.bind false "s0" none (.bin "+" (.variable "s#zelle0") (.variable "v")),
         .trimReq (.variable "s0") "0 .. 255",
         .set (.variable "s#zelle0") "=" (.variable "s0")] none) := by cbv

/-- The fold step accumulates and narrows required: an overflowing prefix
    stops with `Logik.kapazitaet`, the fold never restarts from neutral. -/
theorem akkuFaltSchritt_zeuge :
    uAkkuFaltSchritt probenAkku 0 255 "add" 0 =
      [.locks false (.variable "s#sperre0") (.block
        [.bind false "s0" none (.bin "+" (.variable "m") (.variable "s#zelle0")),
         .trimReq (.variable "s0") "0 .. 255",
         .set (.variable "m") "=" (.variable "s0")] none)] := by cbv

/-- A `writes s` effect names every cell. -/
theorem akkuEffektSchreibt_zeuge :
    uAkkuExpandEffs [probenAkku] ["s"] [.writes (.variable "s")] =
      .ok [.writes (.variable "s#zelle0"), .writes (.variable "s#zelle1")] := by cbv

/-- A `reads s` effect reads every cell. -/
theorem akkuEffektLiest_zeuge :
    uAkkuExpandEffs [probenAkku] ["s"] [.reads (.variable "s")] =
      .ok [.reads (.variable "s#zelle0"), .reads (.variable "s#zelle1")] := by cbv

/-- An update site becomes the update call. -/
theorem akkuUpdateExpandiert_zeuge :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.set (.variable "s") "=" (.variable "t")) =
      .ok [.call "s#aktualisiere" [.variable "t"]] := by cbv

/-- A trailing read becomes the sampled fold. -/
theorem akkuLesenExpandiert_zeuge :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.block [] (some (.ret (some (.variable "s"))))) =
      .ok [.block [.bind false "s#lese" none (.call "s#falte" [])]
        (some (.ret (some (.variable "s#lese"))))] := by cbv

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

/-- The query wrapper name is the accumulator name with `#query`. -/
theorem akkuHuelleName_zeuge : uAkkuHuelle probenAkku = "s#query" := by cbv

/-- The wrapper binds the hardware query once and returns its answer. -/
theorem akkuHuelleKoerper_zeuge :
    uAkkuHuelleKoerper probenAkku =
      .block [.bind false "k" none (.call "s#kern" [])]
        (some (.ret (some (.variable "k")))) := by cbv

/-- The update samples through the wrapper, never the axiom directly. -/
theorem akkuAktRuftHuelle_zeuge :
    uAkkuAktKoerper probenAkku 0 255 "add" =
      .block [.bind false "k" none (.call "s#query" []),
        uAkkuVersand probenAkku 0 255 "add" 2]
      none := by cbv

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

/-- A unit with an update use and a read use elaborates, carrying the
    generated query, update and reduction. -/
theorem akkuVerwendung_zeuge : (elabU [probenAccT, probenMelde, probenLies]).isOk = true := by
  obtain ⟨unit, made, _, _⟩ := elaborated_uses
  rw [made]
  rfl

/-- The generated functions travel with the unit, after the user functions:
    update, reduction, then the query wrapper. -/
theorem akkuFunktionen_zeuge :
    (elabU [probenAccT, probenMelde, probenLies]).map (fun u => u.fns.map (·.name)) =
      .ok ["melde", "lies", "s#aktualisiere", "s#falte", "s#query"] := by
  obtain ⟨unit, made, names, _⟩ := elaborated_uses
  rw [made]
  change (Except.ok (unit.fns.map (·.name)) : Except String (List String)) =
    .ok ["melde", "lies", "s#aktualisiere", "s#falte", "s#query"]
  rw [names]

/-- The generated query travels with the unit as the only foreign body. -/
theorem akkuFrage_zeuge :
    (elabU [probenAccT, probenMelde, probenLies]).map (fun u => u.axs.map (·.name)) =
      .ok ["s#kern"] := by
  obtain ⟨unit, made, _, names⟩ := elaborated_uses
  rw [made]
  change (Except.ok (unit.axs.map (·.name)) : Except String (List String)) = .ok ["s#kern"]
  rw [names]

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
