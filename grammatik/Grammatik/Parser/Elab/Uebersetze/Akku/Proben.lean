/- C15: witnesses for the accumulator use export -- every generated name,
   the query head, the merge fragments, the use-site expansion and its
   narrow refusals, and the elaborated unit carrying the generated
   functions. The decider runs by kernel evaluation (`rfl`): a resolved
   count, the exact query head, the neutral literal, the narrow range text,
   the expanded update call and sampled fold, the refused bare read, and
   the elaborated unit with its query, update and reduction. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Akku.Expand
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The plan of the probe accumulator: `s#kern`, `s#aktualisiere`, `s#falte`. -/
def probenAkku : AkkuPlan :=
  uAkkuPlan "s" 2

/-- The generated names are the accumulator name with `#kern`, `#aktualisiere`, `#falte`. -/
theorem akkuPlanNamen_zeuge : probenAkku =
    { name := "s", frage := "s#kern", akt := "s#aktualisiere",
      falt := "s#falte", kernZahl := 2 } := rfl

/-- The query head answers `0 .. 1` with no parameters, no channel, no writes. -/
theorem akkuFrageKopf_zeuge : uAkkuFrageKopf probenAkku =
    { name := "s#kern", names := [], kinds := [], types := [],
      res := some (0, 1), held := [], ext := true } := rfl

/-- The neutral element as a surface literal, both signs. -/
theorem akkuNeutralExpr_zeuge : uAkkuNeutralExpr 0 = .lit 0 ∧
    uAkkuNeutralExpr (-5) = .un "-" (.lit 5) := by
  exact ⟨rfl, rfl⟩

/-- The narrow range text of the value type. -/
theorem akkuBereichText_zeuge : uAkkuBereichText 0 255 = "0 .. 255" := rfl

/-- The update arm merges and narrows required: an overflowing merge stops
    with `Logik.kapazitaet`, the contribution is never dropped. -/
theorem akkuAktArm_zeuge :
    uAkkuAktArm probenAkku 0 255 "add" 0 =
      .locks false (.variable "s#sperre0") (.block
        [.bind false "s0" none (.bin "+" (.variable "s#zelle0") (.variable "v")),
         .trimReq (.variable "s0") "0 .. 255",
         .set (.variable "s#zelle0") "=" (.variable "s0")] none) := rfl

/-- The fold step accumulates and narrows required: an overflowing prefix
    stops with `Logik.kapazitaet`, the fold never restarts from neutral. -/
theorem akkuFaltSchritt_zeuge :
    uAkkuFaltSchritt probenAkku 0 255 "add" 0 =
      [.locks false (.variable "s#sperre0") (.block
        [.bind false "s0" none (.bin "+" (.variable "m") (.variable "s#zelle0")),
         .trimReq (.variable "s0") "0 .. 255",
         .set (.variable "m") "=" (.variable "s0")] none)] := rfl

/-- A `writes s` effect names every cell. -/
theorem akkuEffektSchreibt_zeuge :
    uAkkuExpandEffs [probenAkku] ["s"] [.writes (.variable "s")] =
      .ok [.writes (.variable "s#zelle0"), .writes (.variable "s#zelle1")] := rfl

/-- A `reads s` effect reads every cell. -/
theorem akkuEffektLiest_zeuge :
    uAkkuExpandEffs [probenAkku] ["s"] [.reads (.variable "s")] =
      .ok [.reads (.variable "s#zelle0"), .reads (.variable "s#zelle1")] := rfl

/-- An update site becomes the update call. -/
theorem akkuUpdateExpandiert_zeuge :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.set (.variable "s") "=" (.variable "t")) =
      .ok [.call "s#aktualisiere" [.variable "t"]] := rfl

/-- A trailing read becomes the sampled fold. -/
theorem akkuLesenExpandiert_zeuge :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.block [] (some (.ret (some (.variable "s"))))) =
      .ok [.block [.bind false "s#lese" none (.call "s#falte" [])]
        (some (.ret (some (.variable "s#lese"))))] := rfl

/-- A nested read is refused: reads go through the sampled fold under the
    cell locks, never bare. -/
theorem unsyncLesen_abgelehnt :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.block [.set (.variable "x") "=" (.bin "+" (.variable "s") (.lit 1))] none) =
      .error "accumulator read without G form: reads go through the sampled fold under the cell locks, never bare" := rfl

/-- A compound update is refused: only plain assignment merges. -/
theorem akkuPlusZuweisung_abgelehnt :
    uAkkuExpandAnw [probenAkku] ["s"] 100000
      (.set (.variable "s") "+=" (.variable "t")) =
      .error "accumulator compound update without G form: only plain assignment merges" := rfl

/-- A shadowed accumulator name is refused up front. -/
theorem akkuSchatten_abgelehnt :
    uAkkuKeinSchatten [probenAkku]
      [({ art := "impl", name := "f", params := [("s", .atom "u32")],
        res := none, fehler := none, klauseln := [] },
        .block [] none)] =
      .error "accumulator name bound as a local without G form: s" := rfl

/-! ## The elaborated unit -/

/-- The probe accumulator: two unsigned `add` cells over `0 .. 255`. -/
def probenAccT : SItemTief :=
  .accT "s" (.atom "u32") "add" (some (.lit 2))

/-- The probe update use: merge the argument. -/
def probenMelde : SItemTief :=
  .fnT { art := "impl", name := "melde", params := [("t", .atom "u32")],
    res := none, fehler := none,
    klauseln := [.effs [.writes (.variable "s")]] }
    (.block [.set (.variable "s") "=" (.variable "t")] none)

/-- The probe read use: return the sampled fold. -/
def probenLies : SItemTief :=
  .fnT { art := "impl", name := "lies", params := [],
    res := some (.atom "u32"), fehler := none, klauseln := [] }
    (.block [] (some (.ret (some (.variable "s")))))

/-- A unit with an update use and a read use elaborates, carrying the
    generated query, update and reduction. -/
theorem akkuVerwendung_zeuge : (elabU [probenAccT, probenMelde, probenLies]).isOk = true := rfl

/-- The generated functions travel with the unit, after the user functions. -/
theorem akkuFunktionen_zeuge :
    (elabU [probenAccT, probenMelde, probenLies]).map (fun u => u.fns.map (·.name)) =
      .ok ["melde", "lies", "s#aktualisiere", "s#falte"] := rfl

/-- The generated query travels with the unit as the only foreign body. -/
theorem akkuFrage_zeuge :
    (elabU [probenAccT, probenMelde, probenLies]).map (fun u => u.axs.map (·.name)) =
      .ok ["s#kern"] := rfl

/-- The probe read gone wrong: a nested read is refused at elaboration. -/
def probenSchlecht : SItemTief :=
  .fnT { art := "impl", name := "schlecht", params := [],
    res := some (.atom "u32"), fehler := none, klauseln := [] }
    (.block [] (some (.ret (some (.bin "+" (.variable "s") (.lit 1))))))

/-- A unit with an unsynchronized read is refused. -/
theorem akkuVerwendung_abgelehnt :
    (elabU [probenAccT, probenSchlecht]).isOk = false := rfl

end Gabbro.Grammatik.Parser.Uebersetze
