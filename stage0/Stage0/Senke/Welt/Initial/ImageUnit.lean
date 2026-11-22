module

public import Stage0.InitialCheck
public import Stage0.Senke.Images.AccumulatorExport
public import Stage0.Senke.Welt.Initial.Arenas
public import Grammatik.Logik.Vertraege.Pruefer.Goal

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Senke

variable {src : String} {options : Profil.Options}

abbrev ImageStarts (u : UProg) :=
  List (Σ fn : (declOf u).Fn, Env (declOf u) ((declOf u).params fn))

/-- The ownership and foreign declarations retained from the canonical
    program. Their scope is fixed before serialization. -/
structure ImageUnitPlan (compiled : Compiled src options) where
  post : AxEns (declOf compiled.unit)
  axiomSources : Option (Vertraege.Pruefer.AxiomSources post)
  postExact : ∀ item world value, post item world value = true ↔
    ∃ old args, AxNach compiled.program.axVertrag item old args world value
  arenas : ArenaStorageExport compiled.unit
  accumulators : {entries : List (Kernzelle.AccumulatorDecl (declOf compiled.unit)) //
    List.Forall₂ (ImageAccumulator compiled) (imageAccumulatorItems compiled) entries}

def ImageUnitPlan.unit {compiled : Compiled src options} (plan : ImageUnitPlan compiled)
    (memory : Speicher (declOf compiled.unit)) (starts : ImageStarts compiled.unit) :
    Einheit (declOf compiled.unit) :=
  { OldSource.einheitVon compiled.unit compiled.program plan.post memory starts [] compiled.checkedDeclarations.val with
    axiomSources := plan.axiomSources
    arenen := plan.arenas.localInterfaces
    akku := plan.accumulators.val }

def imageCheckCarriers (u : UProg) : List ((declOf u).Tab ⊕ (declOf u).Glob) :=
  (List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr

structure CheckedImagePlan (compiled : Compiled src options) (memory : Speicher (declOf compiled.unit))
    (starts : ImageStarts compiled.unit) where
  plan : ImageUnitPlan compiled
  accepted : akzeptiertX_pruefer.akzeptiert (plan.unit memory starts)
    (List.finRange compiled.unit.fns.length) (List.finRange compiled.unit.locks.length)
    (imageCheckCarriers compiled.unit) = true

private def finishImagePlan {compiled : Compiled src options}
    (memory : Speicher (declOf compiled.unit)) (starts : ImageStarts compiled.unit)
    (plan : ImageUnitPlan compiled) : Except String (CheckedImagePlan compiled memory starts) :=
  let model := plan.unit memory starts
  let functions := List.finRange compiled.unit.fns.length
  let locks := List.finRange compiled.unit.locks.length
  let carriers := imageCheckCarriers compiled.unit
  if verdict : checkAkzeptiertX model functions locks carriers = true then
    pure ⟨plan, (akzeptiertX_pruefer_decision model functions locks carriers).trans verdict⟩
  else throw "ir: full model checker refused the image unit"

/-- The production image performs the complete checker decision on the
    exact descriptors and serialized arguments of the unit. -/
def checkImagePlan (compiled : Compiled src options) (memory : Speicher (declOf compiled.unit))
    (starts : ImageStarts compiled.unit)
    (foreign : Except String (CheckedForeignLogic compiled.unit
      (initialUnit compiled.unit compiled.program memory starts compiled.checkedDeclarations.val))) :
    Except String (CheckedImagePlan compiled memory starts) := do
  let arenas ← collectArenaStorage compiled.unit
  let accumulators ← collectImageAccumulators compiled (imageAccumulatorItems compiled)
  if empty : compiled.unit.axs.length = 0 then
    let initial := initialUnit compiled.unit compiled.program memory starts compiled.checkedDeclarations.val
    finishImagePlan memory starts ⟨initial.Q, initial.axiomSources,
      fun item _ _ => False.elim ((Nat.not_lt_zero item.val) (empty ▸ item.isLt)),
      arenas, accumulators⟩
  else
    let verified ← foreign
    finishImagePlan memory starts
      ⟨verified.summary.predicates, some verified.summary.sources, verified.summary.exactPost, arenas, accumulators⟩

end Gabbro.Stage0
