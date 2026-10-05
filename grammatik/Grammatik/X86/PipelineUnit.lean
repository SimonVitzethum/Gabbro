/-
  File:      Grammatik/X86/PipelineUnit.lean
  Subject:   Source-computed units and duties feeding the pipeline (lane 1177).

  The pipeline (`Pipeline.lean`, `PipelineImage.lean`, `PipelineEntry.lean`)
  takes the program as Lean data (a `Block`). This file connects it to the
  source-computed unit and its duties: the generic T3 lowering
  (`Parser/UebersetzeAllg2.lean`: `UProg` elaboration, `lowerFnAt` per
  function, `lowerAllg` for the whole unit with `List.finRange` coverage)
  produces a `Programm` whose bodies are `Endblock`s; the projection
  `rumpfBlock` carries the pipeline-admissible prefix (straight-line
  `assignSlot` chains, the T3 body language without calls) to a pipeline
  `Block`, and the closing Bool `einheitSchluss` conjoins the pipeline
  checks (`validate`, `imageOk`, `weltOk`, `prologImageOk`,
  `eintrittZulassung`) with the entry duty (`requires` at the actual
  arguments). Duties at call sites are carried through the accepted
  `ContractSites` producers (`callSite_vorOk`, `rufAt_ok_gibt_ens`).

  Reused, not duplicated: everything from `Pipeline.lean`,
  `PipelineImage.lean`, `PipelineEntry.lean`, `ContractSites.lean` and the
  T3 lowering. No second interpreter, no per-program rule, no new executor.
-/
import Grammatik.X86.PipelineEntry
import Grammatik.X86.ContractSites
import Grammatik.ZielOrtZeuge
import Grammatik.Parser.UebersetzeAllg2

namespace Gabbro.Grammatik.X86.PipelineUnit

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage
open Gabbro.Grammatik.X86.PipelineEntry
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Body prefix projection: straight-line `assignSlot` chains (the T3 body
    language without calls) become the pipeline `Block`; every tail form
    (`ret`, `retGrund`, `leave`, `next`) ends the block with `.nil`.
    Everything else (calls, control, binders, locks) is REFUSED (`none`). -/
def rumpfBlock : Endblock D V l Γ Λ → Option (Block D V l Γ Λ Λ)
  | .cons (.assignSlot t f i e hw hL) rest =>
    match rumpfBlock rest with
    | some b => some (.cons (.assignSlot t f i e hw hL) b)
    | none => none
  | .cons _ _ => none
  | .ret _ _ => some .nil
  | .retGrund _ _ => some .nil
  | .leave _ => some .nil
  | .next _ => some .nil
  | _ => none

/-- Tail projection: the `Endblock` tail a projected prefix runs into
    (`ret`, `retGrund`, `leave`, `next`); `none` exactly when the body
    leaves the fragment. -/
def rumpfEnde : Endblock D V l Γ Λ → Option (Endblock D V l Γ Λ)
  | .cons (.assignSlot _ _ _ _ _ _) rest => rumpfEnde rest
  | .cons _ _ => none
  | .ret e h => some (.ret e h)
  | .retGrund r h => some (.retGrund r h)
  | .leave h => some (.leave h)
  | .next h => some (.next h)
  | _ => none

/-- TOTALITY (fuel): a projected block always runs clean through the real
    `execBlock` (every `assignSlot` step yields `.ok` by definition, and
    `.nil` does too). Fuel is `sizeOf body`; the recursive call runs on the
    tail with strictly smaller size. -/
theorem rumpfBlock_total_aux (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (n : Nat) :
    ∀ (body : Endblock D V l Γ Λ) (b : Block D V l Γ Λ Λ),
    sizeOf body ≤ n → rumpfBlock body = some b → ∀ (σ : World D) (ρ : Env D Γ),
    ∃ σ' ρ', execBlock O passes R b σ ρ = .ok σ' ρ' := by
  induction n with
  | zero =>
    intro body b
    cases body with
    | cons s rest =>
      intro hle hb σ ρ
      simp only [Endblock.cons.sizeOf_spec] at hle
      omega
    | ret e h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.ret e h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | retGrund r h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.retGrund r h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | leave h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.leave h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | next h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.next h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | bind e rest =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.bind e rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiom a args he hw hg hd hgd rest =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiom a args he hw hg hd hgd rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiomElse a args he hr hw hg hd hgd err rest =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiomElse a args he hr hw hg hd hgd err rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
  | succ n ih =>
    intro body b
    cases body with
    | cons s rest =>
      cases s with
      | assignSlot t f i e hw hL =>
        intro hle hb σ ρ
        cases hr : rumpfBlock rest with
        | none =>
          have h0 : rumpfBlock (D := D) (V := V)
              (.cons (.assignSlot t f i e hw hL) rest) = none := by
            simp [rumpfBlock, hr]
          rw [h0] at hb
          cases hb
        | some b' =>
          have h0 : rumpfBlock (D := D) (V := V)
              (.cons (.assignSlot t f i e hw hL) rest) =
              some (.cons (.assignSlot t f i e hw hL) b') := by
            simp [rumpfBlock, hr]
          rw [h0] at hb
          obtain rfl := Option.some.inj hb
          have hstep := execStmt_assignSlot (V := V) (l := l) O passes R
            t f i e hw hL σ ρ
          have hcons : execBlock O passes R
              (.cons (.assignSlot (V := V) t f i e hw hL) b') σ ρ =
              execBlock O passes R b'
                ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
                  (eval (σ.lese Λ (i.orte ++ e.orte)) i
                    (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
                  (eval (σ.lese Λ (i.orte ++ e.orte)) e
                    (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by
            simp only [execBlock, hstep]
          have hle' : sizeOf rest ≤ n := by
            simp only [Endblock.cons.sizeOf_spec] at hle
            omega
          rw [hcons]
          exact ih rest b' hle' hr _ _
      | _ =>
        intro hle hb σ ρ
        simp [rumpfBlock] at hb
    | ret e h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.ret e h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | retGrund r h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.retGrund r h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | leave h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.leave h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | next h =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.next h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      rw [h0] at hb
      obtain rfl := Option.some.inj hb
      exact ⟨σ, ρ, by simp [execBlock]⟩
    | bind e rest =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V) (.bind e rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiom a args he hw hg hd hgd rest =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiom a args he hw hg hd hgd rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiomElse a args he hr hw hg hd hgd err rest =>
      intro hle hb σ ρ
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiomElse a args he hr hw hg hd hgd err rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb

/-- TOTALITY: a projected block always runs clean through the real
    `execBlock`. -/
theorem rumpfBlock_total (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (body : Endblock D V l Γ Λ) (b : Block D V l Γ Λ Λ)
    (hb : rumpfBlock body = some b) (σ : World D) (ρ : Env D Γ) :
    ∃ σ' ρ', execBlock O passes R b σ ρ = .ok σ' ρ' :=
  rumpfBlock_total_aux O passes R (sizeOf body) body b (Nat.le_refl _) hb σ ρ

/- CUTS (exactly what is NOT proved here):
    Skeleton only: the projection above, nothing else yet.
-/

#print axioms rumpfBlock
#print axioms rumpfEnde
#print axioms rumpfBlock_total

end Gabbro.Grammatik.X86.PipelineUnit
