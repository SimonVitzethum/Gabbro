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

/-- BRIDGE (fuel): the full body run is the tail run at the world the
    projected prefix reaches. Both sides step through the same real
    `execStmt`; `assignSlot` always yields `.ok`, so prefix and body agree
    on every step. -/
theorem rumpfBruecke_aux (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (n : Nat) :
    ∀ (body : Endblock D V l Γ Λ) (b : Block D V l Γ Λ Λ)
    (tail : Endblock D V l Γ Λ),
    sizeOf body ≤ n → rumpfBlock body = some b → rumpfEnde body = some tail →
    ∀ (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ),
    execBlock O passes R b σ ρ = .ok σ' ρ' →
    execEnd O passes R body σ ρ = execEnd O passes R tail σ' ρ' := by
  induction n with
  | zero =>
    intro body b tail
    cases body with
    | cons s rest =>
      intro hle hb he σ ρ σ' ρ' hsrc
      simp only [Endblock.cons.sizeOf_spec] at hle
      omega
    | ret e h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.ret e h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.ret e h) =
        some ((.ret e h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | retGrund r h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.retGrund r h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.retGrund r h) =
        some ((.retGrund r h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | leave h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.leave h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.leave h) =
        some ((.leave h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | next h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.next h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.next h) =
        some ((.next h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | bind e rest =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.bind e rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiom a args he hw hg hd hgd rest =>
      intro hle hb hee σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiom a args he hw hg hd hgd rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiomElse a args he hr hw hg hd hgd err rest =>
      intro hle hb hee σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiomElse a args he hr hw hg hd hgd err rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
  | succ n ih =>
    intro body b tail
    cases body with
    | cons s rest =>
      cases s with
      | assignSlot t f i e hw hL =>
        intro hle hb he σ ρ σ' ρ' hsrc
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
          have ht : rumpfEnde (D := D) (V := V)
              (.cons (.assignSlot t f i e hw hL) rest) = rumpfEnde rest := by
            simp [rumpfEnde]
          rw [ht] at he
          have hcons : execBlock O passes R
              (.cons (.assignSlot (V := V) t f i e hw hL) b') σ ρ =
              execBlock O passes R b'
                ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
                  (eval (σ.lese Λ (i.orte ++ e.orte)) i
                    (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
                  (eval (σ.lese Λ (i.orte ++ e.orte)) e
                    (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by
            simp only [execBlock, hstep]
          rw [hcons] at hsrc
          have hend : execEnd O passes R
              (.cons (.assignSlot (V := V) (l := l) t f i e hw hL) rest) σ ρ =
              execEnd O passes R rest
                ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
                  (eval (σ.lese Λ (i.orte ++ e.orte)) i
                    (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
                  (eval (σ.lese Λ (i.orte ++ e.orte)) e
                    (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by
            simp only [execEnd, hstep]
          have hle' : sizeOf rest ≤ n := by
            simp only [Endblock.cons.sizeOf_spec] at hle
            omega
          rw [hend]
          exact ih rest b' tail hle' hr he _ _ _ _ hsrc
      | _ =>
        intro hle hb he σ ρ σ' ρ' hsrc
        simp [rumpfBlock] at hb
    | ret e h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.ret e h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.ret e h) =
        some ((.ret e h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | retGrund r h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.retGrund r h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.retGrund r h) =
        some ((.retGrund r h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | leave h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.leave h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.leave h) =
        some ((.leave h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | next h =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.next h) =
        some (Block.nil : Block D V l Γ Λ Λ) := by
        simp [rumpfBlock]
      have ht : rumpfEnde (D := D) (V := V) (.next h) =
        some ((.next h) : Endblock D V l Γ Λ) := by
        simp [rumpfEnde]
      rw [h0] at hb
      rw [ht] at he
      obtain rfl := Option.some.inj hb
      obtain rfl := Option.some.inj he
      simp only [execBlock] at hsrc
      cases hsrc
      rfl
    | bind e rest =>
      intro hle hb he σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V) (.bind e rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiom a args he hw hg hd hgd rest =>
      intro hle hb hee σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiom a args he hw hg hd hgd rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb
    | bindAxiomElse a args he hr hw hg hd hgd err rest =>
      intro hle hb hee σ ρ σ' ρ' hsrc
      have h0 : rumpfBlock (D := D) (V := V)
        (.bindAxiomElse a args he hr hw hg hd hgd err rest) = none := by
        simp [rumpfBlock]
      rw [h0] at hb
      cases hb

/-- BRIDGE: the full body run is the tail run at the world the projected
    prefix reaches. -/
theorem rumpfBruecke (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (body : Endblock D V l Γ Λ) (b : Block D V l Γ Λ Λ)
    (tail : Endblock D V l Γ Λ)
    (hb : rumpfBlock body = some b) (he : rumpfEnde body = some tail)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ)
    (hsrc : execBlock O passes R b σ ρ = .ok σ' ρ') :
    execEnd O passes R body σ ρ = execEnd O passes R tail σ' ρ' :=
  rumpfBruecke_aux O passes R (sizeOf body) body b tail (Nat.le_refl _) hb he
    σ ρ σ' ρ' hsrc

/- CUTS (exactly what is NOT proved here):
    Skeleton only: the projection above, nothing else yet.
-/

#print axioms rumpfBlock
#print axioms rumpfEnde
#print axioms rumpfBlock_total_aux
#print axioms rumpfBlock_total
#print axioms rumpfBruecke_aux
#print axioms rumpfBruecke

/-! ## 3. The per-function unit closing check.

    One decided `Bool` per unit function: the body projects to a pipeline
    block ending in a value return, the pipeline validator accepts the
    candidate bytes, the loaded image and initial world check out, the entry
    sequence and the admitted entry check out, and the entry duty
    (`requires` at the actual arguments) holds. -/

/-- The tail is a value return (the only tail the entry run can execute). -/
def istRueck : Endblock D V l Γ Λ → Bool
  | .ret _ _ => true
  | _ => false

/-- THE UNIT CLOSING CHECK for one function: projection, return tail, the
    pipeline validator, the loaded image, the initial world, the entry
    sequence, the admitted entry, and the entry duty at actual values. -/
def einheitSchluss (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl) : Bool :=
  match rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) with
  | none => false
  | some b =>
    match rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) with
    | none => false
    | some tail =>
      (istRueck tail &&
        (validate c (layoutVon ps) certs b bytes &&
        (imageOk p bild c ps es certs b bytes &&
        (weltOk bild ps σ &&
        (prologImageOk bild c abi (D.params f).length &&
        (eintrittZulassung p bild (effBias bild.modus) art z tore &&
        wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          (P.requires f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ)))))))

/-- CLOSING: every leg jointly closes the check. Each premise is used by
    the rewrite below. -/
theorem einheitSchluss_verbindung (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (tail : Endblock D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (P.rumpf f) = some b)
    (he : rumpfEnde (P.rumpf f) = some tail)
    (hrt : istRueck tail = true)
    (hval : validate c (layoutVon ps) certs b bytes = true)
    (himg : imageOk p bild c ps es certs b bytes = true)
    (hwelt : weltOk bild ps σ = true)
    (hpro : prologImageOk bild c abi (D.params f).length = true)
    (hzul : eintrittZulassung p bild (effBias bild.modus) art z tore = true)
    (hreq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f))
      (P.requires f).orte) (P.requires f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = true) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true := by
  simp [einheitSchluss, hb, he, hrt, hval, himg, hwelt, hpro, hzul, hreq]

/-- A closed check carries its projection and return tail. -/
theorem einheitSchluss_gibt_projektion (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    ∃ (b : Block D (vertragVon D f) false (D.params f)
        (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
      (tail : Endblock D (vertragVon D f) false (D.params f)
        (Signatur.anfang D (D.signatur f))),
      rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b ∧
        rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail ∧
        istRueck tail = true := by
  unfold einheitSchluss at h
  generalize rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = ob at h ⊢
  generalize rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = oe at h ⊢
  cases ob with
  | none =>
    simp at h
  | some b0 =>
    cases oe with
    | none =>
      simp at h
    | some t0 =>
      dsimp only at h
      exact ⟨b0, t0, rfl, rfl, (Bool.and_eq_true_iff.mp h).1⟩

/-- A closed check carries all seven legs (right-nested, so every later
    projection is structural). -/
theorem einheitSchluss_legs (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    ∃ (b : Block D (vertragVon D f) false (D.params f)
        (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
      (tail : Endblock D (vertragVon D f) false (D.params f)
        (Signatur.anfang D (D.signatur f))),
      rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b ∧
      (rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail ∧
      (istRueck tail = true ∧
      (validate c (layoutVon ps) certs b bytes = true ∧
      (imageOk p bild c ps es certs b bytes = true ∧
      (weltOk bild ps σ = true ∧
      (prologImageOk bild c abi (D.params f).length = true ∧
      (eintrittZulassung p bild (effBias bild.modus) art z tore = true ∧
      wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f))
        (P.requires f).orte) (P.requires f)
        (σ.lese (Signatur.anfang D (D.signatur f))
          (P.requires f).orte) ρ) = true))))))) := by
  unfold einheitSchluss at h
  generalize rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = ob at h ⊢
  generalize rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = oe at h ⊢
  cases ob with
  | none =>
    simp at h
  | some b0 =>
    cases oe with
    | none =>
      simp at h
    | some t0 =>
      dsimp only at h
      have hR := (Bool.and_eq_true_iff.mp h).1
      have hr1 := (Bool.and_eq_true_iff.mp h).2
      have hV := (Bool.and_eq_true_iff.mp hr1).1
      have hr2 := (Bool.and_eq_true_iff.mp hr1).2
      have hI := (Bool.and_eq_true_iff.mp hr2).1
      have hr3 := (Bool.and_eq_true_iff.mp hr2).2
      have hW := (Bool.and_eq_true_iff.mp hr3).1
      have hr4 := (Bool.and_eq_true_iff.mp hr3).2
      have hP := (Bool.and_eq_true_iff.mp hr4).1
      have hr5 := (Bool.and_eq_true_iff.mp hr4).2
      have hZ := (Bool.and_eq_true_iff.mp hr5).1
      have hQ := (Bool.and_eq_true_iff.mp hr5).2
      exact ⟨b0, t0, rfl, rfl, hR, hV, hI, hW, hP, hZ, hQ⟩

/-- A closed check carries a validated pipeline block. -/
theorem einheitSchluss_gibt_validate (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    ∃ (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f))),
      validate c (layoutVon ps) certs b bytes = true := by
  obtain ⟨b, tail, hb, he, hR, hV, hI, hW, hP, hZ, hQ⟩ :=
    einheitSchluss_legs P f c ps es certs bytes p bild abi σ ρ art z tore h
  exact ⟨b, hV⟩

/-- A closed check carries an accepted loaded image for its block. -/
theorem einheitSchluss_gibt_imageOk (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    ∃ (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f))),
      imageOk p bild c ps es certs b bytes = true := by
  obtain ⟨b, tail, hb, he, hR, hV, hI, hW, hP, hZ, hQ⟩ :=
    einheitSchluss_legs P f c ps es certs bytes p bild abi σ ρ art z tore h
  exact ⟨b, hI⟩

/-- A closed check carries the initial-world check. -/
theorem einheitSchluss_gibt_weltOk (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    weltOk bild ps σ = true := by
  obtain ⟨b, tail, hb, he, hR, hV, hI, hW, hP, hZ, hQ⟩ :=
    einheitSchluss_legs P f c ps es certs bytes p bild abi σ ρ art z tore h
  exact hW

/-- A closed check carries the entry-sequence check. -/
theorem einheitSchluss_gibt_prolog (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    prologImageOk bild c abi (D.params f).length = true := by
  obtain ⟨b, tail, hb, he, hR, hV, hI, hW, hP, hZ, hQ⟩ :=
    einheitSchluss_legs P f c ps es certs bytes p bild abi σ ρ art z tore h
  exact hP

/-- A closed check carries the admitted entry. -/
theorem einheitSchluss_gibt_zulassung (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    eintrittZulassung p bild (effBias bild.modus) art z tore = true := by
  obtain ⟨b, tail, hb, he, hR, hV, hI, hW, hP, hZ, hQ⟩ :=
    einheitSchluss_legs P f c ps es certs bytes p bild abi σ ρ art z tore h
  exact hZ

/-- A closed check carries the entry duty at the actual arguments. -/
theorem einheitSchluss_gibt_requires (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true) :
    ReqAmEintritt P f
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ := by
  obtain ⟨b, tail, hb, he, hR, hV, hI, hW, hP, hZ, hQ⟩ :=
    einheitSchluss_legs P f c ps es certs bytes p bild abi σ ρ art z tore h
  exact hQ

/-! ## 4. Refusals: every failing leg poisons the check. -/

/-- Without a projection (calls, control, binders, locks) the check
    refuses. -/
theorem einheitSchluss_verweigert_ohne_projektion (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = none) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = false := by
  simp [einheitSchluss, h]

/-- Without a tail (same shapes) the check refuses. -/
theorem einheitSchluss_verweigert_ohne_ende (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b)
    (he : rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = none) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = false := by
  simp [einheitSchluss, hb, he]

/-- Without a value-return tail the check refuses. -/
theorem einheitSchluss_verweigert_ohne_endrueck (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (tail : Endblock D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b)
    (he : rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail)
    (hrt : istRueck tail = false) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = false := by
  simp [einheitSchluss, hb, he, hrt]

/-- Without validator acceptance the check refuses. -/
theorem einheitSchluss_verweigert_ohne_validate (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (tail : Endblock D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b)
    (he : rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail)
    (hval : validate c (layoutVon ps) certs b bytes = false) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = false := by
  simp [einheitSchluss, hb, he, hval]

/-- Without the entry duty the check refuses. -/
theorem einheitSchluss_verweigert_ohne_requires (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (tail : Endblock D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b)
    (he : rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail)
    (hreq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f))
      (P.requires f).orte) (P.requires f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = false) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = false := by
  simp [einheitSchluss, hb, he, hreq]

/-- Without the entry sequence the check refuses. -/
theorem einheitSchluss_verweigert_ohne_prolog (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (tail : Endblock D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b)
    (he : rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail)
    (hpro : prologImageOk bild c abi (D.params f).length = false) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = false := by
  simp [einheitSchluss, hb, he, hpro]

/-- Without the admitted entry the check refuses. -/
theorem einheitSchluss_verweigert_ohne_eintritt (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild) (abi : List Register)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (tail : Endblock D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b)
    (he : rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail)
    (hzul : eintrittZulassung p bild (effBias bild.modus) art z tore = false) :
    einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = false := by
  simp [einheitSchluss, hb, he, hzul]

/-! ## 5. Execution: the closed check runs the loaded image. -/

/-- A return tail is a value return. -/
theorem istRueck_ret (tail : Endblock D V l Γ Λ) (h : istRueck tail = true) :
    ∃ (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende), tail = .ret e hΛ := by
  cases tail with
  | ret e hΛ =>
    exact ⟨e, hΛ, rfl⟩
  | retGrund r hΛ =>
    simp [istRueck] at h
  | leave h =>
    simp [istRueck] at h
  | next h =>
    simp [istRueck] at h
  | cons s rest =>
    simp [istRueck] at h
  | bind e rest =>
    simp [istRueck] at h
  | bindAxiom a args he0 hw hg hd hgd rest =>
    simp [istRueck] at h
  | bindAxiomElse a args he0 hr hw hg hd hgd err rest =>
    simp [istRueck] at h

/-- **UNIT CORRECTNESS FROM AN ADMITTED ENTRY.** From the closed unit
    check and a source run of the body reaching a value return, the
    fetched run from the admitted entry reaches the code end with the
    prefix world and environment represented, stops there with the stack
    word intact, carries the entry duty at the actual arguments, and the
    reached prefix world is exactly where the source tail returns.
    Composes the bridge (`rumpfBruecke`), the totality (`rumpfBlock_total`)
    and the pipeline entry theorem (`pipeline_correct_entry`); nothing is
    re-proved. -/
theorem einheit_correct_entry (P : Programm D) (f : D.Fn)
    (c : PipeCfg) (abi : List Register)
    (ps : List (Platz D)) (es : List TabLayout)
    (certs : List (OptimizationRules.PassKind × OptimizationRules.BlockCert))
    (bytes : List Byte)
    (p : Profil) (bild : Bild)
    (σ : World D) (ρ : Env D (D.params f))
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (reg : Register → Wort) (fl : Flags)
    (hschluss : einheitSchluss P f c ps es certs bytes p bild abi σ ρ art z tore = true)
    (hz : z.zustand = eintrittStart bild c
      (encodeAll (prolog c abi (D.params f).length)).length reg fl)
    (hargs : AbiArgs abi ρ reg)
    (O : Orakel D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
    (σ1 : World D) (v : ErgVal D (D.erg f))
    (hsrc : execEnd O passes R (P.rumpf f) σ ρ = .zurueck σ1 v) :
    ∃ (σ' : World D) (ρ' : Env D (D.params f))
      (tail : Endblock D (vertragVon D f) false (D.params f)
        (Signatur.anfang D (D.signatur f)))
      (n : Nat) (s' : Zustand),
      laufBytes n z.zustand = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧
      EnvRepr ρ' s'.register (abbOf c) ∧
      byteschritt s' = .verweigert ∧
      lesbar8 s'.speicher (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 s'.speicher (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      rumpfEnde (V := vertragVon D f) (l := false) (P.rumpf f) = some tail ∧
      execEnd (V := vertragVon D f) (l := false) O passes R tail σ' ρ' =
        .zurueck σ1 v ∧
      ReqAmEintritt P f
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ := by
  obtain ⟨b, tail, hb, he, hR, hV, hI, hW, hP, hZ, hQ⟩ :=
    einheitSchluss_legs P f c ps es certs bytes p bild abi σ ρ art z tore hschluss
  obtain ⟨σp, ρp, hrun⟩ :=
    rumpfBlock_total (V := vertragVon D f) (l := false) O passes R
      (P.rumpf f) b hb σ ρ
  have hbridge := rumpfBruecke (V := vertragVon D f) (l := false) O passes R
    (P.rumpf f) b tail hb he σ ρ σp ρp hrun
  have htailrun : execEnd (V := vertragVon D f) (l := false) O passes R
      tail σp ρp = .zurueck σ1 v :=
    hbridge.symm.trans hsrc
  obtain ⟨n, s', hrunB, hrip, hW', hE', hstop, hles, hschr⟩ :=
    pipeline_correct_entry p bild c abi ps es certs b bytes hV hI hP σ hW
      art z tore hZ reg fl hz ρ hargs O passes R σp ρp hrun
  have hreq := einheitSchluss_gibt_requires P f c ps es certs bytes p bild abi
    σ ρ art z tore hschluss
  exact ⟨σp, ρp, tail, n, s', hrunB, hrip, hW', hE', hstop, hles, hschr, he,
    htailrun, hreq⟩

/-! ## 6. Call-site duties carried through the accepted producers. -/

/-- A successful direct call carries the entry duty at the actual
    arguments (reused `callSite_vorOk`) and the callee prefix runs clean
    from the call's entry worlds (reused totality). -/
theorem einheit_ruf_req (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {f : D.Fn} {args : Args D Γ Λ (D.params f)}
    {hp : RufPasst D V (D.signatur f) Λ} {hr : D.gruende f = 0}
    {σ : World D} {ρ : Env D Γ} {σ' : World D} {ρ' : Env D Γ}
    (h : execStmt (V := V) O passes (rufAt P O passes fuel)
      (Stmt.call (V := V) (l := l) f args hp hr) σ ρ = .ok σ' ρ')
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b) :
    ReqAmEintritt P f
      ((σ.lese Λ args.orte).lese (Signatur.anfang D (D.signatur f))
        (P.requires f).orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) ∧
    ∃ (σp : World D) (ρp : Env D (D.params f)),
      execBlock (V := vertragVon D f) (l := false) O passes
        (rufAt P O passes fuel) b
        ((σ.lese Λ args.orte).lese (Signatur.anfang D (D.signatur f))
          (P.requires f).orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .ok σp ρp := by
  refine ⟨callSite_vorOk P O passes fuel h, ?_⟩
  obtain ⟨σp, ρp, hrun⟩ := rumpfBlock_total (V := vertragVon D f) (l := false)
    O passes (rufAt P O passes fuel) (P.rumpf f) b hb _ _
  exact ⟨σp, ρp, hrun⟩

/-- A successful returning call carries the return duty at the actual
    result (reused `rufAt_ok_gibt_ens`) and the callee prefix runs clean
    from the entry worlds (reused totality). -/
theorem einheit_ruf_ens (P : Programm D) (O : Orakel D)
    (passes : Nat)
    (fuel : Nat) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (sread : World D)
    (hread : sread = σ.lese (Signatur.anfang D (D.signatur f))
      (P.requires f).orte)
    (hreq : wahr? (eval sread (P.requires f) sread ρ) = true)
    (σ1 : World D) (v : ErgVal D (D.erg f))
    (hbody : execEnd (V := vertragVon D f) O passes (rufAt P O passes fuel)
      (P.rumpf f) sread ρ = EndAusgang.zurueck σ1 v)
    (sret : World D)
    (hret : sret = σ1.lese (vertragVon D f).ende (P.ensures f).orte)
    (sinv : World D)
    (hsinv : sinv = (D.invs.filter (schuldet f)).foldl
      (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) sret)
    (hinv : D.invs.find? (fun i => schuldet f i &&
      !wahr? (eval sinv (P.invariante i) sinv .nil)) = none)
    (σ' : World D)
    (h : rufAt P O passes (fuel + 1) f σ ρ =
      RufAusgang.ok (D := D) (f := f) σ' v)
    (b : Block D (vertragVon D f) false (D.params f)
      (Signatur.anfang D (D.signatur f)) (Signatur.anfang D (D.signatur f)))
    (hb : rumpfBlock (V := vertragVon D f) (l := false) (P.rumpf f) = some b) :
    RufEnsCheck P f sread sret ρ v ∧ σ' = sinv ∧
    ∃ (σp : World D) (ρp : Env D (D.params f)),
      execBlock (V := vertragVon D f) (l := false) O passes
        (rufAt P O passes fuel) b sread ρ = .ok σp ρp := by
  obtain ⟨hens, heq⟩ := rufAt_ok_gibt_ens P O passes fuel f σ ρ sread hread
    hreq σ1 v hbody sret hret sinv hsinv hinv σ' h
  refine ⟨hens, heq, ?_⟩
  obtain ⟨σp, ρp, hrun⟩ := rumpfBlock_total (V := vertragVon D f) (l := false)
    O passes (rufAt P O passes fuel) (P.rumpf f) b hb sread ρ
  exact ⟨σp, ρp, hrun⟩

/-! ## 7. The source-computed unit check: every function lowered or refused.

    Over the generic T3 lowering (`UProg`, `lowerFnAt`, `lowerAllg`): the
    decided per-function verdict is lowering success plus a projected
    pipeline block; the whole-unit check covers every function
    (`List.finRange`, the same coverage `lowerAllg` itself uses). -/

/-- Per-function unit verdict: the T3 lowering succeeds and the body
    projects to a pipeline block. -/
def t3Stand (u : UProg) (f : Fin u.fns.length) : Bool :=
  match lowerFnAt u f with
  | .error _ => false
  | .ok v => (rumpfBlock v.2).isSome

/-- Whole-unit check: every function of the elaborated unit is lowered to
    a pipeline block (or the check refuses). -/
def t3EinheitOk (u : UProg) : Bool :=
  (List.finRange u.fns.length).all (t3Stand u)

/-- The verdict reason, as data. -/
def t3Grund (u : UProg) (f : Fin u.fns.length) : String :=
  match lowerFnAt u f with
  | .error _ => "lowering-failed"
  | .ok v =>
    match rumpfBlock v.2 with
    | some _ => "lowered"
    | none => "body-outside-fragment"

/-- COVERING: an accepted whole-unit check gives every function its
    lowered body and pipeline block. -/
theorem t3Einheit_gedeckt (u : UProg) (f : Fin u.fns.length)
    (h : t3EinheitOk u = true) :
    ∃ (v : EnsTy u f × RumpTy u f)
      (b : Block (declOf u) (vertragVon (declOf u) f) false
        ((declOf u).params f)
        (Signatur.anfang (declOf u) ((declOf u).signatur f))
        (Signatur.anfang (declOf u) ((declOf u).signatur f))),
      lowerFnAt u f = .ok v ∧ rumpfBlock v.2 = some b := by
  have hmem : t3Stand u f = true :=
    List.all_eq_true.mp h f (List.mem_finRange f)
  unfold t3Stand at hmem
  cases hfn : lowerFnAt u f with
  | error e =>
    rw [hfn] at hmem
    change (false = true) at hmem
    cases hmem
  | ok v =>
    rw [hfn] at hmem
    change ((rumpfBlock v.2).isSome = true) at hmem
    cases hr : rumpfBlock v.2 with
    | none =>
      rw [hr] at hmem
      change (false = true) at hmem
      cases hmem
    | some b =>
      exact ⟨v, b, rfl, hr⟩

/-- A refused verdict is either a failed lowering or a body outside the
    fragment, with its reason. -/
theorem t3Stand_verweigert (u : UProg) (f : Fin u.fns.length)
    (h : t3Stand u f = false) :
    (∃ e : String, lowerFnAt u f = .error e ∧
      t3Grund u f = "lowering-failed") ∨
    (∃ v : EnsTy u f × RumpTy u f, lowerFnAt u f = .ok v ∧
      rumpfBlock v.2 = none ∧ t3Grund u f = "body-outside-fragment") := by
  unfold t3Stand at h
  cases hfn : lowerFnAt u f with
  | error e =>
    rw [hfn] at h
    exact Or.inl ⟨e, rfl, by unfold t3Grund; rw [hfn]⟩
  | ok v =>
    rw [hfn] at h
    change ((rumpfBlock v.2).isSome = false) at h
    cases hr : rumpfBlock v.2 with
    | some b =>
      rw [hr] at h
      change (true = false) at h
      cases h
    | none =>
      exact Or.inr ⟨v, rfl, hr, by unfold t3Grund; rw [hfn]; dsimp only; rw [hr]⟩

/-- Decided lists: a refused `all` names its witness. -/
theorem all_verweigert_aux {α : Type _} (l : List α) (p : α → Bool)
    (h : l.all p = false) : ∃ x ∈ l, p x = false := by
  revert h
  induction l with
  | nil =>
    intro h
    simp at h
  | cons y ys ih =>
    intro h
    cases hp : p y with
    | true =>
      have h2 : (p y && ys.all p) = false := h
      rw [hp] at h2
      change (ys.all p) = false at h2
      obtain ⟨x, hx, hfx⟩ := ih h2
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩
    | false =>
      exact ⟨y, List.mem_cons.mpr (Or.inl rfl), hp⟩

/-- A refused whole-unit check names its function. -/
theorem t3Einheit_verweigert (u : UProg) (h : t3EinheitOk u = false) :
    ∃ f : Fin u.fns.length,
      f ∈ List.finRange u.fns.length ∧ t3Stand u f = false := by
  unfold t3EinheitOk at h
  obtain ⟨x, hx, hfx⟩ := all_verweigert_aux _ _ h
  exact ⟨x, hx, hfx⟩

end Gabbro.Grammatik.X86.PipelineUnit
