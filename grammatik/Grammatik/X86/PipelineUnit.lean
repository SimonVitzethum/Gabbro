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

end Gabbro.Grammatik.X86.PipelineUnit
