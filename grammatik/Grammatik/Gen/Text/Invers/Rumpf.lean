/-
  File:      Grammatik/Gen/Text/Invers/Rumpf.lean
  Subject:   THE BODY READ BACK (Tier 2.1, step 2): for every statement, block and end block of the fragment of
             `uOfSt`/`uOfBl`/`uOfEnd`, in every context `SInv` describes, the elaborator's run reader `uAnwReihe`
             (with fuel above the term's size) builds exactly the plain statements `uOf*` computes from the model
             term, and `uEnde` the trailing return; the fragment keeps the held resources (`Λ' = Λ`).
-/
module
public import Grammatik.Gen.Text.Invers.Geraet
public import Grammatik.Gen.Text.Invers.Rumpf_satzFaelle.Teil3
@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
variable {z : Spez} {V : Vertrag z.deklaration} (gNr : Nat → Nat) (tabs : List UTab) (koepfe : List UFnKopf)

theorem rumpf_satz (hM : ∀ m : z.deklaration.Marke, False) (hK : KInv (z := z) gNr koepfe)
    (hI : KIdx (z := z) koepfe) (n : Nat) :
    RumpfSatz (z := z) (V := V) gNr tabs koepfe n := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by omega, fun _ _ _ _ _ _ h => by omega, fun _ _ _ _ _ _ _ _ h => by omega⟩
  | succ n ih =>
  obtain ⟨ihS, ihB, ihE⟩ := ih
  refine ⟨?_, ?_, ?_⟩
  · apply rumpf_satz_stmt <;> assumption
  · apply rumpf_satz_block <;> assumption
  · apply rumpf_satz_ende <;> assumption

end Gabbro.Grammatik.Gen.Text
