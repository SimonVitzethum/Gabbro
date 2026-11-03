/- Part 2 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T2Basis
import all Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T2Basis
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section SpurK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  (A : D.Lock → Prop) (C : D.Fn → Prop) (hR : RufSG R C)
include hR
/-- Frame results do not see the trace (covered residues of the converse). -/
theorem semK_SG : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ), RestK A C r →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      (semK O passes R r σ ρ).gleich (semK O passes R r σ' ρ)
  | _, _, _, .ende e, hr => by
      intro σ σ' ρ h
      obtain ⟨he, ho⟩ := hr.ende_inv
      exact endErg_SG (endSGK O passes R A C hR e he ho σ σ' ρ h)
  | _, _, _, .dann b k, hr => by
      intro σ σ' ρ h
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hr.dann_inv
      have h1 := blockSGK O passes R A C hR b hb ho σ σ' ρ h
      rw [semK_dann, semK_dann]
      generalize execBlock O passes R b σ ρ = o at h1 ⊢
      generalize execBlock O passes R b σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact semK_SG k hk _ _ _ hs1)
  | _, _, _, .schrumpf k, hr => by
      intro σ σ' ρ h
      exact semK_SG k hr.schrumpf_inv σ σ' ρ.tail h
  | _, _, _, .frei L k, hr => by
      intro σ σ' ρ h
      exact semK_SG k hr.frei_inv (σ.gibt L) (σ'.gibt L) ρ (h.gibt L)
  | _, _, _, .trav .., hr => by cases hr
  | _, _, _, .travRest .., hr => by cases hr
  | _, _, _, .verbrauch .., hr => by cases hr
  | _, _, _, .verbrauchRest .., hr => by cases hr
  | _, _, _, .wieder .., hr => by cases hr
  | _, _, _, .wiederRest .., hr => by cases hr
  | _, _, _, .ewig .., hr => by cases hr
  | _, _, _, .ewigRest .., hr => by cases hr
  | _, _, _, .wartet .., hr => by cases hr
  | _, _, _, .wartetSonst .., hr => by cases hr
  | _, _, _, .abbruch _, _ => fun _ _ _ _ => REnde.gleich_refl _
  | _, _, _, .leer, _ => fun _ _ _ _ => REnde.gleich_refl _
  | _, _, _, .rueckBereit .., _ => fun _ _ _ _ => REnde.gleich_refl _

end SpurK
/-- **The body-running handler does not see the trace** on the callees the
    converse admits, at every depth. -/
theorem rufRumpf_SG (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) :
    ∀ d, RufSG (rufRumpf P O passes d) (TiefK P A d)
  | 0 => fun _ hC => (hC : False).elim
  | d + 1 => by
      intro g hC σ σ' ρ h
      obtain ⟨he, ho⟩ := hC
      have h1 := endSGK O passes (rufRumpf P O passes d) A (TiefK P A d) (rufRumpf_SG P O passes A d)
        (P.rumpf g) he ho σ σ' ρ h
      simp only [rufRumpf]
      generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes d) (P.rumpf g) σ ρ = o
        at h1 ⊢
      generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes d) (P.rumpf g) σ' ρ = o'
        at h1 ⊢
      cases o with
      | zurueck σ1 v1 =>
        cases o' with
        | zurueck σ2 v2 => exact h1
        | leave h' => exact absurd h' (by decide)
        | next h' => exact absurd h' (by decide)
        | _ => exact h1.elim
      | leave h' => exact absurd h' (by decide)
      | next h' => exact absurd h' (by decide)
      | _ =>
        cases o' with
        | zurueck => exact h1.elim
        | leave h' => exact absurd h' (by decide)
        | next h' => exact absurd h' (by decide)
        | _ => trivial

/-! ## 4. Each machine step keeps the frame semantics, with calls -/


end Gabbro.Grammatik
