/- Part 8 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.RufAdaequatG.T7

namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem REnde.gleich_refl {V : Vertrag D} (r : REnde V) : r.gleich r := by
  cases r with
  | zurueck σ v => exact ⟨⟨rfl, rfl⟩, rfl⟩
  | sonst => trivial

theorem REnde.gleich_symm {V : Vertrag D} {r r' : REnde V} (h : r.gleich r') : r'.gleich r := by
  cases r <;> cases r' <;> simp_all [REnde.gleich, SG]

theorem REnde.gleich_trans {V : Vertrag D} {r r' r'' : REnde V} (h1 : r.gleich r')
    (h2 : r'.gleich r'') : r.gleich r'' := by
  cases r <;> cases r' <;> cases r'' <;> simp_all [REnde.gleich, SG]

section Sem

variable (O : Orakel D) (passes : Nat) {V : Vertrag D}

def endErg {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → REnde V
  | .zurueck σ v => .zurueck σ v
  | _ => .sonst

def semR : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → World D →
    Env D Γ → REnde V
  | _, _, _, .ende e, σ, ρ => endErg (execEnd O passes keinRuf e σ ρ)
  | _, _, _, .dann b k, σ, ρ =>
      match execBlock O passes keinRuf b σ ρ with
      | .ok σ' ρ' => semR k σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | _ => .sonst
  | _, _, _, .schrumpf k, σ, ρ => semR k σ ρ.tail
  | _, _, _, .frei L k, σ, ρ => semR k (σ.gibt L) ρ
  | _, _, _, .trav .., _, _ => .sonst
  | _, _, _, .travRest .., _, _ => .sonst
  | _, _, _, .wieder .., _, _ => .sonst
  | _, _, _, .wiederRest .., _, _ => .sonst
  | _, _, _, .ewig .., _, _ => .sonst
  | _, _, _, .ewigRest .., _, _ => .sonst
  | _, _, _, .wartet .., _, _ => .sonst
  | _, _, _, .wartetSonst .., _, _ => .sonst
  | _, _, _, .abbruch .., _, _ => .sonst

/-- Continue with `k` after an outcome. -/
def nachA {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (o : Ausgang V l Γ)
    (k : GRest D V l Γ Λ) : REnde V :=
  match o with
  | .ok σ ρ => semR O passes k σ ρ
  | .zurueck σ v => .zurueck σ v
  | _ => .sonst

variable {l : Bool} {Γ : Ctx}

theorem semR_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann b k) σ ρ = nachA O passes (execBlock O passes keinRuf b σ ρ) k := by
  simp only [semR, nachA]

theorem nachA_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    nachA O passes (execBlock O passes keinRuf (.cons s rest) σ ρ) k =
      nachA O passes (execStmt O passes keinRuf s σ ρ) (.dann rest k) := by
  simp only [execBlock]
  generalize execStmt O passes keinRuf s σ ρ = o
  cases o <;> simp only [nachA, semR_dann]

theorem nachA_schrumpf {τ : Ty} {Λ : List (Res D)} (o : Ausgang V l (τ :: Γ))
    (k : GRest D V l Γ Λ) :
    nachA O passes o.schrumpf k = nachA O passes o (.schrumpf k) := by
  cases o <;> simp only [Ausgang.schrumpf, nachA, semR]

theorem nachA_schrumpfArm (c : Option (Int × Int)) {Λ : List (Res D)}
    (o : Ausgang V l (ArmCtx Γ c)) (k : GRest D V l Γ Λ) :
    nachA O passes (o.schrumpfArm c) k =
      (match c, o with
       | none, o => nachA O passes o k
       | some (_, _), o => nachA O passes o (.schrumpf k)) := by
  cases c with
  | none => rfl
  | some p => exact nachA_schrumpf O passes o k

theorem nachA_zuAusgang {Λ : List (Res D)} (o : EndAusgang V l Γ) (k : GRest D V l Γ Λ) :
    nachA O passes o.zuAusgang k = endErg o := by
  cases o <;> rfl

theorem endErg_schrumpf {τ : Ty} (o : EndAusgang V l (τ :: Γ)) : endErg o.schrumpf = endErg o := by
  cases o <;> rfl

theorem endErg_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    endErg (execEnd O passes keinRuf (.cons s rest) σ ρ) =
      nachA O passes (execStmt O passes keinRuf s σ ρ) (.dann .nil (.ende rest)) := by
  simp only [execEnd]
  generalize execStmt O passes keinRuf s σ ρ = o
  cases o <;> simp only [endErg, nachA, semR, execBlock]

/-- The `locks` release: a return inside the body loses the final `gibt`
    (the machine pops without it), which only the trace sees. -/
theorem nachA_frei {Λ : List (Res D)} (o : Ausgang V l Γ) (L : D.Lock)
    (k : GRest D V l Γ Λ) :
    (nachA O passes o (.frei L k)).gleich (nachA O passes (o.mapWelt (·.gibt L)) k) := by
  cases o with
  | ok σ ρ => exact REnde.gleich_refl _
  | zurueck σ v => exact ⟨⟨rfl, rfl⟩, rfl⟩
  | _ => trivial

theorem endErg_SG {o o' : EndAusgang V l Γ} (h : EndSG o o') :
    (endErg o).gleich (endErg o') := by
  cases o <;> cases o' <;> simp_all [EndSG, endErg, REnde.gleich]

end Sem
/-- The residues the converse follows: covered, oracle-free blocks in
    `dann` position, covered end blocks, `schrumpf` and `frei` layers. -/
inductive RestG {V : Vertrag D} (A : D.Lock → Prop) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop where
  | ende {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ)
      (he : EndG A e) (ho : e.ohneOrakel = true) : RestG A (.ende e)
  | dann {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
      (k : GRest D V l Γ Λ') (hb : BlockG A mr b) (ho : b.ohneOrakel = true)
      (hk : RestG A k) : RestG A (.dann b k)
  | schrumpf {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ)
      (hk : RestG A k) : RestG A (.schrumpf (τ := τ) k)
  | frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ)
      (hk : RestG A k) : RestG A (.frei L k)
  | abbruch {l : Bool} {Γ : Ctx} {Λ Λk : List (Res D)} (k : GRest D V l Γ Λk)
      (hk : RestG A k) : RestG A (.abbruch (Λ := Λ) k)

section RestInv

variable {V : Vertrag D} {A : D.Lock → Prop} {l : Bool} {Γ : Ctx}

theorem RestG.ende_inv {Λ : List (Res D)} {e : Endblock D V l Γ Λ}
    (h : RestG A (.ende e)) : EndG A e ∧ e.ohneOrakel = true := by
  cases h with
  | ende _ he ho => exact ⟨he, ho⟩

theorem RestG.dann_inv {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'}
    {k : GRest D V l Γ Λ'} (h : RestG A (.dann b k)) :
    (∃ mr, BlockG A mr b) ∧ b.ohneOrakel = true ∧ RestG A k := by
  cases h with
  | dann _ _ hb ho hk => exact ⟨⟨_, hb⟩, ho, hk⟩

theorem RestG.schrumpf_inv {Λ : List (Res D)} {τ : Ty} {k : GRest D V l Γ Λ}
    (h : RestG A (.schrumpf (τ := τ) k)) : RestG A k := by
  cases h with
  | schrumpf _ hk => exact hk

theorem RestG.frei_inv {Λ : List (Res D)} {L : D.Lock} {k : GRest D V l Γ Λ}
    (h : RestG A (.frei L k)) : RestG A k := by
  cases h with
  | frei _ _ hk => exact hk

/-- The head statement of a covered `dann` block is a covered form. -/
theorem RestG.dann_cons_art {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : RestG A (.dann (.cons s rest) k)) : s.gArt = true := by
  obtain ⟨⟨_, hb⟩, _, _⟩ := h.dann_inv
  exact hb.cons_inv.1.art

theorem RestG.ende_cons_art {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : RestG A (.ende (.cons s rest))) : s.gArt = true := by
  obtain ⟨he, _⟩ := h.ende_inv
  exact he.cons_inv.1.art

end RestInv
/-- Frame results do not see the trace (covered, oracle-free residues). -/
theorem semR_SG (O : Orakel D) (passes : Nat) {V : Vertrag D} (A : D.Lock → Prop) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ), RestG A r →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      (semR O passes r σ ρ).gleich (semR O passes r σ' ρ)
  | _, _, _, .ende e, hr => by
      intro σ σ' ρ h
      obtain ⟨he, ho⟩ := hr.ende_inv
      exact endErg_SG (endSG O passes A e he ho σ σ' ρ h)
  | _, _, _, .dann b k, hr => by
      intro σ σ' ρ h
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hr.dann_inv
      have h1 := blockSG O passes A b hb ho σ σ' ρ h
      rw [semR_dann, semR_dann]
      generalize execBlock O passes keinRuf b σ ρ = o at h1 ⊢
      generalize execBlock O passes keinRuf b σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact semR_SG O passes A k hk _ _ _ hs1)
  | _, _, _, .schrumpf k, hr => by
      intro σ σ' ρ h
      exact semR_SG O passes A k hr.schrumpf_inv σ σ' ρ.tail h
  | _, _, _, .frei L k, hr => by
      intro σ σ' ρ h
      exact semR_SG O passes A k hr.frei_inv (σ.gibt L) (σ'.gibt L) ρ (h.gibt L)
  | _, _, _, .trav .., hr => by cases hr
  | _, _, _, .travRest .., hr => by cases hr
  | _, _, _, .wieder .., hr => by cases hr
  | _, _, _, .wiederRest .., hr => by cases hr
  | _, _, _, .ewig .., hr => by cases hr
  | _, _, _, .ewigRest .., hr => by cases hr
  | _, _, _, .wartet .., hr => by cases hr
  | _, _, _, .wartetSonst .., hr => by cases hr
  | _, _, _, .abbruch _, _ => fun _ _ _ _ => REnde.gleich_refl _

theorem REnde.gleich_of_eq {V : Vertrag D} {r r' : REnde V} (h : r = r') : r.gleich r' := by
  rw [h]
  exact REnde.gleich_refl r'

/-! ## 16. Each machine step keeps the frame semantics -/


end Gabbro.Grammatik
