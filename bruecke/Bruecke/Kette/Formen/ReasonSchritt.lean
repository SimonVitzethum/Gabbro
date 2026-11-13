module
public import Bruecke.Kette.Formen.Reason
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem stmtZiel_reason_G {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {fn : UFn} {ns : BodyNames} {Λ : List (Res (declOf u))}
    {count j : Nat} {x id : String} {v : Var Γ (.why count)}
    {ga : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count}
    {bs : List (String × List Gabbro.Body.Stmt)}
    (hj : paramPos fn.params x = .ok j) (hv : lowVar Γ j (.why count) = .ok v)
    (hid : ns.lookup fn x = some id)
    (hArms : ReasonRelated u C c O passes R fn ns.active Λ count 0 ga bs)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    StmtZiel_G u C c O passes R fn ns.active (.onWhy (.var v) ga) σ ρ s (.onReason (.name id) bs) := by
  let σl := σ.lese Λ (Expr.var (Λ := Λ) v).orte
  have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
  have hi : ns.active[j]? = some id := by simpa only [BodyNames.lookup, hj] using hid
  have hval : Gabbro.Body.eval s (.name id) = some (.reason (caseLabel (ρ.get v).val)) := by
    simp only [Gabbro.Body.eval]
    rw [hL.values j id hi, Nat.zero_add, nthVal_lowVar _ _ _ _ ρ hv]
    rfl
  obtain ⟨b, bb, hG, hB, hBlock⟩ := hArms.select (ρ.get v)
  apply stmtZiel_of_G (blk := b) (σl := σl)
  · change execGrund O passes R ga (ρ.get v) σl ρ = _
    exact hG σl ρ
  · intro ρB
    simp only [Gabbro.Body.step, hval]
    simpa only [Nat.zero_add] using hB ρB s
  · exact hBlock σl ρ s hWl hL

end Gabbro.Bruecke
