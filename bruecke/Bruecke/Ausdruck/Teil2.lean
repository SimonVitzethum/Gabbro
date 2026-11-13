module
public import Bruecke.Ausdruck.Records
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem lowSideVal_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {sd : USide} {ls : LowSide u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowSideVal u Γ Λ fn sd = .ok ls) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  unfold lowSideVal at h
  split at h
  · cases h
  · cases hw : lowWertE u Γ Λ fn none sd with
    | error e => simp [lowSideEns, zahlVon, hw] at h
    | ok wv =>
      have hv := lowWertE_rec_sim (er := none) hw hb hA hT σ₀ σ ρ w β hW hL
      have hz : zahlVon (.ok wv) = .ok ls := by simpa only [lowSideEns, hw] using h
      have same := zahlVon_ok hz
      rw [same] at hv
      exact hv

/-- A value fitted into a target range (`lowWertAt`) keeps its number. -/
theorem lowWertAt_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {lo hi : Int}
    {sd : USide} {e : Expr (declOf u) Γ Λ (.int lo hi)} {eB : Gabbro.Body.Expr}
    (h : lowWertAt u Γ Λ fn lo hi sd = .ok e) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int lo hi) (eval σ₀ e σ ρ)) := by
  unfold lowWertAt at h
  split at h
  · cases h
  · rename_i ls hls
    split at h
    · split at h
      · cases h
        rw [lowSideVal_sim hls hb hA hT σ₀ σ ρ w β hW hL]
        rfl
      · cases h
    · cases h

end Gabbro.Bruecke
