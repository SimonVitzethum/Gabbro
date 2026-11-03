module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T4

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Completed answers occur only at an empty-stack head. A continuation
    never contains one; pending cleanup is a running state on either stack. -/
def GRest.antwortPosition {V : Vertrag D} (root : Prop) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende _ => True
  | _, _, _, .dann _ k => k.antwortPosition False
  | _, _, _, .schrumpf k => k.antwortPosition False
  | _, _, _, .frei _ k => k.antwortPosition False
  | _, _, _, .trav _ _ _ _ k => k.antwortPosition False
  | _, _, _, .travRest _ _ _ _ k => k.antwortPosition False
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k => k.antwortPosition False
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k => k.antwortPosition False
  | _, _, _, .wieder _ _ _ _ k => k.antwortPosition False
  | _, _, _, .wiederRest _ _ _ _ k => k.antwortPosition False
  | _, _, _, .ewig _ _ _ _ k => k.antwortPosition False
  | _, _, _, .ewigRest _ _ _ _ k => k.antwortPosition False
  | _, _, _, .wartet _ k => k.antwortPosition False
  | _, _, _, .wartetSonst _ _ _ k => k.antwortPosition False
  | _, _, _, .abbruch k => k.antwortPosition False
  | _, _, _, .leer => True
  | _, _, _, .rueckBereit _ k => k.antwortPosition False
  | _, _, _, .zurueckgekehrt _ => root
  | _, _, _, .aufraeumen _ _ => True

private theorem antwortPosition_mono {V : Vertrag D} {p q : Prop} (hpq : p → q)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (h : r.antwortPosition p) : r.antwortPosition q := by
  cases r <;> first | exact h | exact hpq h

def AntwortPositionG (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.antwortPosition (z.stapel = []) ∧
    ∀ c ∈ z.stapel, c.rest.2.2.2.2.antwortPosition False

private theorem antwortRestG_position {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : c.2.2.2.2.antwortPosition False) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.antwortPosition False := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;>
    simp_all [antwortRestG, GRest.antwortPosition]
  all_goals split at ha <;> simp_all [GRest.antwortPosition]

private theorem rufAntwortG_position {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (hz : AntwortPositionG z) (ha : rufAntwortG z vor σ a = some z') : AntwortPositionG z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact ⟨rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      refine ⟨antwortPosition_mono False.elim _ (antwortRestG_position _ _ _ _
        (hz.2 c (by simp [hst])) hr), ?_⟩
      intro F hF
      exact hz.2 F (by simp only [hst, List.mem_cons]; exact Or.inr hF)

set_option maxHeartbeats 4000000 in
/-- The internal protocol never leaves a completed callee on a live stack. -/
theorem antwortPositionG_schritt {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M')
    (h : AntwortPositionG (M.faeden t)) : AntwortPositionG (M'.faeden t) := by
  cases hs with
  | g7 hs =>
      cases hs with
      | rueckAntwort ρ a hhead z ha =>
          simp only [rufUpdateG_self]
          exact rufAntwortG_position h ha
      | _ =>
          simp_all [AntwortPositionG, GRest.antwortPosition, GRest.weiterOpt,
            rufUpdateG_self, antwortPosition_mono]
  | g1 hs | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;>
        simp_all [AntwortPositionG, GRest.antwortPosition, GRest.weiterOpt,
          rufUpdateG_self, antwortPosition_mono]

theorem antwortPositionG_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, AntwortPositionG (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      rw [start_faden]
      exact ⟨trivial, fun _ h => (List.not_mem_nil h).elim⟩
  | schritt N N' u hn hs ih =>
      intro t
      by_cases htu : t = u
      · subst t
        exact antwortPositionG_schritt hs (ih u)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Gabbro.Grammatik
