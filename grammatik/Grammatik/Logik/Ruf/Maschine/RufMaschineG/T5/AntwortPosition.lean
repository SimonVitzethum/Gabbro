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
  | _, _, _, .aufraeumen _ remaining => remaining ≠ []

private theorem antwortPosition_mono {V : Vertrag D} {p q : Prop} (hpq : p → q)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (h : r.antwortPosition p) : r.antwortPosition q := by
  cases r <;> first | exact h | exact hpq h

/-- The position predicate on a whole sigma residue; folding the projections keeps
    the residue a non-dependent argument, so `hhead` rewrites it. -/
def RestPos {V : Vertrag D} (root : Prop)
    (x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) : Prop :=
  x.2.2.2.2.antwortPosition root

def AntwortPositionG (z : RufFadenG D) : Prop :=
  RestPos (z.stapel = []) z.kopf.rest ∧ ∀ c ∈ z.stapel, RestPos False c.rest

/-- A waiting caller's continuation is in answer position when the caller's residue is. -/
private theorem wartet_position {caller : RufRahmenG D}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    {restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ'}
    {k : GRest D (vertragVon D caller.f) l Γ Λ'} {ρ : Env D Γ}
    (hc : RufWartetHeadG caller restb k ρ) (h : RestPos False caller.rest) :
    k.antwortPosition False := by
  unfold RestPos at h
  rcases hc with hc | ⟨n, err, hc⟩
  · rw [hc] at h
    exact h
  · rw [hc] at h
    exact h

/-- The continuation behind a generalized foreign binder keeps the answer position. -/
private theorem weiterOpt_position {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ' : List (Res D)}
    (e : Option Ty) (k : GRest D V l Γ Λ') (h : k.antwortPosition False) :
    (GRest.weiterOpt (Λ := Λ') e k).antwortPosition False := by
  cases e with
  | none => exact h
  | some τ => simpa [GRest.weiterOpt, GRest.antwortPosition] using h

private theorem antwortRestG_position {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : c.2.2.2.2.antwortPosition False) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.antwortPosition False := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;>
    simp_all [antwortRestG, GRest.antwortPosition]
  all_goals first
    | (subst ha; simp_all [GRest.antwortPosition])
    | (obtain ⟨_, ha⟩ := ha; subst ha; simp_all [GRest.antwortPosition])
    | (split at ha <;> simp_all [GRest.antwortPosition])

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
      | rueckFreigabeLetzte _ _ _ _ z ha
      | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z ha
      | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z ha =>
          simp only [rufUpdateG_self]
          exact rufAntwortG_position h ha
      | _ =>
          try simp only [rufUpdateG_self]
          simp only [AntwortPositionG] at h ⊢
          try simp_all
          all_goals (try simp only [RestPos, GRest.antwortPosition])
          all_goals first
            | (apply weiterOpt_position; simpa [RestPos, GRest.antwortPosition] using h.1)
            | simpa [RestPos, GRest.antwortPosition] using h.1
            | (refine antwortPosition_mono False.elim _ ?_; simpa [RestPos, GRest.antwortPosition] using h.1)
            | simpa [RestPos, GRest.antwortPosition] using h.2.1
            | (refine antwortPosition_mono False.elim _ ?_; simpa [RestPos, GRest.antwortPosition] using h.2.1)
            | (refine antwortPosition_mono False.elim _ ?_; refine h.2 _ ?_; simp_all)
            | (simp_all [RestPos, GRest.antwortPosition]; done)
            | (split <;> simpa [RestPos, GRest.antwortPosition] using h.1)
            | (split <;> simp_all [RestPos, GRest.antwortPosition]; done)
            | (apply wartet_position (h := h.2.1); assumption)
            | (apply wartet_position (h := h.1); assumption)
            | (rcases ‹Option Ty› with _ | τ <;> simpa [RestPos, GRest.antwortPosition] using h.1)
            | skip
  | g1 hs | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;>
        (try simp only [rufUpdateG_self]) <;>
        (simp only [AntwortPositionG] at h ⊢) <;>
        (try simp_all)
      all_goals (try simp only [RestPos, GRest.antwortPosition])
      all_goals first
        | (apply weiterOpt_position; simpa [RestPos, GRest.antwortPosition] using h.1)
        | simpa [RestPos, GRest.antwortPosition] using h.1
        | (refine antwortPosition_mono False.elim _ ?_; simpa [RestPos, GRest.antwortPosition] using h.1)
        | simpa [RestPos, GRest.antwortPosition] using h.2.1
        | (refine antwortPosition_mono False.elim _ ?_; simpa [RestPos, GRest.antwortPosition] using h.2.1)
        | (refine antwortPosition_mono False.elim _ ?_; refine h.2 _ ?_; simp_all)
        | (simp_all [RestPos, GRest.antwortPosition]; done)
        | (split <;> simpa [RestPos, GRest.antwortPosition] using h.1)
        | (split <;> simp_all [RestPos, GRest.antwortPosition]; done)
        | (apply wartet_position (h := h.2.1); assumption)
        | (apply wartet_position (h := h.1); assumption)
        | (rcases ‹Option Ty› with _ | τ <;> simpa [RestPos, GRest.antwortPosition] using h.1)
        | skip

theorem antwortPositionG_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, AntwortPositionG (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      unfold AntwortPositionG
      dsimp only [RufStartG]
      cases init t with
      | mk g rho => exact ⟨trivial, fun _ h => (List.not_mem_nil h).elim⟩
  | schritt N N' u hn hs ih =>
      intro t
      by_cases htu : t = u
      · subst t
        exact antwortPositionG_schritt hs (ih u)
      · rw [rufSchrittG_passt_anders P O pa N N' u t htu hs]
        exact ih t

end Gabbro.Grammatik
