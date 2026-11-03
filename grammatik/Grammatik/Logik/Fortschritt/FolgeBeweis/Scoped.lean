module

public import Grammatik.Logik.Fortschritt.FolgeBeweis.Teil1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} (Φ : Folge D)

theorem fR_scopedWert {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg} {R : RueckRessourcen D V Λ}
    {b w : Bool} (hr : r.scopedWert = some (e, R)) (hk : r.fR Φ b w) : (!b || w) = true := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle hr <;> subst r
  · simpa only [GRest.fR, fE] using hk
  · simp only [GRest.fR, fE, fS, Bool.and_eq_true] at hk
    exact hk.1
  · simp only [GRest.fR, fB, fS, Bool.and_eq_true] at hk
    exact hk.1.1

theorem fR_scopedGrund {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} {g : Fin V.gruende} {R : RueckRessourcen D V Λ}
    {b w : Bool} (hr : r.scopedGrund = some (g, R)) (hk : r.fR Φ b w) : (!b || w) = true := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle hr <;> subst r
  · simpa only [GRest.fR, fE] using hk
  · simp only [GRest.fR, fE, fS, Bool.and_eq_true] at hk
    exact hk.1
  · simp only [GRest.fR, fB, fS, Bool.and_eq_true] at hk
    exact hk.1.1

private theorem antwortRestG_fR {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende) (b : Bool)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : c.2.2.2.2.fR Φ b (Φ.vor g)) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.fR Φ b (match a with | .inl _ => Φ.vor g | .inr _ => false) := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a with
  | inl value =>
      cases r with
      | wartet body k =>
          unfold antwortRestG at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            simpa only [GRest.fR] using hc
          · cases ha
      | wartetSonst n err body k =>
          unfold antwortRestG at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            simp only [GRest.fR] at hc ⊢
            exact hc.2
          · cases ha
      | _ =>
          unfold antwortRestG at ha
          change some _ = some c' at ha
          have equal := Option.some.inj ha
          subst c'
          exact hc
  | inr reason =>
      cases r with
      | wartetSonst n err body k =>
          unfold antwortRestG at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            simp only [GRest.fR, fB_alsBlock] at hc ⊢
            exact ⟨hc.1, hc.2.2⟩
          · cases ha
      | _ =>
          unfold antwortRestG at ha
          change none = some c' at ha
          cases ha

/-- Cleanup leaves the log silent for a root and appends exactly one answer
    event for a callee. Both channels demand the predecessor before cleanup. -/
theorem folgeInvG_rufAntwortG {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (hz : FolgeInvG Φ z)
    (hret : (!Φ.ende z.kopf.f || Armiert Φ z.log) = true)
    (ha : rufAntwortG z vor σ a = some z') : FolgeInvG Φ z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      refine ⟨?_, trivial, hz.2.2⟩
      simpa only [GRest.fR] using hret
  | cons c st =>
      have hc := hz.2.1
      simp only [hst, FolgeStapel] at hc
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      have hnew := antwortRestG_fR Φ z.kopf.f a (Φ.ende c.f) c.rest r hc.1 hr
      have hordered : Φ.ende z.kopf.f = true → Armiert Φ z.log = true := by
        intro he
        simpa only [he, Bool.not_true, Bool.false_or] using hret
      cases a <;>
        exact ⟨hnew, hc.2, fun _ he => hordered he, hz.2.2⟩

end Gabbro.Grammatik
