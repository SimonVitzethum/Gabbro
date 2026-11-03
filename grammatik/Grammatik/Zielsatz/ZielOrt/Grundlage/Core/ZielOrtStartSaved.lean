module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStartScoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Saved answers anywhere in a residue satisfy `good`. Looking through all
    continuations makes this invariant stable under peeling, pushes and pops. -/
def GRest.antwortGut {V : Vertrag D}
    (good : (ErgVal D V.erg ⊕ Fin V.gruende) × World D → Prop) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende _ => True
  | _, _, _, .dann _ k => k.antwortGut good
  | _, _, _, .schrumpf k => k.antwortGut good
  | _, _, _, .frei _ k => k.antwortGut good
  | _, _, _, .trav _ _ _ _ k => k.antwortGut good
  | _, _, _, .travRest _ _ _ _ k => k.antwortGut good
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k => k.antwortGut good
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k => k.antwortGut good
  | _, _, _, .wieder _ _ _ _ k => k.antwortGut good
  | _, _, _, .wiederRest _ _ _ _ k => k.antwortGut good
  | _, _, _, .ewig _ _ _ _ k => k.antwortGut good
  | _, _, _, .ewigRest _ _ _ _ k => k.antwortGut good
  | _, _, _, .wartet _ k => k.antwortGut good
  | _, _, _, .wartetSonst _ _ _ k => k.antwortGut good
  | _, _, _, .abbruch k => k.antwortGut good
  | _, _, _, .rueckBereit _ k => k.antwortGut good
  | _, _, _, .zurueckgekehrt a => good a
  | _, _, _, .aufraeumen a _ => good a
  | _, _, _, .leer => True

private def antwortGut (P : Programm D) (F : RufRahmenG D)
    (a : (ErgVal D (vertragVon D F.f).erg ⊕ Fin (vertragVon D F.f).gruende) × World D) : Prop :=
  match a.1 with
  | .inl v => EnsAmRueck P F.f F.s0 a.2 F.rho v ∧ InvAmRueck P F.f a.2
  | .inr _ => True

private def rahmenAntwortGut (P : Programm D) (F : RufRahmenG D) : Prop :=
  F.rest.2.2.2.2.antwortGut (antwortGut P F)

private def fadenAntwortGut (P : Programm D) (z : RufFadenG D) : Prop :=
  rahmenAntwortGut P z.kopf ∧ ∀ F ∈ z.stapel, rahmenAntwortGut P F

private theorem antwortGut_weiterOpt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (e : Option Ty) (k : GRest D V l Γ Λ')
    (good : (ErgVal D V.erg ⊕ Fin V.gruende) × World D → Prop) :
    (GRest.weiterOpt (Λ := Λ) e k).antwortGut good ↔ k.antwortGut good := by
  cases e <;> exact Iff.rfl

private theorem antwortRestG_gut {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (good : (ErgVal D V.erg ⊕ Fin V.gruende) × World D → Prop)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : c.2.2.2.2.antwortGut good) (ha : antwortRestG g a c = some c') :
    c'.2.2.2.2.antwortGut good := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;>
    simp_all [antwortRestG, GRest.antwortGut]
  all_goals first
    | (subst ha; simp_all [GRest.antwortGut])
    | (obtain ⟨_, ha⟩ := ha; subst ha; simp_all [GRest.antwortGut])
    | (split at ha <;> simp_all [GRest.antwortGut])

private theorem rufAntwortG_gut {P : Programm D} {z z' : RufFadenG D}
    {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (hz : fadenAntwortGut P z) (hg : antwortGut P z.kopf ⟨a, vor⟩)
    (ha : rufAntwortG z vor σ a = some z') : fadenAntwortGut P z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      refine ⟨?_, by simp⟩
      simpa only [rahmenAntwortGut, GRest.antwortGut, antwortGut] using hg
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      refine ⟨?_, ?_⟩
      · have hc := antwortRestG_gut z.kopf.f a (antwortGut P c) c.rest r
          (hz.2 c (by simp [hst])) hr
        simpa only [rahmenAntwortGut, antwortGut] using hc
      · intro F hF
        exact hz.2 F (by simp only [hst, List.mem_cons]; exact Or.inr hF)

set_option maxHeartbeats 4000000 in
private theorem antwortGut_schritt {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M')
    (h : fadenAntwortGut P (M.faeden t)) (hsc : ScopedRueckGutG P M) :
    fadenAntwortGut P (M'.faeden t) := by
  cases hs with
  | g7 hs =>
      cases hs with
      | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hnonempty =>
          dsimp only
          rw [rufUpdateG_self]
          refine ⟨?_, h.2⟩
          subst σ₁
          simpa only [rahmenAntwortGut, GRest.antwortGut, antwortGut] using
            (hsc t _ _ _ ρ r e R hhead hret)
      | rueckScopedGrund ρ r grund R hhead hret hscope hΛ hnonempty =>
          dsimp only
          rw [rufUpdateG_self]
          refine ⟨?_, h.2⟩
          simp only [rahmenAntwortGut, GRest.antwortGut, antwortGut]
      | rueckFreigabe ρ a L remaining hhead hnonempty =>
          dsimp only
          rw [rufUpdateG_self]
          refine ⟨?_, h.2⟩
          have hk := h.1
          change (M.faeden t).kopf.rest.2.2.2.2.antwortGut _ at hk
          rw [hhead] at hk
          simpa only [rahmenAntwortGut, GRest.antwortGut, antwortGut] using hk
      | rueckFreigabeLetzte ρ a L hhead z ha =>
          dsimp only
          rw [rufUpdateG_self]
          apply rufAntwortG_gut h ?_ ha
          have hk := h.1
          change (M.faeden t).kopf.rest.2.2.2.2.antwortGut _ at hk
          rw [hhead] at hk
          simpa only [GRest.antwortGut] using hk
      | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z ha =>
          dsimp only
          rw [rufUpdateG_self]
          apply rufAntwortG_gut h ?_ ha
          subst σ₁
          exact hsc t _ _ _ ρ r e R hhead hret
      | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z ha =>
          dsimp only
          rw [rufUpdateG_self]
          exact rufAntwortG_gut (a := .inr grund) h (by simp only [antwortGut]) ha
      | _ =>
          dsimp only
          rw [rufUpdateG_self]
          simp_all [fadenAntwortGut, rahmenAntwortGut, antwortGut,
            GRest.antwortGut, RufDannHeadG, RufEndHeadG]
  | g1 hs | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;> dsimp only <;> rw [rufUpdateG_self]
      all_goals try
        rcases ‹RufWartetHeadG _ _ _ _› with hc | ⟨n, err, hc⟩
      all_goals
        simp_all [fadenAntwortGut, rahmenAntwortGut, antwortGut, GRest.antwortGut,
          antwortGut_weiterOpt, RufDannHeadG, RufEndHeadG]

/-- Replay supplies the guarantee at the cleanup source; a structural
    invariant carries it with the saved snapshot through all later steps.
    It never compares a released carrier with current shared memory. -/
theorem startScopedEndeG_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    (hsc : ∀ N, RufErreichbarG P O pa (RufStartG P sp init) N → ScopedRueckGutG P N)
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    StartScopedEndeG P M := by
  have hgood : ∀ t, fadenAntwortGut P (M.faeden t) := by
    induction hr with
    | start =>
        intro t
        rw [start_faden]
        simp [fadenAntwortGut, rahmenAntwortGut, GRest.antwortGut]
    | schritt N N' u hn hs ih =>
        intro t
        by_cases htu : t = u
        · subst t
          exact antwortGut_schritt hs (ih u) (hsc N hn)
        · rw [rufSchrittG_fremd hs t htu]
          exact ih t
  intro t _ l Γ ρ v vor hhead
  have h := (hgood t).1
  change (M.faeden t).kopf.rest.2.2.2.2.antwortGut _ at h
  rw [hhead] at h
  simpa only [GRest.antwortGut, antwortGut] using h

end Gabbro.Grammatik
