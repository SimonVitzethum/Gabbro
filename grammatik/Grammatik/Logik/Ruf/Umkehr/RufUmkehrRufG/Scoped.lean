module

public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T3

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Read the return expression before folding the lexical releases. All
    three source-head positions have the same sequential frame result. -/
theorem semK_scopedWert (O : Orakel D) (passes : Nat)
    (Ruf : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg)
    (R : RueckRessourcen D V Λ) (h : r.scopedWert = some (e, R))
    (σ : World D) (ρ : Env D Γ) :
    semK O passes Ruf r σ ρ =
      .zurueck (R.scopes.foldl World.gibt (σ.lese Λ e.orte))
        (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle h <;>
    subst r <;> rfl

/-- The shared answer operation resumes precisely the caller described by
    the converse's existing plain/binding continuation relation. -/
private theorem antwortRestG_wiederauf {g : D.Fn} (caller : RufRahmenG D)
    (v : ErgVal D (D.erg g))
    (rest : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
      Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)
    (h : antwortRestG g (.inl v) caller.rest = some rest) :
    Wiederauf g caller v ⟨caller.f, caller.rho, caller.s0, rest⟩ := by
  obtain ⟨cf, crho, cs0, ⟨l, Γ, Λ, ρ, k⟩⟩ := caller
  cases k <;> simp only [antwortRestG] at h
  all_goals first
    | (cases h; exact Wiederauf.wie rfl)
    | (split at h
       · rename_i he
         simp only [Option.some.injEq] at h
         subst rest
         first
         | exact Wiederauf.bind _ _ _ rfl he
         | exact Wiederauf.bindSonst _ _ _ _ _ rfl he
       · cases h)

/-- Delivery preserves the frame result both for a root (completed residue)
    and for a callee (logged pop). The saved read world is never re-read. -/
private theorem erhaltK_antwort {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {A : D.Lock → Prop} {C : D.Fn → Prop} {M M' : RufMaschineG D} {f : Faden}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ)
    (vor σ : World D) (v : ErgVal D (D.erg (M.faeden f).kopf.f))
    (z : RufFadenG D) (ha : rufAntwortG (M.faeden f) vor σ (.inl v) = some z)
    (hz : M'.faeden f = z) (hm : M'.speicher = σ.speicher)
    (hs : (semK O passes R r (M.weltVon f) ρ).gleich (.zurueck σ v)) :
    ErhaltK P O passes R A C M M' f (M.faeden f) ρ r := by
  unfold ErhaltK
  cases hst : (M.faeden f).stapel with
  | nil =>
    simp only [rufAntwortG, hst, Option.some.injEq] at ha
    subst z
    refine Or.inl ⟨false, _, _, (M.faeden f).kopf.rho,
      .zurueckgekehrt ⟨.inl v, vor⟩, σ.spur, ?_,
      RestK.zurueckgekehrt v vor, ?_⟩
    · simpa only [hst] using hz
    · have hw : M'.weltVon f = σ := by
        unfold RufMaschineG.weltVon
        rw [hm, hz]
        exact Speicher.welt_speicher σ
      rw [hw]
      exact REnde.gleich_symm hs
  | cons caller st =>
    simp only [rufAntwortG, hst] at ha
    cases hr : antwortRestG (M.faeden f).kopf.f (.inl v) caller.rest with
    | none => simp only [hr, Option.bind] at ha; cases ha
    | some rest =>
      simp only [hr, Option.bind, Option.some.injEq] at ha
      subst z
      exact Or.inr (Or.inl ⟨v, σ, caller, _, st, hst,
        antwortRestG_wiederauf caller v rest hr, hz, hm, hs⟩)

/-- Scoped returns retain the normal-answer converse through every cleanup
    step. Reason returns remain outside its syntactic fragment. -/
theorem schrittErhaltK_g7 {P : Programm D} {O : Orakel D} {passes : Nat}
    {Ruf : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {A : D.Lock → Prop} {C : D.Fn → Prop}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG7 P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestK A C r) :
    ErhaltK P O passes Ruf A C M M' f z ρ r := by
  subst hz
  cases hs with
  | dannVerbrauch =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlegeK hhead
  | verbrauchWeiter =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlegeK hhead
  | verbrauchLeer =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlegeK hhead
  | verbrauchFort =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlegeK hhead
  | dannLeaveVerbrauch =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlegeK hhead
  | dannNextVerbrauch =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlegeK hhead
  | rueckScopedWert ρ2 r2 e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hn =>
    have hsem := semK_scopedWert O passes Ruf r2 e R hret (M.weltVon f) ρ2
    rw [hR] at hhead
    cases hhead
    subst hs₁
    unfold ErhaltK
    refine Or.inl ⟨_, _, _, _, .aufraeumen _ R.scopes, _,
      rufUpdateG_self _ _ _, RestK.aufraeumen _ _ _, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq hsem.symm
  | rueckScopedGrund ρ2 r2 grund R hhead hret
  | rueckScopedGrundDirekt ρ2 r2 grund R hhead hret =>
    rcases GRest.scopedGrund_faelle hret with he | ⟨rest, he⟩ | ⟨Λ', rest, k, he⟩ <;>
      subst r2 <;> widerlegeK hhead
  | rueckFreigabe ρ2 a L remaining hhead hn =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨answer, vor⟩ := a
    cases answer with
    | inr grund => cases hcov
    | inl v =>
      unfold ErhaltK
      refine Or.inl ⟨_, _, _, _, .aufraeumen ⟨.inl v, vor⟩ remaining, _,
        rufUpdateG_self _ _ _, RestK.aufraeumen v vor remaining, ?_⟩
      rw [weltVon_upd]
      exact REnde.gleich_of_eq rfl
  | rueckFreigabeLetzte ρ2 a L hhead z' ha =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨answer, vor⟩ := a
    cases answer with
    | inr grund => cases hcov
    | inl v =>
      apply erhaltK_antwort _ _ vor ((M.weltVon f).gibt L) v z' ha
      · exact rufUpdateG_self _ _ _
      · rfl
      · exact REnde.gleich_of_eq rfl
  | rueckScopedWertDirekt ρ2 r2 e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z' ha =>
    have hsem := semK_scopedWert O passes Ruf r2 e R hret (M.weltVon f) ρ2
    rw [hempty] at hsem
    rw [hR] at hhead
    cases hhead
    subst hs₁
    apply erhaltK_antwort _ _ _ _ _ z' ha
    · exact rufUpdateG_self _ _ _
    · rfl
    · exact REnde.gleich_of_eq hsem

/-! Nonempty-cleanup witnesses reuse the adequacy fixture's real lock,
    value result, memory, and suspended caller. -/

def umkehrScopedVor : World adD := adSp0.welt [.nimmt () []]

def umkehrScopedR : RueckRessourcen adD (vertragVon adD adFn) adΛL :=
  ⟨[()], List.Perm.refl _⟩

def umkehrScopedExpr : Expr adD [] adΛL (adD.typ () ()) :=
  .slot () () adIdx adDarf

/-- The source head reads before releasing its nonempty lexical scope. -/
theorem semK_scopedWert_zeuge :
    semK adO 0 keinRuf
      (.ende (l := false) (.retScoped (.val umkehrScopedExpr) umkehrScopedR))
      umkehrScopedVor Env.nil =
      .zurueck ((umkehrScopedVor.lese adΛL umkehrScopedExpr.orte).gibt ())
        (evalErg (umkehrScopedVor.lese adΛL umkehrScopedExpr.orte) (.val umkehrScopedExpr)
          (umkehrScopedVor.lese adΛL umkehrScopedExpr.orte) Env.nil) :=
  semK_scopedWert adO 0 keinRuf _ _ umkehrScopedR rfl _ _

def umkehrScopedWert : ErgVal adD (adD.erg adFn) :=
  ⟨7, by decide, by decide⟩

def umkehrScopedM : RufMaschineG adD :=
  ⟨adSp0, fun _ => ⟨[adCaller],
    ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], _, Env.nil,
      .aufraeumen ⟨.inl umkehrScopedWert, umkehrScopedVor⟩ [()]⟩⟩,
    umkehrScopedVor.spur, []⟩, [], adSp0.welt []⟩

def umkehrScopedNach : RufFadenG adD :=
  ⟨[], adCaller, (umkehrScopedVor.gibt ()).spur,
    [.rueck adFn Env.nil umkehrScopedWert (adSp0.welt []) (umkehrScopedVor.gibt ())]⟩

def umkehrScopedM' : RufMaschineG adD :=
  ⟨adSp0, rufUpdateG umkehrScopedM.faeden 0 umkehrScopedNach,
    [⟨0, .gibt ()⟩], adSp0.welt []⟩

/-- The last release really pops a callee and retains its saved value,
    satisfying the step theorem's coverage and head premises jointly. -/
theorem schrittErhaltK_g7_zeuge :
    RufSchrittG7 adP adO 0 umkehrScopedM 0 umkehrScopedM' ∧
    ErhaltK adP adO 0 keinRuf (fun _ => False) (fun _ => False)
      umkehrScopedM umkehrScopedM' 0 (umkehrScopedM.faeden 0) Env.nil
      (.aufraeumen (l := false) ⟨.inl umkehrScopedWert, umkehrScopedVor⟩ [()]) := by
  have hs : RufSchrittG7 adP adO 0 umkehrScopedM 0 umkehrScopedM' :=
    .rueckFreigabeLetzte umkehrScopedM 0 Env.nil
      ⟨.inl umkehrScopedWert, umkehrScopedVor⟩ () rfl umkehrScopedNach rfl
  exact ⟨hs, schrittErhaltK_g7 hs _ rfl Env.nil _ rfl (RestK.aufraeumen _ _ _)⟩

#print axioms Gabbro.Grammatik.schrittErhaltK_g7
#print axioms Gabbro.Grammatik.semK_scopedWert_zeuge
#print axioms Gabbro.Grammatik.schrittErhaltK_g7_zeuge

end Gabbro.Grammatik
