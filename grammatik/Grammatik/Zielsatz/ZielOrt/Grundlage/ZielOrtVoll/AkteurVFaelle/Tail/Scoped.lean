module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The checked footprint of the selected scoped-return expression. -/
private theorem scopedWert_orteV {P : Programm D} {S0 : List (D.Tab ⊕ D.Glob)}
    {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg} {R : RueckRessourcen D V Λ}
    (hok : r.okV P S0) (hret : r.scopedWert = some (e, R)) : e.orte ⊆ S0 := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle hret <;> subst r
  · simpa only [endblockOrteP] using hok.2
  · simpa only [stmtOrteP] using (okV_ende_cons hok).2.1
  · simpa only [stmtOrteP] using (okV_dann_cons hok).2.1

/-- Saving the answer preserves the source prediction, including its lexical cleanup. -/
private theorem scopedWert_semV (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg)
    (R : RueckRessourcen D V Λ) (hret : r.scopedWert = some (e, R))
    (σ saved : World D) (ρ : Env D Γ) :
    (semV O passes calls r σ ρ).gleich
      (semV O passes calls (.aufraeumen (l := l) ⟨.inl (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ), saved⟩ R.scopes) (σ.lese Λ e.orte) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle hret <;> subst r
  · simp only [semV, weiterZ, execEnd]
    exact ZErg.gleich_refl _
  · simp only [execEnd, execStmt, semV, weiterZ, laufA, zErg, weiterZ_grund]
    exact ZErg.gleich_refl _
  · rw [semV_dann_cons]
    simp only [execStmt, semV, weiterZ, laufA, zErg, weiterZ_grund]
    exact weiterZ_zurueck O passes calls k _ _

/-- Saving the answer preserves the source prediction, including its lexical cleanup. -/
private theorem scopedGrund_semV (O : Orakel D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende)
    (R : RueckRessourcen D V Λ) (hret : r.scopedGrund = some (grund, R))
    (σ saved : World D) (ρ : Env D Γ) :
    (semV O passes calls r σ ρ).gleich
      (semV O passes calls (.aufraeumen (l := l) ⟨.inr grund, saved⟩ R.scopes) (σ) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle hret <;> subst r
  · simp only [semV, weiterZ, execEnd]
    exact ZErg.gleich_refl _
  · simp only [execEnd, execStmt, semV, weiterZ, laufA, zErg, weiterZ_grund]
    exact ZErg.gleich_refl _
  · rw [semV_dann_cons]
    simp only [execStmt, semV, weiterZ, laufA, zErg, weiterZ_grund]
    exact ZErg.gleich_refl _

section Replay
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- Save a scoped answer before any lock is released; empty cleanup is allowed here. -/
theorem fadenV_scopedWert {z : RufFadenG D} {W : World D}
    (hF : FadenV P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (R : RueckRessourcen D (vertragVon D z.kopf.f) Λ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedWert = some (e, R)) (spur' : List (Ereignis D)) :
    FadenV P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen ⟨.inl (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ), W.lese Λ e.orte⟩ R.scopes⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
    refine fadenV_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
    have he := scopedWert_orteV hok hret
    have hv := evalErg_gleichAuf e (fun _ h => he h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, ?_, trivial, ?_⟩
    · exact hg
    · intro calls O'
      have heq := scopedWert_semV O' passes calls r e R hret σ (W.lese Λ e.orte) ρ
      rw [hv] at heq
      exact ZErg.folgt_of_gleich heq

/-- Save a scoped answer before any lock is released; empty cleanup is allowed here. -/
theorem fadenV_scopedGrund {z : RufFadenG D} {W : World D}
    (hF : FadenV P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (grund : Fin (vertragVon D z.kopf.f).gruende)
    (R : RueckRessourcen D (vertragVon D z.kopf.f) Λ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedGrund = some (grund, R)) (spur' : List (Ereignis D)) :
    FadenV P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen ⟨.inr grund, W⟩ R.scopes⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
    refine fadenV_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
    refine ⟨σ, Nat.le_refl _, ?_, trivial, ?_⟩
    · exact hg
    · intro calls O'
      have heq := scopedGrund_semV O' passes calls r grund R hret σ W ρ
      exact ZErg.folgt_of_gleich heq

/-- Release one scope and retain the already evaluated answer. -/
theorem fadenV_scopedFreigabe
    {z : RufFadenG D} {W : World D} (hF : FadenV P O passes z W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende) × World D)
    (L : D.Lock) (remaining : List D.Lock)
    (hr : z.kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a (L :: remaining)⟩)
    (spur' : List (Ereignis D)) :
    FadenV P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen a remaining⟩⟩, spur', z.log⟩ (W.speicher.welt spur') := by
  refine fadenV_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
  refine ⟨σ.gibt L, Nat.le_succ _, hg, trivial, ?_⟩
  intro calls O'
  apply ZErg.folgt_of_eq
  rfl

/-- A saved value at completed cleanup still satisfies the function contract. -/
private theorem kopfV_scopedEns (hO : GutO O)
    (hK : ∀ f, KoerperGutV P passes f)
    {F : RufRahmenG D} {W : World D} (hF : KopfV P O passes F W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ) (v : ErgVal D (vertragVon D F.f).erg) (vor : World D)
    (hr : F.rest = ⟨l, Γ, _, ρ, .aufraeumen ⟨.inl v, vor⟩ []⟩) :
    EnsAmRueck P F.f F.s0 W F.rho v := by
  obtain ⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩ := hF
  have h1 := heq (rufAusV H) (orakelAus O HA) (rufAusV_passt hf) (orakelAus_passt O hfa) rfl
  rw [hr] at h1
  simp only [semV, weiterZ, List.foldl_nil] at h1
  obtain ⟨σ', hex, hsg⟩ := zErg_gleich_zurueck (ZErg.folgt_zurueck h1)
  have hens := (hK F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (rufAusV H)
    (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) F.s0 F.rho hreq).1 σ' v hex
  exact ens_transfer hens (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P F.f h) ((gleichAuf_SG hsg).trans hg))

/-- Deliver a completed cleanup through the canonical root/callee answer operation. -/
theorem fadenV_scopedAntwort (hO : GutO O)
    (hK : ∀ f, KoerperGutV P passes f)
    (e0 : Ereignis D)
    {z z' : RufFadenG D} {W : World D} (hF : FadenV P O passes z W) (hL : LogOk P z.log)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende) × World D)
    (hr : z.kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a []⟩)
    (hantwort : rufAntwortG z a.2 W a.1 = some z') :
    FadenV P O passes z' (W.speicher.welt z'.spur) ∧ LogOk P z'.log := by
  cases hs : z.stapel with
  | nil =>
    simp only [rufAntwortG, hs, Option.some.injEq] at hantwort
    subst z'
    refine ⟨?_, hL⟩
    have hroot := fadenV_lokal hF hr z.kopf.rho (.zurueckgekehrt (l := false) ⟨a.1, a.2⟩) W.spur
      (fun σ hg hok => by
        refine ⟨σ, Nat.le_refl _, hg, trivial, ?_⟩
        intro calls O'
        apply ZErg.folgt_of_eq
        simp only [semV, weiterZ, List.foldl_nil])
    have hw : W.speicher.welt W.spur = W := Speicher.welt_speicher W
    simpa only [hs, hw] using hroot
  | cons caller rst =>
    have hSt := hF.2
    rw [hs] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt

    rcases a with ⟨av, vor⟩
    cases av with
    | inl v =>
      have hens := kopfV_scopedEns hO hK hF.1 ρ v vor hr
      cases ha : antwortRestG z.kopf.f (.inl v) caller.rest with
      | none => simp [rufAntwortG, hs, ha] at hantwort
      | some resp =>
        simp [rufAntwortG, hs, ha] at hantwort
        subst hantwort
        refine ⟨⟨?_, hSt'⟩, logOk_rueck hL hens⟩
        rcases caller with ⟨cf, crho, cs0, lc, Γc, Λc, ρc, rc⟩
        cases rc <;> simp only [antwortRestG] at ha
        all_goals first
          | (cases ha
             apply popV_kopf e0 hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
               _ _ id
               (fun calls O' σa X h => h.1 rfl) _ ⟨rfl, rfl⟩)
          | (split at ha <;> (try contradiction)
             rename_i he
             cases ha
             apply popV_kopf e0 hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
               _ _ id
               (fun calls O' σa X h => h.2 _ _ _ _ _ _ _ _ (Or.inl rfl) he) _ ⟨rfl, rfl⟩)
          | (split at ha <;> (try contradiction)
             rename_i he
             cases ha
             apply popV_kopf e0 hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
               _ _ (fun hok => ⟨hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2⟩)
               (fun calls O' σa X h => h.2 _ _ _ _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩) he) _ ⟨rfl, rfl⟩)
    | inr grund =>
      cases ha : antwortRestG z.kopf.f (.inr grund) caller.rest with
      | none => simp [rufAntwortG, hs, ha] at hantwort
      | some resp =>
        simp [rufAntwortG, hs, ha] at hantwort
        subst hantwort
        refine ⟨⟨?_, hSt'⟩, logOk_grund hL⟩
        rcases caller with ⟨cf, crho, cs0, lc, Γc, Λc, ρc, rc⟩
        cases rc <;> simp only [antwortRestG] at ha
        all_goals try contradiction
        all_goals
          split at ha <;> (try contradiction)
          rename_i hn
          cases ha
          apply popV_kopf e0 hWc W (fun σa => .why σa grund) (Or.inr ⟨grund, fun _ => rfl⟩)
            _ _
            (fun hok => by
              apply okV_alsBlock _ _ _ hok.1 hok.2.1 hok.2.2.2.2
              intro L
              exact Block.held_iff (by assumption) L)
            (fun calls O' σa X h => h _ _ _ _ _ _ _ _ _ _ rfl hn) _ ⟨rfl, rfl⟩

end Replay

end Gabbro.Grammatik
