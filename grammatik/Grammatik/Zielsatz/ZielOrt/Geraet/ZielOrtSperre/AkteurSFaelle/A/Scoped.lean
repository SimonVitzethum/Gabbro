module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The checked footprint of the selected scoped-return expression. -/
private theorem scopedWert_orteS {P : Programm D} {S0 S1 : List (D.Tab ⊕ D.Glob)}
    {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg} {R : RueckRessourcen D V Λ}
    (hok : r.okS P S0 S1) (hret : r.scopedWert = some (e, R)) : e.orte ⊆ S0 := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle hret <;> subst r
  · simpa only [endblockOrteP] using hok.2
  · simpa only [stmtOrteP] using (okS_ende_cons hok).2.1
  · simpa only [stmtOrteP] using (okS_dann_cons hok).2.1

/-- Saving the answer preserves the source prediction, including its lexical cleanup. -/
private theorem scopedWert_semS (O : Orakel D) (S : SperrInv D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg)
    (R : RueckRessourcen D V Λ) (hret : r.scopedWert = some (e, R))
    (σ saved : World D) (ρ : Env D Γ) :
    (semH S O U passes calls r σ ρ).gleich
      (semH S O U passes calls (.aufraeumen (l := l) ⟨.inl (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ), saved⟩ R.scopes) (σ.lese Λ e.orte) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle hret <;> subst r
  · cases hc : scopesInvH S R.scopes (σ.lese Λ e.orte) <;>
      simp only [semH, weiterH, execEndH, hc, Bool.false_eq_true, if_false, if_true, laufA, zErgG, weiterH_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (σ.lese Λ e.orte) <;> rw [semH_ende_cons]
    all_goals simp only [execEndH, execStmtH, hc, Bool.false_eq_true, if_false, if_true, semH, weiterH, laufA, zErgG, weiterH_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (σ.lese Λ e.orte) <;> rw [semH_dann_cons]
    all_goals simp only [execStmtH, hc, Bool.false_eq_true, if_false, if_true, semH, weiterH, laufA, zErgG, weiterH_logik]
    all_goals first | exact ZErgG.gleich_refl _ | exact weiterH_zurueck S O U passes calls k _ _

/-- Saving the answer preserves the source prediction, including its lexical cleanup. -/
private theorem scopedGrund_semS (O : Orakel D) (S : SperrInv D) (U : Umwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende)
    (R : RueckRessourcen D V Λ) (hret : r.scopedGrund = some (grund, R))
    (σ saved : World D) (ρ : Env D Γ) :
    (semH S O U passes calls r σ ρ).gleich
      (semH S O U passes calls (.aufraeumen (l := l) ⟨.inr grund, saved⟩ R.scopes) (σ) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle hret <;> subst r
  · cases hc : scopesInvH S R.scopes (σ) <;>
      simp only [semH, weiterH, execEndH, hc, Bool.false_eq_true, if_false, if_true, laufA, zErgG, weiterH_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (σ) <;> rw [semH_ende_cons]
    all_goals simp only [execEndH, execStmtH, hc, Bool.false_eq_true, if_false, if_true, semH, weiterH, laufA, zErgG, weiterH_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (σ) <;> rw [semH_dann_cons]
    all_goals simp only [execStmtH, hc, Bool.false_eq_true, if_false, if_true, semH, weiterH, laufA, zErgG, weiterH_logik]
    all_goals first | exact ZErgG.gleich_refl _ | exact weiterH_grund S O U passes calls k _ _

section Replay
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}

/-- Save a scoped answer before any lock is released; empty cleanup is allowed here. -/
theorem fadenS_scopedWert {z : RufFadenG D} {W : World D}
    (hFS : ∀ f, FussS P S lok f)
    (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (R : RueckRessourcen D (vertragVon D z.kopf.f) Λ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedWert = some (e, R)) (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen ⟨.inl (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ), W.lese Λ e.orte⟩ R.scopes⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
    refine fadenS_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
    have he := erg_stabil (hFS _) e (scopedWert_orteS hok hret)
    have hv := evalErg_gleichAuf e (fun _ h => he h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, ?_, trivial, ?_⟩
    · exact GleichAuf.mono (fun _ h => stabilS_mono (fun L hL => R.genau.symm.mem_iff.mp (List.mem_append.mpr ((List.mem_append.mp hL).elim Or.inr Or.inl))) h) ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩
    · intro calls O' U
      have heq := scopedWert_semS O' S U passes calls r e R hret σ (W.lese Λ e.orte) ρ
      rw [hv] at heq
      exact ZErgG.folgt_of_gleich heq

/-- Save a scoped answer before any lock is released; empty cleanup is allowed here. -/
theorem fadenS_scopedGrund {z : RufFadenG D} {W : World D}
    (hFS : ∀ f, FussS P S lok f)
    (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (grund : Fin (vertragVon D z.kopf.f).gruende)
    (R : RueckRessourcen D (vertragVon D z.kopf.f) Λ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedGrund = some (grund, R)) (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen ⟨.inr grund, W⟩ R.scopes⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
    refine fadenS_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
    refine ⟨σ, Nat.le_refl _, ?_, trivial, ?_⟩
    · exact GleichAuf.mono (fun _ h => stabilS_mono (fun L hL => R.genau.symm.mem_iff.mp (List.mem_append.mpr ((List.mem_append.mp hL).elim Or.inr Or.inl))) h) ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩
    · intro calls O' U
      have heq := scopedGrund_semS O' S U passes calls r grund R hret σ W ρ
      exact ZErgG.folgt_of_gleich heq

/-- Release one scope and retain the already evaluated answer. -/
theorem fadenS_scopedFreigabe (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    {z : RufFadenG D} {W : World D} (hF : FadenS P O passes Q S lok z W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende) × World D)
    (L : D.Lock) (remaining : List D.Lock)
    (hr : z.kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a (L :: remaining)⟩)
    (spur' : List (Ereignis D)) :
    FadenS P O passes Q S lok
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen a remaining⟩⟩, spur', z.log⟩ (W.speicher.welt spur') := by
  have hW := kopfS_frei_inv hO hRL hQ hS hsp hK hF.1 L List.mem_cons_self hr
    (fun O' U calls σ hi => by
      rw [semH_aufraeumen_freigabe, hi]
      rfl)
  refine fadenS_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  refine ⟨σ.gibt L, Nat.le_succ _,
    gleichAuf_frei hg spur', trivial, ?_⟩
  intro calls O' U
  apply ZErgG.folgt_of_eq
  rw [semH_aufraeumen_freigabe, hiσ, if_true]

/-- A saved value at completed cleanup still satisfies the function contract. -/
private theorem kopfS_scopedEns (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hFS : ∀ f, FussS P S lok f)
    {F : RufRahmenG D} {W : World D} (hF : KopfS P O passes Q S lok F W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ) (v : ErgVal D (vertragVon D F.f).erg) (vor : World D)
    (hr : F.rest = ⟨l, Γ, _, ρ, .aufraeumen ⟨.inl v, vor⟩ []⟩) :
    EnsAmRueck P F.f F.s0 W F.rho v := by
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, hk, hfa, hra, hqa, hka, hfu, hiu, hku, hg, hok, heq⟩ := hF
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU)
    (rufAusV_passt hf) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu)
    (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only [List.map_nil, List.nil_append] at hg
  simp only [semH, weiterH, scopesInvH, List.all_nil, if_true, List.foldl_nil] at h1
  obtain ⟨σ', hex, hsg⟩ := zErgG_gleich_zurueck (ZErgG.folgt_zurueck h1)
  have hens := ((hK F.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra)
    (regLokal_orakelAus hRL HA) (orakelAus_vertrag hQ hqa)
    (umweltAus S sp HU) (umweltAus_ok hS hsp hiu)
    (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) F.s0 F.rho hreq).1 σ' v hex
  exact ens_transfer hens (GleichAuf.refl _ _)
    (GleichAuf.mono (ens_stabil (hFS _) (List.Perm.refl _))
      ((gleichAuf_SG hsg).trans hg))

/-- With no event type, the saved answer supplies the existing call-record justification. -/
private theorem kopfS_scopedBegr (hE : ¬ Nonempty (Ereignis D))
    {F : RufRahmenG D} {W : World D} (hF : KopfS P O passes Q S lok F W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D F.f).erg ⊕ Fin (vertragVon D F.f).gruende) × World D)
    (hr : F.rest = ⟨l, Γ, _, ρ, .aufraeumen a []⟩) :
    Begruendet P O passes S
      ⟨F.f, F.s0, F.rho, match a.1 with | .inl v => .ok F.s0 v | .inr r => .why F.s0 r⟩ := by
  obtain ⟨H, HA, HU, σ, _, hf, _, hk, _, _, _, hka, _, _, _, _, _, heq⟩ := hF
  cases ha : a.1 with
  | inl v =>
    refine .mk _ _ _ _ H hf (hk.2 hE) (fun calls U hR => ?_)
    have h1 := heq calls O U hR (hka.2 hE) (passtU_leer hE S U HU)
       ⟨rfl, rfl, rfl⟩
    rw [hr] at h1
    simp only [semH, weiterH, scopesInvH, List.all_nil, if_true, List.foldl_nil, ha] at h1
    obtain ⟨σ', hex, _⟩ := zErgG_gleich_zurueck (ZErgG.folgt_zurueck h1)
    exact ⟨σ', hex⟩
  | inr r =>
    refine .mk _ _ _ _ H hf (hk.2 hE) (fun calls U hR => ?_)
    have h1 := heq calls O U hR (hka.2 hE) (passtU_leer hE S U HU)
       ⟨rfl, rfl, rfl⟩
    rw [hr] at h1
    simp only [semH, weiterH, scopesInvH, List.all_nil, if_true, List.foldl_nil, ha] at h1
    obtain ⟨σ', hex, _⟩ := zErgG_gleich_grund (ZErgG.folgt_grund h1)
    exact ⟨σ', hex⟩

/-- Deliver a completed cleanup through the canonical root/callee answer operation. -/
theorem fadenS_scopedAntwort (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hFS : ∀ f, FussS P S lok f)
    {z z' : RufFadenG D} {W : World D} (hF : FadenS P O passes Q S lok z W) (hL : LogOk P z.log)
    (hRS : RahmenStapelS P S lok W.speicher (RufSchluesselG z.kopf) z.stapel)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende) × World D)
    (hr : z.kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a []⟩)
    (hantwort : rufAntwortG z a.2 W a.1 = some z') :
    FadenS P O passes Q S lok z' (W.speicher.welt z'.spur) ∧ LogOk P z'.log := by
  cases hs : z.stapel with
  | nil =>
    simp only [rufAntwortG, hs, Option.some.injEq] at hantwort
    subst z'
    refine ⟨?_, hL⟩
    have hroot := fadenS_lokal hF hr z.kopf.rho (.zurueckgekehrt (l := false) ⟨a.1, a.2⟩) W.spur
      (fun σ hg hok => by
        refine ⟨σ, Nat.le_refl _, hg, trivial, ?_⟩
        intro calls O' U
        apply ZErgG.folgt_of_eq
        simp only [semH, weiterH, scopesInvH, List.all_nil, if_true, List.foldl_nil])
    simpa only [hs] using hroot
  | cons caller rst =>
    have hSt := hF.2
    rw [hs] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hs] at hRS'
    have hb := fun hE => kopfS_scopedBegr hE hF.1 ρ a hr
    rcases a with ⟨av, vor⟩
    cases av with
    | inl v =>
      have hens := kopfS_scopedEns hO hRL hQ hS hsp hK hFS hF.1 ρ v vor hr
      cases ha : antwortRestG z.kopf.f (.inl v) caller.rest with
      | none => simp [rufAntwortG, hs, ha] at hantwort
      | some resp =>
        simp only [rufAntwortG, hs, ha, Option.bind, Option.some.injEq] at hantwort
        subst z'
        refine ⟨⟨?_, hSt'⟩, logOk_rueck hL hens⟩
        rcases caller with ⟨cf, crho, cs0, lc, Γc, Λc, ρc, rc⟩
        cases rc <;> simp only [antwortRestG] at ha
        all_goals first
          | (cases ha
             apply popS_kopf hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
               hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
               _ _ (fun _ h => h) id
               (fun calls O' U σa X h => h.1 rfl) _ ⟨rfl, rfl⟩)
          | (split at ha <;> (try contradiction)
             rename_i he
             cases ha
             apply popS_kopf hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
               hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
               _ _ (fun _ h => h) id
               (fun calls O' U σa X h => h.2 _ _ _ _ _ _ _ _ (Or.inl rfl) he) _ ⟨rfl, rfl⟩)
          | (split at ha <;> (try contradiction)
             rename_i he
             cases ha
             apply popS_kopf hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
               hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
               _ _ (fun _ h => h) (fun hok => ⟨hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2⟩)
               (fun calls O' U σa X h => h.2 _ _ _ _ _ _ _ _ (Or.inr ⟨_, _, rfl⟩) he) _ ⟨rfl, rfl⟩)
    | inr grund =>
      cases ha : antwortRestG z.kopf.f (.inr grund) caller.rest with
      | none => simp [rufAntwortG, hs, ha] at hantwort
      | some resp =>
        simp only [rufAntwortG, hs, ha, Option.bind, Option.some.injEq] at hantwort
        subst z'
        refine ⟨⟨?_, hSt'⟩, logOk_grund hL⟩
        rcases caller with ⟨cf, crho, cs0, lc, Γc, Λc, ρc, rc⟩
        cases rc <;> simp only [antwortRestG] at ha
        all_goals try contradiction
        all_goals
          split at ha <;> (try contradiction)
          rename_i hn
          cases ha
          apply popS_kopf hWc W (fun σa => .why σa grund) (Or.inr ⟨grund, fun _ => rfl⟩)
            hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
            _ _ (fun _ h => h)
            (fun hok => by
              apply okS_alsBlock _ _ _ hok.1 hok.2.1 hok.2.2.2.2
              intro L
              exact Block.held_iff (by assumption) L)
            (fun calls O' U σa X h => h _ _ _ _ _ _ _ _ _ _ rfl hn) _ ⟨rfl, rfl⟩

end Replay

end Gabbro.Grammatik
