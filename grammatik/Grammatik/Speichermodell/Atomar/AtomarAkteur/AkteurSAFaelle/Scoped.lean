module

public import Grammatik.Speichermodell.Atomar.AtomarReplay
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Scoped
public import Grammatik.Speichermodell.Maschine.SperreSemA.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The checked footprint of the selected scoped-return expression. -/
private theorem scopedWert_orteSA {P : Programm D} {S0 S1 : List (D.Tab ⊕ D.Glob)}
    {r : GRest D V l Γ Λ} {e : ErgExpr D Γ Λ V.erg} {R : RueckRessourcen D V Λ}
    (hok : r.okS P S0 S1) (hret : r.scopedWert = some (e, R)) : e.orte ⊆ S0 := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle hret <;> subst r
  · simpa only [endblockOrteP] using hok.2
  · simpa only [stmtOrteP] using (okS_ende_cons hok).2.1
  · simpa only [stmtOrteP] using (okS_dann_cons hok).2.1

/-- Saving the answer preserves the source prediction, including its lexical cleanup. -/
private theorem scopedWert_semSA (O : Orakel D) (S : SperrInv D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (e : ErgExpr D Γ Λ V.erg)
    (R : RueckRessourcen D V Λ) (hret : r.scopedWert = some (e, R))
    (σ saved : World D) (ρ : Env D Γ) :
    (semHA S O U A passes calls r σ ρ).gleich
      (semHA S O U A passes calls (.aufraeumen (l := l) ⟨.inl (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ), saved⟩ R.scopes) (leseA A σ Λ e.orte) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedWert_faelle hret <;> subst r
  · cases hc : scopesInvH S R.scopes (leseA A σ Λ e.orte) <;>
      simp only [semHA, weiterHA, execEndHA, hc, Bool.false_eq_true, if_false, if_true, laufA, zErgG, weiterHA_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (leseA A σ Λ e.orte) <;> rw [semHA_ende_cons]
    all_goals simp only [execEndHA, execStmtHA, hc, Bool.false_eq_true, if_false, if_true, semHA, weiterHA, laufA, zErgG, weiterHA_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (leseA A σ Λ e.orte) <;> rw [semHA_dann_cons]
    all_goals simp only [execStmtHA, hc, Bool.false_eq_true, if_false, if_true, semHA, weiterHA, laufA, zErgG, weiterHA_logik]
    all_goals first | exact ZErgG.gleich_refl _ | exact weiterHA_zurueck S O U A passes calls k _ _

/-- Saving the answer preserves the source prediction, including its lexical cleanup. -/
private theorem scopedGrund_semSA (O : Orakel D) (S : SperrInv D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (r : GRest D V l Γ Λ) (grund : Fin V.gruende)
    (R : RueckRessourcen D V Λ) (hret : r.scopedGrund = some (grund, R))
    (σ saved : World D) (ρ : Env D Γ) :
    (semHA S O U A passes calls r σ ρ).gleich
      (semHA S O U A passes calls (.aufraeumen (l := l) ⟨.inr grund, saved⟩ R.scopes) (σ) ρ) := by
  obtain h | ⟨rest, h⟩ | ⟨Λ', rest, k, h⟩ := GRest.scopedGrund_faelle hret <;> subst r
  · cases hc : scopesInvH S R.scopes (σ) <;>
      simp only [semHA, weiterHA, execEndHA, hc, Bool.false_eq_true, if_false, if_true, laufA, zErgG, weiterHA_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (σ) <;> rw [semHA_ende_cons]
    all_goals simp only [execEndHA, execStmtHA, hc, Bool.false_eq_true, if_false, if_true, semHA, weiterHA, laufA, zErgG, weiterHA_logik]
    all_goals exact ZErgG.gleich_refl _
  · cases hc : scopesInvH S R.scopes (σ) <;> rw [semHA_dann_cons]
    all_goals simp only [execStmtHA, hc, Bool.false_eq_true, if_false, if_true, semHA, weiterHA, laufA, zErgG, weiterHA_logik]
    all_goals first | exact ZErgG.gleich_refl _ | exact weiterHA_grund S O U A passes calls k _ _

section Replay
variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D} {zyk : D.Fn → D.Fn → Bool}

/-- Save a scoped answer before any lock is released; empty cleanup is allowed here. -/
theorem fadenSA_scopedWert {z : RufFadenG D} {W : World D}
    (hFS : ∀ f, FussSX P S lok Tg f)
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (R : RueckRessourcen D (vertragVon D z.kopf.f) Λ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedWert = some (e, R)) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen ⟨.inl (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ), W.lese Λ e.orte⟩ R.scopes⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
  refine fadenSA_lese hF hr ρ _ spur' Λ e.orte (fun hok => ?_) (fun σ hg hok => ?_)
  · exact erg_stabilX (hFS _) e (scopedWert_orteSA hok hret)
  · have hv := evalErg_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ
    refine ⟨σ, ⟨Nat.le_refl _, Nat.le_refl _⟩, ?_, trivial, ?_⟩
    · exact GleichAuf.mono (fun _ h => List.mem_append_left _ (stabilS_mono (fun L hL => R.genau.symm.mem_iff.mp (List.mem_append.mpr ((List.mem_append.mp hL).elim Or.inr Or.inl))) h)) hg
    · intro calls O' U A σ0 hQ hg0 hread
      have heq := scopedWert_semSA O' S U A passes calls r e R hret σ0 (W.lese Λ e.orte) ρ
      rw [hread, hv] at heq
      exact ZErgG.folgt_of_gleich heq

/-- Save a scoped answer before any lock is released; empty cleanup is allowed here. -/
theorem fadenSA_scopedGrund {z : RufFadenG D} {W : World D}
    (hFS : ∀ f, FussSX P S lok Tg f)
    (hF : FadenSA P O passes Q S lok Tg m zyk z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (grund : Fin (vertragVon D z.kopf.f).gruende)
    (R : RueckRessourcen D (vertragVon D z.kopf.f) Λ)
    (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (hret : r.scopedGrund = some (grund, R)) (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen ⟨.inr grund, W⟩ R.scopes⟩⟩, spur', z.log⟩
      (W.speicher.welt spur') := by
    refine fadenSA_lokal hF hr ρ _ spur' (fun σ hg hok => ?_)
    refine ⟨rfl, ?_, trivial, ?_⟩
    · exact GleichAuf.mono (fun _ h => stabilS_mono (fun L hL => R.genau.symm.mem_iff.mp (List.mem_append.mpr ((List.mem_append.mp hL).elim Or.inr Or.inl))) h) ⟨fun t ht => hg.1 t ht, fun g hg' => hg.2 g hg'⟩
    · intro calls O' U A
      have heq := scopedGrund_semSA O' S U A passes calls r grund R hret σ W ρ
      exact ZErgG.folgt_of_gleich heq

/-- Release one scope and retain the already evaluated answer. -/
theorem fadenSA_scopedFreigabe (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragOP (PreQ P) Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f)
    {z : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg m zyk z W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende) × World D)
    (L : D.Lock) (remaining : List D.Lock)
    (hr : z.kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a (L :: remaining)⟩)
    (spur' : List (Ereignis D)) :
    FadenSA P O passes Q S lok Tg m zyk
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨l, Γ, _, ρ, .aufraeumen a remaining⟩⟩, spur', z.log⟩ (W.speicher.welt spur') := by
  have hW := kopfSA_frei_inv hO hRL hQ hS hsp hK hF.1 L List.mem_cons_self hr
    (fun O' U A calls σ hi => by
      rw [semHA_aufraeumen_freigabe, hi]
      rfl)
  refine fadenSA_lokalQ hF hr ρ _ spur' (fun σ HX hfx hkx hg hok => ?_)
  have hiσ : S.inv L σ.speicher = true := (inv_gleich hS List.mem_cons_self hg).trans hW
  refine ⟨σ.gibt L, HX, hfx, kurzX_mono hkx (Nat.le_succ _), fun _ h => h, World.rang_le_gibt σ L,
    gleichAuf_frei hg spur', trivial, ?_⟩
  intro calls O' U A _ _ _
  apply ZErgG.folgt_of_eq
  rw [semHA_aufraeumen_freigabe, hiσ]
  rfl

/-- A saved value at completed cleanup still satisfies the function contract. -/
private theorem kopfSA_scopedEns (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragOP (PreQ P) Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f)
    (hFS : ∀ f, FussSX P S lok Tg f)
    (hTV : ∀ c, Tg c → VertragsFrei P c)
    {F : RufRahmenG D} {W : World D} (hF : KopfSA P O passes Q S lok Tg m zyk F W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ) (v : ErgVal D (vertragVon D F.f).erg) (vor : World D)
    (hr : F.rest = ⟨l, Γ, _, ρ, .aufraeumen ⟨.inl v, vor⟩ []⟩) :
    EnsAmRueck P F.f F.s0 W F.rho v := by
  obtain ⟨H, HA, HU, HX, σ, hreq, hf, hv, hm, hk, hfa, hra, hqa, hka, hfu, hiu, hku,
    ⟨hfx, hkx⟩, hg, hok, heq⟩ := hF
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX)
    (rufAusV_passt hf) (orakelAus_passt O hfa) (umweltAus_passt S sp hfu)
    (umweltAusA_passt Tg hfx) (umweltAusA_ok Tg HX) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only [List.map_nil, List.nil_append] at hg
  simp only [semHA, weiterHA, scopesInvH, List.all_nil, if_true, List.foldl_nil] at h1
  obtain ⟨σ', hex, hsg⟩ := zErgG_gleich_zurueck (ZErgG.folgt_zurueck h1)
  have hens := ((hK F.f).1 (orakelAus O HA) (orakelAus_rahmen hO hra)
    (regLokal_orakelAus hRL HA) (orakelAus_vertragOP hQ hqa)
    (umweltAus S sp HU) (umweltAus_ok hS hsp hiu)
    (umweltAusA Tg HX) (umweltAusA_ok Tg HX)
    (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) F.s0 F.rho hreq).1 σ' v hex
  exact ens_transfer hens (GleichAuf.refl _ _)
    (GleichAuf.mono (ens_stabilX (hFS _) hTV (List.Perm.refl _))
      ((gleichAuf_SG hsg).trans hg))

/-- With no event type, the saved answer supplies the existing call-record justification. -/
private theorem kopfSA_scopedBegr (hE : ¬ Nonempty (Ereignis D))
    {F : RufRahmenG D} {W : World D} (hF : KopfSA P O passes Q S lok Tg m zyk F W)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D F.f).erg ⊕ Fin (vertragVon D F.f).gruende) × World D)
    (hr : F.rest = ⟨l, Γ, _, ρ, .aufraeumen a []⟩) :
    BegruendetA P O passes S
      ⟨F.f, F.s0, F.rho, match a.1 with | .inl v => .ok F.s0 v | .inr r => .why F.s0 r⟩ := by
  obtain ⟨H, HA, HU, HX, σ, _, hf, _, _, hk, _, _, _, hka, _, _, _, _, _, _, heq⟩ := hF
  cases ha : a.1 with
  | inl v =>
    refine .mk _ _ _ _ H hf (hk.2 hE) (fun calls U A hR => ?_)
    have h1 := heq calls O U A hR (hka.2 hE) (passtU_leer hE S U HU)
      (passtX_leer hE Tg A HX) (havocA_leer hE Tg A) ⟨rfl, rfl, rfl⟩
    rw [hr] at h1
    simp only [semHA, weiterHA, scopesInvH, List.all_nil, if_true, List.foldl_nil, ha] at h1
    obtain ⟨σ', hex, _⟩ := zErgG_gleich_zurueck (ZErgG.folgt_zurueck h1)
    exact ⟨σ', hex⟩
  | inr r =>
    refine .mk _ _ _ _ H hf (hk.2 hE) (fun calls U A hR => ?_)
    have h1 := heq calls O U A hR (hka.2 hE) (passtU_leer hE S U HU)
      (passtX_leer hE Tg A HX) (havocA_leer hE Tg A) ⟨rfl, rfl, rfl⟩
    rw [hr] at h1
    simp only [semHA, weiterHA, scopesInvH, List.all_nil, if_true, List.foldl_nil, ha] at h1
    obtain ⟨σ', hex, _⟩ := zErgG_gleich_grund (ZErgG.folgt_grund h1)
    exact ⟨σ', hex⟩

/-- Deliver a completed cleanup through the canonical root/callee answer operation. -/
theorem fadenSA_scopedAntwort (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragOP (PreQ P) Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f)
    (hFS : ∀ f, FussSX P S lok Tg f)
    (hTV : ∀ c, Tg c → VertragsFrei P c)
    {z z' : RufFadenG D} {W : World D} (hF : FadenSA P O passes Q S lok Tg m zyk z W) (hL : LogOk P z.log)
    (hRS : RahmenStapelS P S lok W.speicher (RufSchluesselG z.kopf) z.stapel)
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende) × World D)
    (hr : z.kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a []⟩)
    (hantwort : rufAntwortG z a.2 W a.1 = some z') :
    FadenSA P O passes Q S lok Tg m zyk z' (W.speicher.welt z'.spur) ∧ LogOk P z'.log := by
  cases hs : z.stapel with
  | nil =>
    simp only [rufAntwortG, hs, Option.some.injEq] at hantwort
    subst z'
    refine ⟨?_, hL⟩
    have hroot := fadenSA_lokal hF hr z.kopf.rho (.zurueckgekehrt (l := false) ⟨a.1, a.2⟩) W.spur
      (fun σ hg hok => by
        refine ⟨rfl, hg, trivial, ?_⟩
        intro calls O' U A
        apply ZErgG.folgt_of_eq
        simp only [semHA, weiterHA, scopesInvH, List.all_nil, if_true, List.foldl_nil])
    simpa only [hs, Speicher.welt_speicher] using hroot
  | cons caller rst =>
    have hSt := hF.2
    rw [hs] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hs] at hRS'
    have hb := fun hE => kopfSA_scopedBegr hE hF.1 ρ a hr
    rcases a with ⟨av, vor⟩
    cases av with
    | inl v =>
      have hens := kopfSA_scopedEns hO hRL hQ hS hsp hK hFS hTV hF.1 ρ v vor hr
      cases ha : antwortRestG z.kopf.f (.inl v) caller.rest with
      | none => simp [rufAntwortG, hs, ha] at hantwort
      | some resp =>
        simp [rufAntwortG, hs, ha] at hantwort
        subst z'
        refine ⟨⟨?_, hSt'⟩, logOk_rueck hL hens⟩
        rcases caller with ⟨cf, crho, cs0, lc, Γc, Λc, ρc, rc⟩
        cases rc with
        | wartet rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · rename_i he
            cases ha
            refine popSA_kopf hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
              hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
              _ (.dann rest (.schrumpf k)) (fun _ h => h) id ?_ _ ⟨rfl, rfl⟩
            intro calls O' U A σa X h
            exact h.2 _ _ _ _ _ _ _ _ (Or.inl rfl) he
          · contradiction
        | wartetSonst n err rest k =>
          simp only [antwortRestG] at ha
          split at ha
          · rename_i he
            cases ha
            refine popSA_kopf hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
              hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
              _ (.dann rest (.schrumpf k)) (fun _ h => h) ?_ ?_ _ ⟨rfl, rfl⟩
            · intro hok
              exact ⟨hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2⟩
            · intro calls O' U A σa X h
              exact h.2 _ _ _ _ _ _ _ _ (Or.inr ⟨n, err, rfl⟩) he
          · contradiction
        | _ =>
          simp only [antwortRestG] at ha
          cases ha
          exact popSA_kopf hWc W (fun σa => .ok σa v) (Or.inl ⟨v, fun _ => rfl, hens⟩)
            hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
            _ _ (fun _ h => h) id
            (fun calls O' U A σa X h => h.1 rfl) _ ⟨rfl, rfl⟩
    | inr grund =>
      cases ha : antwortRestG z.kopf.f (.inr grund) caller.rest with
      | none => simp [rufAntwortG, hs, ha] at hantwort
      | some resp =>
        simp [rufAntwortG, hs, ha] at hantwort
        subst z'
        refine ⟨⟨?_, hSt'⟩, logOk_grund hL⟩
        rcases caller with ⟨cf, crho, cs0, lc, Γc, Λc, ρc, rc⟩
        cases rc <;> simp only [antwortRestG] at ha
        all_goals try contradiction
        all_goals
          split at ha <;> (try contradiction)
          rename_i hn
          cases ha
          apply popSA_kopf hWc W (fun σa => .why σa grund) (Or.inr ⟨grund, fun _ => rfl⟩)
            hb (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
            _ _ (fun _ h => h)
            (fun hok => by
              apply okS_alsBlock _ _ _ hok.1 hok.2.1 hok.2.2.2.2
              intro L
              exact Block.held_iff (by assumption) L)
            (fun calls O' U A σa X h => h _ _ _ _ _ _ _ _ _ _ rfl hn) _ ⟨rfl, rfl⟩

end Replay

end Gabbro.Grammatik
