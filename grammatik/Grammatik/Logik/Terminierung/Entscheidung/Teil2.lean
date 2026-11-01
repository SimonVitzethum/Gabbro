module

public import Grammatik.Logik.Terminierung.Rekursion
public import Grammatik.Gen.Abdeckung.Satz.MerkmalZerlegt
public import Grammatik.Zielsatz.Faeden.Verbund.T1
public import Grammatik.Logik.Ruf.Maschine.BudgetMonoton
public import Grammatik.Logik.Terminierung.Entscheidung.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Klasse
variable [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (mass : D.Fn → Bool)

theorem ewigFrei_rumpf (hvoll : ∀ g : D.Fn, g ∈ fs) {f : D.Fn} (hf : ewigFrei P fs f = true) :
    rufeE (ewigFrei P fs) (ewigFreiS P fs) false (P.rumpf f) = true := by
  have hew : (befE false false (P.rumpf f)).ewig = false := by
    have := List.all_eq_true.mp hf f (hvoll f)
    simpa [reachB_wurzel, befund] using this
  rw [rufeE_ohneEwig _ _ (P.rumpf f) false false hew]
  refine rufeE_aus_ruft hvoll _ fun g hr => List.all_eq_true.2 fun h _ => ?_
  cases hgh : reachB P fs g h
  · rfl
  · have hfg : reachB P fs f g = true := Zielsatz.reachB_ruft P hvoll (reachB_wurzel P fs f) hr
    have := List.all_eq_true.mp hf h (hvoll h)
    simpa [reachB_trans hvoll hfg hgh] using this

end Klasse

/-! ## 5. `endet` never stands at a spent budget -/

section Budget

variable [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
  {fs : List D.Fn}

theorem rufeR_istEwig {Z : D.Fn → Bool} {ZS : Nat → Bool} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {r : GRest D V l Γ Λ} (h : rufeR Z ZS false r = true) : r.istEwig = false := by
  cases r <;> simp_all [rufeR, GRest.istEwig]

/-- The frame's residue admits no `forever`. -/
def EFR (P : Programm D) (fs : List D.Fn) (r : RufRahmenG D) : Prop :=
  rufeR (ewigFrei P fs) (ewigFreiS P fs) false r.rest.2.2.2.2 = true

theorem ewigFrei_schritt (hvoll : ∀ g : D.Fn, g ∈ fs) {M M' : RufMaschineG D} {t : Faden}
    (hs : RufSchrittGX P O pa Tg M t M')
    (hI : ∀ r ∈ (M.faeden t).kopf :: (M.faeden t).stapel, EFR P fs r) :
    ∀ r ∈ (M'.faeden t).kopf :: (M'.faeden t).stapel, EFR P fs r := by
  obtain ⟨σ, M'', hg, _, _, _, hfa, _, _⟩ := hs
  have hfa' : M'.faeden t = M''.faeden t := by rw [hfa]
  rw [hfa']
  have hI' : ∀ r ∈ ((mitSpeicher M σ).faeden t).kopf :: ((mitSpeicher M σ).faeden t).stapel, EFR P fs r := hI
  rcases schrittArt hg (fun _ => 0) (ewigFrei P fs) (ewigFreiS P fs) false with
    ⟨hst, hpot⟩ | ⟨g, caller', rho, s0, hst, hkopf, hpush⟩ | ⟨caller, rst, hst, hst', hpop⟩
  · intro r hr
    rw [hst] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hpot (hI' _ List.mem_cons_self)).1
    · exact hI' r (List.mem_cons_of_mem _ hr)
  · obtain ⟨hokc, hdir⟩ := hpush (hI' _ List.mem_cons_self)
    have hgf : ewigFrei P fs g = true := by
      rcases hdir with ⟨hz, _⟩ | ⟨n, hn, hp, _⟩
      · exact hz
      · have := List.all_eq_true.mp hn g (hvoll g)
        simpa [hp] using this
    intro r hr
    rw [hst] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · unfold EFR
      rw [hkopf]
      exact ewigFrei_rumpf P fs hvoll hgf
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hokc
      · exact hI' r (List.mem_cons_of_mem _ hr)
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have hc : EFR P fs caller := hI' caller (by rw [hst]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      exact (hpop (fun _ => 0) _ _ false).1 hc
    · rw [hst'] at hr
      exact hI' r (by rw [hst]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

/-- **A thread whose start reaches no `forever` never stands at a `forever`**: no frame of it ever holds one, on
    every GX run -- so its head is never a spent budget (`RestHalt .budget` is a head `ewig 0`). -/
theorem ewigFrei_ohne_budget (hvoll : ∀ g : D.Fn, g ∈ fs) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init)
    (t : Faden) (hw : ewigFrei P fs (init t).1 = true) :
    ∀ j, ((R.M j).faeden t).kopf.rest.2.2.2.2.istEwig = false := by
  have hI : ∀ j, ∀ r ∈ ((R.M j).faeden t).kopf :: ((R.M j).faeden t).stapel, EFR P fs r := by
    intro j
    induction j with
    | zero =>
      rw [h0]
      rcases hi : init t with ⟨g, rho⟩
      rw [hi] at hw
      unfold RufStartG
      dsimp only
      rw [hi]
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ewigFrei_rumpf P fs hvoll hw
    | succ j ih =>
      cases h : R.akt j with
      | none => rw [R.stotter j h]; exact ih
      | some u =>
        by_cases htu : t = u
        · subst htu
          exact ewigFrei_schritt hvoll (R.schritt j t h) ih
        · rw [Zielsatz.gx_fremd (R.schritt j u h) t htu]; exact ih
  intro j
  exact rufeR_istEwig (hI j _ List.mem_cons_self)

end Budget

/-! ## 6. The class `endet` -/

/-- **T5 -- THE CLASS `endet` MEANS WHAT IT SAYS.** A thread whose start function the algorithm puts in class
    `endet`: on every infinite GX run it takes only finitely many steps, and its head never stands at a `forever` (so
    never at a spent budget) -- its end does not lean on the passes machine G grants. -/
theorem endet_satz [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (m : Mass D) {fs : List D.Fn} (mass : D.Fn → Bool) (Q : AxEns D) (S : SperrInv D) (K : Faden → D.Fn → Bool)
    (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P pa Q S Tg f) (hM : ∀ f, MassPflicht P pa Q S Tg m (zykS P fs) f)
    (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hL : ∀ f g, zykS P fs f g = true → (m f).length = (m g).length)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden)
    (hk : klasse P fs mass (init t).1 = .endet) :
    (∃ N, ∀ j, N ≤ j → R.akt j ≠ some t) ∧ ∀ j, ((R.M j).faeden t).kopf.rest.2.2.2.2.istEwig = false :=
  ⟨terminierung m Q S K lok sp init hO hRL hQ hlok hS hvoll hAbg hWurzel hTA hTV hTS hTO hFragS hFS hlokK hK hM
      hStart hsp hex hL R h0 t,
    ewigFrei_ohne_budget hvoll sp init R h0 t (ewigFrei_klasse P fs mass hvoll hk)⟩

end Gabbro.Grammatik
