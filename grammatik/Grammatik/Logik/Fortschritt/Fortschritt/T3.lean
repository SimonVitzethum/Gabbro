/- Part 3 of 3 of `Fortschritt` (split by instrumente/teile/lean-teilen.py; the umbrella `Fortschritt.lean` imports all parts). -/
import Grammatik.Logik.Fortschritt.Fortschritt.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Bereich

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **A replayed thread passes every float range check at its head** (as `fadenS_prueft` for
    the `logik` checks): a failing check makes the head predict `logik bereich` at the
    replay's sequential world (the operands read stable carriers, so the check reads the same
    there), which `KoerperGutS` excludes. -/
theorem fadenS_bereich (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hFS : ∀ f, FussS P S lok f) {M : RufMaschineG D}
    (t : Faden) (hF : FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) :
    BereichG M t := by
  refine ⟨fun l Γ Λ Λ' ρ op l1 h1 l2 h2 lo hi a b rest k hr hv => ?_,
    fun l Γ Λ Λ' ρ q lo hi rest k hr hv => ?_,
    fun l Γ Λ Λ' ρ l1 h1 e lo hi rest k hr hv => ?_⟩
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    have hab : a.orte ++ b.orte ⊆ fussOrteG P (M.faeden t).kopf.f :=
      fun _ h => hok.2.1 (List.mem_append_left _ h)
    have hgl := hg.lese Λ Λ (a.orte ++ b.orte) (a.orte ++ b.orte)
    have ea := eval_gleichAuf a (fun _ h => expr_stabil (hFS _) a
      (fun _ h' => hab (List.mem_append_left _ h')) h) hgl ρ
    have eb := eval_gleichAuf b (fun _ h => expr_stabil (hFS _) b
      (fun _ h' => hab (List.mem_append_right _ h')) h) hgl ρ
    have hv' : gleitPasst lo hi (gleitRechne op
        (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
        (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = none := by
      rw [ea, eb]; exact hv
    refine hno .bereich ?_
    rw [semH_dann]
    simp only [execBlockH, hv']
    exact weiterH_logik _ _ _ _ _ _ _
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    refine hno .bereich ?_
    rw [semH_dann]
    simp only [execBlockH, hv]
    exact weiterH_logik _ _ _ _ _ _ _
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    have he : e.orte ⊆ fussOrteG P (M.faeden t).kopf.f :=
      fun _ h => hok.2.1 (List.mem_append_left _ h)
    have ee := eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => he h') h)
      (hg.lese Λ Λ e.orte e.orte) ρ
    have hv' : gleitPasst lo hi (gleitAusInt
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = none := by
      rw [ee]; exact hv
    refine hno .bereich ?_
    rw [semH_dann]
    simp only [execBlockH, hv']
    exact weiterH_logik _ _ _ _ _ _ _

/-- **On every reachable machine every thread passes its float range checks**, for any set
    of local carriers with the rely `LokOk` (the premises of `zielInvS_erreichbarL`). -/
theorem bereichG_erreichbarL (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) (M : RufMaschineG D)
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) : ∀ t, BereichG M t := fun t =>
  fadenS_bereich hO hRL hQ hS hsp hK hFS t
    ((zielInvS_erreichbarL P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS hLok hK
      hStart hsp hex M hr).1.1 t)

/-- The same for thread-local carriers of the call graphs `K` (the premises of
    `ziel_ort_mehrfaden_bei`). -/
theorem bereichG_mehrfaden (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) (M : RufMaschineG D)
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) : ∀ t, BereichG M t :=
  bereichG_erreichbarL P O passes Q S (lokK P K) sp init hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFuss) hFuss
    (lokOk_mehr hO hvoll sp init K hAbg hWurzel) hK hStart hSstart hex M hr

end Bereich
/-! ## 7. The theorem -/

/-- **`FortschrittG` on every reachable machine at which no `logik` check
    fails.** From `GutO`, the lock floors (`StufenM`) and a duplicate-free
    start trace, on every reachable machine with `KeinLogikHaltG`: every
    thread is finished, waits for a lock another thread holds, stands at a
    named hardware stop, or can step. -/
theorem fortschrittG_aus {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (hSt : StufenM P) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) (hL : KeinLogikHaltG O passes M)
    (hB : ∀ t, BereichG M t) (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) :
    Zielsatz.FortschrittG P O passes M := fun t =>
  fortschritt_faden hO (fortInvG_erreichbar sp init hr t)
    (rufG_nie_wartend P O passes sp init M hr t)
    (fun L hL' => rufG_haelt_statisch hO sp init hr t _ List.mem_cons_self L hL') (hL t) (hB t)
    (rangInvG_erreichbar hO hSt sp init hND hr t) (kopf_ants hAnt sp init hr t)

/-- **Progress up to named stops under the premises of the flagship**
    (`ziel_ort_sperre`, whose conclusion supplies `KeinLogikHaltG`), the
    lock floors, and a duplicate-free start trace. -/
theorem fortschrittG_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hSt : StufenM P) (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup)
    (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      Zielsatz.FortschrittG P O passes M := fun M hr =>
  fortschrittG_aus hO hSt sp init hND hr
    (ziel_ort_sperre P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss hK hStart
      hSstart hex M hr).2.2.1
    (bereichG_erreichbarL P O passes Q S (freiB fs) sp init hO hRL hQ hlok hS
      (programmImFragmentS_ok P S hvoll hFrag (fussSperreB_ok hvoll hFuss))
      (fussSperreB_ok hvoll hFuss) (lokOk_frei hO hvoll sp init) hK hStart hSstart hex M hr)
    hAnt

/-- **Progress up to named stops under the premises of `ziel_ort_mehrfaden`**
    (several active threads with thread-local carriers, every budget), the
    lock floors and a duplicate-free start trace. -/
theorem fortschrittG_mehrfaden (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ (passes : Nat) (f : D.Fn), InvGutS P passes Q S f)
    (hSt : StufenM P) (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup)
    (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      Zielsatz.FortschrittG P O passes M := fun passes M hr =>
  fortschrittG_aus hO hSt sp init hND hr
    (ziel_ort_mehrfaden P O Q S fs sp init K hO hRL hQ hlok hS hvoll hFrag hAbg hWurzel hFuss hK
      hStart hSstart hex hI passes M hr).1.2.2.1
    (bereichG_mehrfaden P O passes Q S fs sp init K hO hRL hQ hlok hS hvoll hFrag hAbg hWurzel
      hFuss (hK passes) hStart hSstart hex M hr) hAnt

/-- Starts without signature locks (the declared starts of `AkzeptiertSpec`
    and every idle start, `Zielsatz.Ruhig`) have a duplicate-free start
    trace. -/
theorem startSpur_nodup_leer (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (h : ∀ t, D.haelt (init t).1 = []) :
    ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup := fun t => by
  rw [startSpur, h t]
  exact List.nodup_nil

#print axioms Gabbro.Grammatik.Endblock.alsBlock_terminal
#print axioms Gabbro.Grammatik.fortInvG_schritt
#print axioms Gabbro.Grammatik.fortInvG_erreichbar
#print axioms Gabbro.Grammatik.axiom_erw
#print axioms Gabbro.Grammatik.blatt_fall
#print axioms Gabbro.Grammatik.fort_abb
#print axioms Gabbro.Grammatik.fort_ende
#print axioms Gabbro.Grammatik.fort_dann
#print axioms Gabbro.Grammatik.fortschritt_faden
#print axioms Gabbro.Grammatik.fortschrittG_aus
#print axioms Gabbro.Grammatik.fortschrittG_sperre
#print axioms Gabbro.Grammatik.fortschrittG_mehrfaden
#print axioms Gabbro.Grammatik.startSpur_nodup_leer


end Gabbro.Grammatik
