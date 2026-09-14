/-
  File:      Grammatik/SperreMaschine.lean
  Subject:   THE MACHINE SIDE OF LOCK INVARIANTS -- what G guarantees without
             the user: (1) the rely on the stable carriers of every frame
             (other threads leave them alone), (2) the callee frame fact of
             `rufG_rahmen` over the stable carriers of every suspended frame
             (`rufG_rahmenS`), (3) the classification of the steps that
             release a lock, and (4) the lock invariant of every FREE lock
             holds in the machine memory (`SperrInvG`), given that every
             release re-establishes it (which the replay derives from the
             user obligation, `ZielOrtSperre.lean`).
-/
import Grammatik.SperreBeweis

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The rely on stable carriers -/

section Rely

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The local carriers are left alone by other threads**: on every
    reachable machine, a step of thread `u` does not move a local carrier
    of the safe set of any frame of another thread. For `lok = freiB fs`
    (written by no function) this holds on every run (`lokOk_frei`); for a
    program with one active thread and every carrier local it holds because
    only that thread moves and the others' frames have empty footprints
    (`ZielOrtEinfaden.lean`). -/
def LokOk (P : Programm D) (O : Orakel D) (passes : Nat) (lok : D.Tab ⊕ D.Glob → Bool)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop :=
  ∀ {M M' : RufMaschineG D} {u : Faden}, RufErreichbarG P O passes (RufStartG P sp init) M →
    RufSchrittG P O passes M u M' → ∀ t, t ≠ u →
    ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, ∀ c ∈ sicher P lok F.f, lok c = true →
      TraegerGleich M'.speicher M.speicher c

/-- Carriers written by no function are left alone by every step. -/
theorem lokOk_frei (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) : LokOk P O passes (freiB fs) sp init :=
  fun _ hs _ _ _ _ c _ hc => schritt_traeger hO hs c (Or.inr (freiB_ok hvoll hc _))

/-- **Another thread's step leaves the stable carriers of every frame of
    thread `t` alone**: a safe carrier is guarded by a signature lock the
    frame's thread holds (`rufG_haelt_signatur`) or local (`LokOk`); a
    protected carrier of a lock the frame names held is guarded by that
    lock, which the thread holds (`rufG_haelt_statisch`). -/
theorem stabilS_rely (hO : GutO O) {S : SperrInv D} (hS : SperrInvOk S)
    {lok : D.Tab ⊕ D.Glob → Bool} (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hlok : LokOk P O passes lok sp init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (F : RufRahmenG D) (hF : F ∈ (M.faeden t).kopf :: (M.faeden t).stapel)
    (c : D.Tab ⊕ D.Glob) (hc : c ∈ stabilS P S lok F.f F.rest.2.2.1) :
    TraegerGleich M'.speicher M.speicher c := by
  rcases stabilS_mem.mp hc with hc | ⟨L, hL, hcL⟩
  · have hsf := (sicher_mem.mp hc).2
    simp only [Bool.or_eq_true] at hsf
    rcases hsf with hsig | hfrei
    · obtain ⟨L, hB, hLh⟩ := sigB_ok hsig
      have hLt := rufG_haelt_signatur hO sp init hr t F hF L hLh
      exact relyG hO sp init hex hr hs t (fun e => htu e.symm) c L hB hLt
    · exact hlok hr hs t htu F hF c hc hfrei
  · have hLt := rufG_haelt_statisch hO sp init hr t F hF L hL
    exact relyG hO sp init hex hr hs t (fun e => htu e.symm) c L (hS.1 L c hcL) hLt

end Rely

/-! ## 2. The callee frame fact over stable carriers -/

section Stapel

variable (P : Programm D) (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool)

/-- The frame invariant of a stack (as `RahmenStapel`), over the stable
    carriers of each suspended frame at its holdings. -/
def RahmenStapelS (Sp : Speicher D) :
    (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest =>
      (∀ c, TraegerSchreibt G.1 c = true → TraegerSchreibt F.f c = true) ∧
      (∀ c ∈ stabilS P S lok F.f F.rest.2.2.1, TraegerSchreibt G.1 c = false →
        TraegerGleich Sp G.2.2.speicher c) ∧
      RahmenStapelS Sp (RufSchluesselG F) rest

def RahmenInvS (M : RufMaschineG D) : Prop :=
  ∀ t, RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden t).kopf) (M.faeden t).stapel

end Stapel

section StapelL

variable {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}

theorem rahmenStapelS_cons {Sp : Speicher D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D} {F : RufRahmenG D} {rest : List (RufRahmenG D)} :
    RahmenStapelS P S lok Sp G (F :: rest) ↔
      ((∀ c, TraegerSchreibt G.1 c = true → TraegerSchreibt F.f c = true) ∧
      (∀ c ∈ stabilS P S lok F.f F.rest.2.2.1, TraegerSchreibt G.1 c = false →
        TraegerGleich Sp G.2.2.speicher c) ∧
      RahmenStapelS P S lok Sp (RufSchluesselG F) rest) := Iff.rfl

theorem rahmenStapelS_speicher {Sp Sp' : Speicher D} :
    ∀ {G : Σ f : D.Fn, Env D (D.params f) × World D} {st : List (RufRahmenG D)},
      RahmenStapelS P S lok Sp G st →
      (∀ c, TraegerSchreibt G.1 c = false → TraegerGleich Sp' Sp c) →
        RahmenStapelS P S lok Sp' G st
  | _, [], _, _ => trivial
  | G, F :: rest, h, hS => by
      obtain ⟨hk, hf, hr⟩ := rahmenStapelS_cons.mp h
      refine rahmenStapelS_cons.mpr ⟨hk, fun c hc hw => traegerGleich_trans (hS c hw) (hf c hc hw),
        rahmenStapelS_speicher hr (fun c hw => hS c ?_)⟩
      cases hG : TraegerSchreibt G.1 c with
      | false => rfl
      | true =>
          exact absurd ((hk c hG).symm.trans hw) Bool.noConfusion

theorem rahmenStapelS_fremd {Sp Sp' : Speicher D} :
    ∀ {G : Σ f : D.Fn, Env D (D.params f) × World D} {st : List (RufRahmenG D)},
      RahmenStapelS P S lok Sp G st →
      (∀ F ∈ st, ∀ c ∈ stabilS P S lok F.f F.rest.2.2.1, TraegerGleich Sp' Sp c) →
        RahmenStapelS P S lok Sp' G st
  | _, [], _, _ => trivial
  | G, F :: rest, h, hS => by
      obtain ⟨hk, hf, hr⟩ := rahmenStapelS_cons.mp h
      exact rahmenStapelS_cons.mpr ⟨hk,
        fun c hc hw => traegerGleich_trans (hS F List.mem_cons_self c hc) (hf c hc hw),
        rahmenStapelS_fremd hr (fun F' hF' => hS F' (List.mem_cons_of_mem _ hF'))⟩

theorem rahmenStapelS_push {Sp Sp' : Speicher D} {F : RufRahmenG D}
    {st : List (RufRahmenG D)} (h : RahmenStapelS P S lok Sp (RufSchluesselG F) st)
    (hmem : ∀ c, TraegerSchreibt F.f c = false → TraegerGleich Sp' Sp c)
    (G : Σ f : D.Fn, Env D (D.params f) × World D)
    (hk : ∀ c, TraegerSchreibt G.1 c = true → TraegerSchreibt F.f c = true)
    (hG : ∀ c, TraegerGleich Sp' G.2.2.speicher c)
    (r : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D F.f) l Γ Λ) :
    RahmenStapelS P S lok Sp' G (⟨F.f, F.rho, F.s0, r⟩ :: st) :=
  rahmenStapelS_cons.mpr ⟨hk, fun c _ _ => hG c, rahmenStapelS_speicher h hmem⟩

theorem rahmenStapelS_pop {Sp Sp' : Speicher D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (h : RahmenStapelS P S lok Sp G (caller :: rst))
    (hmem : ∀ c, TraegerSchreibt G.1 c = false → TraegerGleich Sp' Sp c) :
    RahmenStapelS P S lok Sp' (RufSchluesselG caller) rst := by
  obtain ⟨hk, _, hr⟩ := rahmenStapelS_cons.mp h
  refine rahmenStapelS_speicher hr (fun c hw => hmem c ?_)
  cases hG : TraegerSchreibt G.1 c with
  | false => rfl
  | true => exact absurd ((hk c hG).symm.trans hw) Bool.noConfusion

/-- The suspended frame's agreement at a return world over the same
    memory. -/
theorem gleichOhne_of_stapelS {Sp : Speicher D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D} {F : RufRahmenG D}
    {rest : List (RufRahmenG D)} (h : RahmenStapelS P S lok Sp G (F :: rest)) (s1 : World D)
    (hs1 : s1.slots = Sp.slots ∧ s1.globs = Sp.globs) :
    GleichOhne G.1 (stabilS P S lok F.f F.rest.2.2.1) G.2.2 s1 := by
  obtain ⟨_, hf, _⟩ := rahmenStapelS_cons.mp h
  refine ⟨fun t ht hw => ?_, fun x hx hw => ?_⟩
  · have e : Sp.slots t = G.2.2.slots t := hf (.inl t) ht hw
    rw [hs1.1]
    exact e.symm
  · have e : Sp.globs x = G.2.2.globs x := hf (.inr x) hx hw
    rw [hs1.2]
    exact e.symm

end StapelL

section Maschine

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}

set_option maxHeartbeats 1000000 in
/-- **The acting thread keeps its frame invariant** (as
    `rahmenStapel_akteur`). -/
theorem rahmenStapelS_akteur (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (h : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) :
    RahmenStapelS P S lok M'.speicher (RufSchluesselG (M'.faeden u).kopf) (M'.faeden u).stapel := by
  have hmem : ∀ c, TraegerSchreibt (M.faeden u).kopf.f c = false →
      TraegerGleich M'.speicher M.speicher c :=
    fun c hc => schritt_traeger hO hs c (Or.inr hc)
  cases hs with
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0
    simp only [rufUpdateG_self]
    exact rahmenStapelS_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0
    simp only [rufUpdateG_self]
    exact rahmenStapelS_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0
    simp only [rufUpdateG_self]
    exact rahmenStapelS_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    subst hs0
    simp only [rufUpdateG_self]
    exact rahmenStapelS_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hg
    simp only [rufUpdateG_self]
    exact rahmenStapelS_push h hmem _ (traegerSchreibt_passt (g := g) hp)
      (fun c => by cases c <;> rfl) _
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hg
    simp only [rufUpdateG_self]
    exact rahmenStapelS_push h hmem _ (traegerSchreibt_passt (g := g) hp)
      (fun c => by cases c <;> rfl) _
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
    subst hs0 hg
    simp only [rufUpdateG_self]
    exact rahmenStapelS_push h hmem _ (traegerSchreibt_passt (g := g) hp)
      (fun c => by cases c <;> rfl) _
  -- pops
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
      hneu hnw =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
      hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapelS_pop (G := RufSchluesselG (M.faeden u).kopf) (caller := caller) h hmem
  -- every other rule keeps the stack and the head's key
  | _ =>
    simp only [rufUpdateG_self]
    exact rahmenStapelS_speicher h hmem

/-- **Another thread's step keeps the frame invariant** (every stable
    carrier of every suspended frame is left alone, `stabilS_rely`). -/
theorem rahmenStapelS_andere (hO : GutO O) (hS : SperrInvOk S)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hlok : LokOk P O passes lok sp init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (h : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden t).kopf) (M.faeden t).stapel) :
    RahmenStapelS P S lok M'.speicher (RufSchluesselG (M'.faeden t).kopf) (M'.faeden t).stapel := by
  rw [rufSchrittG_fremd hs t htu]
  exact rahmenStapelS_fremd h (fun F hF c hc =>
    stabilS_rely hO hS sp init hex hlok hr hs t htu F (List.mem_cons_of_mem _ hF) c hc)

/-- **CALLEES RESPECT THEIR FRAMES ON G, over stable carriers
    (`rufG_rahmenS`).** On every reachable machine, for every suspended frame
    `F` waiting for a callee `g` entered at `s0`: live memory agrees with
    `s0` on every stable carrier of `F` (at its holdings) that `g` does not
    declare as written. Premises: `GutO`, a well-formed lock-invariant
    family, the local carriers left alone by other threads (`LokOk`), the
    exclusive start. No footprint check is needed: stability is by the held
    locks themselves. -/
theorem rufG_rahmenS (hO : GutO O) (hS : SperrInvOk S)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hlok : LokOk P O passes lok sp init)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    RahmenInvS P S lok M := by
  induction hr with
  | start =>
      intro t
      show RahmenStapelS P S lok sp _ ((RufStartG P sp init).faeden t).stapel
      have e : ((RufStartG P sp init).faeden t).stapel = [] := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).stapel = []
        cases init t
        rfl
      rw [e]
      trivial
  | schritt M M' u hr' hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact rahmenStapelS_akteur hO hs (ih t)
      · exact rahmenStapelS_andere hO hS sp init hex hlok hr' hs t htu (ih t)

end Maschine

/-! ## 3. The steps that release a lock -/

section Freigabe

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **How one step moves the held locks of the acting thread, with the
    releasing rules named**: the held set stays or grows (every rule but
    three), or the head is a release marker `frei L` (`freiGib`), or a
    `leave`/`next` leaves a `locks` body (`peelFreiLeave`, `peelFreiNext`)
    -- and then memory is untouched and exactly one entry of `L` leaves the
    held set. -/
theorem freigabe_schrittG (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') :
    (∀ L, L ∈ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur) ∨
    (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (L : D.Lock)
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (ρ : Env D Γ),
      (M.faeden u).kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩ ∧
      M'.speicher = M.speicher ∧
      offen (M'.faeden u).spur = (offen (M.faeden u).spur).erase L) ∨
    (∃ (Γ : Ctx) (Λ Λ1 : List (Res D)) (L : D.Lock)
      (rest : Block D (vertragVon D (M.faeden u).kopf.f) true Γ Λ (Res.held L :: Λ1))
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ1) (ρ : Env D Γ) (h : true = true)
      (x : Bool),
      (M.faeden u).kopf.rest =
        ⟨true, Γ, Λ, ρ, .dann (.cons (if x then .leave h else .next h) rest) (.frei L k)⟩ ∧
      M'.speicher = M.speicher ∧
      offen (M'.faeden u).spur = (offen (M.faeden u).spur).erase L) := by
  have hgross : ∀ {a b : List D.Lock}, a = b → ∀ L, L ∈ b → L ∈ a := fun e L h => e ▸ h
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (hgross (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inl (hgross (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
  | dannLocks l Γ Λ Λ'' L _ _ _ _ _ _ _ _ hfrei =>
      simp only [rufUpdateG_self]
      exact Or.inl fun K hK => List.mem_cons_of_mem _ hK
  | freiGib l Γ Λ L k ρ hhead =>
      refine Or.inr (Or.inl ⟨l, Γ, Λ, L, k, ρ, hhead, rfl, ?_⟩)
      simp only [rufUpdateG_self]
      rfl
  | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
      refine Or.inr (Or.inr ⟨Γ, Λ, _, L, rest, k, ρ, hl, true, hhead, rfl, ?_⟩)
      simp only [rufUpdateG_self]
      rfl
  | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
      refine Or.inr (Or.inr ⟨Γ, Λ, _, L, rest, k, ρ, hl, false, hhead, rfl, ?_⟩)
      simp only [rufUpdateG_self]
      rfl
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [hs₁, lese_offen, leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [hs₂, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | _ =>
      subst_vars
      simp only [rufUpdateG_self]
      refine Or.inl (hgross ?_)
      first
        | exact trivial
        | rfl
        | exact lese_offen _ _ _

end Freigabe

/-! ## 4. The invariant of every free lock holds in the machine -/

/-- **The machine lock invariant**: every lock that no thread holds has its
    invariant at the live memory. -/
def SperrInvG (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ L : D.Lock, (∀ t : Faden, L ∉ offen (M.faeden t).spur) → S.inv L M.speicher = true

theorem sperrInvG_start (P : Programm D) (S : SperrInv D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hsp : ∀ L, S.inv L sp = true) :
    SperrInvG S (RufStartG P sp init) :=
  fun L _ => hsp L

section SperrInvG

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}

/-- **A step keeps the machine lock invariant**, given that every lock the
    step releases has its invariant at the new memory (the replay's side,
    `ZielOrtSperre.lean`). A lock free before the step keeps its protected
    carriers (every write needs all guards of its carrier held), so its
    invariant stays; a lock that becomes free was held by the acting thread
    alone and is released by the step. -/
theorem sperrInvG_schritt (hO : GutO O) (hS : SperrInvOk S) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') (hSG : SperrInvG S M)
    (hfrei : ∀ L, L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur →
      S.inv L M'.speicher = true) :
    SperrInvG S M' := by
  intro L hL
  by_cases hM : ∀ t, L ∉ offen (M.faeden t).spur
  · -- free before: its protected carriers are untouched
    rw [← hSG L hM]
    refine hS.2 L _ _ fun c hc => ?_
    exact schritt_traeger hO hs c (Or.inl ⟨L, hS.1 L c hc, hM u⟩)
  · -- held before by some thread: it can only be the acting thread
    have ⟨t, ht⟩ : ∃ t, L ∈ offen (M.faeden t).spur := by
      refine Classical.byContradiction fun hn => hM fun t ht => hn ⟨t, ht⟩
    by_cases htu : t = u
    · subst htu
      exact hfrei L ht (hL t)
    · exact absurd (by rw [rufSchrittG_fremd hs t htu]; exact ht) (hL t)

end SperrInvG

#print axioms Gabbro.Grammatik.stabilS_rely
#print axioms Gabbro.Grammatik.rufG_rahmenS
#print axioms Gabbro.Grammatik.freigabe_schrittG
#print axioms Gabbro.Grammatik.sperrInvG_schritt

end Gabbro.Grammatik
