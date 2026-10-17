/- Part 5 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.RufUmkehrRufG.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Kette

variable (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (n : Nat)
  (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D) (S : REnde (vertragVon D fn))

theorem wartend_of_wartet {F : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    {restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ'} {k : GRest D (vertragVon D F.f) l Γ Λ'}
    {ρc : Env D Γ} (hc : F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) : F.wartend = true := by
  unfold RufRahmenG.wartend
  rw [hc]
  rfl

/-- The demand the pending call chain `unten` (top first, ending with the
    frame of `fn`) makes on the result of a frame of `g` directly above it. -/
inductive Anspruch : List (RufRahmenG D) → (g : D.Fn) → REnde (vertragVon D g) → Prop
  | basis (res : REnde (vertragVon D fn)) (h : res.gleich S) : Anspruch [] fn res
  | sonst (unten : List (RufRahmenG D)) (g : D.Fn) : Anspruch unten g .sonst
  | wie (F : RufRahmenG D) (unten : List (RufRahmenG D)) (g : D.Fn) (σ1 : World D)
      (v1 : ErgVal D (D.erg g)) (hnw : F.wartend = false)
      (h : Anspruch unten F.f (semK O passes (rufRumpf P O passes (n - unten.length))
        F.rest.2.2.2.2 σ1 F.rest.2.2.2.1)) :
      Anspruch (F :: unten) g (.zurueck σ1 v1)
  | bind (F : RufRahmenG D) (unten : List (RufRahmenG D)) (g : D.Fn) (σ1 : World D)
      (v1 : ErgVal D (D.erg g)) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ)
      (hc : F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg g = some τ)
      (h : Anspruch unten F.f (semK O passes (rufRumpf P O passes (n - unten.length))
        (.dann restb (.schrumpf k)) σ1 (.cons (ergWert he v1) ρc))) :
      Anspruch (F :: unten) g (.zurueck σ1 v1)

/-- A frame waiting in the chain, covered at its depth `d`: plainly (it
    advanced past the call) or waiting for a bound value. -/
def FrameK (d : Nat) (F : RufRahmenG D) : Prop :=
  (F.wartend = false ∧ RestK A (TiefK P A d) F.rest.2.2.2.2) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
      F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∧ RestK A (TiefK P A d) (.dann restb (.schrumpf k)))

/-- The chain below the top: every frame covered at its depth; the bottom
    one is the frame of `fn` (its key). -/
inductive KetteOk : List (RufRahmenG D) → Prop
  | nil : KetteOk []
  | cons (F : RufRahmenG D) (unten : List (RufRahmenG D))
      (hF : FrameK P A (n - unten.length) F)
      (hkey : unten = [] → RufSchluesselG F = ⟨fn, rho, s0⟩) (h : KetteOk unten) :
      KetteOk (F :: unten)

/-- The top frame: covered at its depth, its frame result meets the demand
    of the chain below, and it is the frame of `fn` if the chain is empty. -/
def TopOk (unten : List (RufRahmenG D)) (T : RufRahmenG D) (σ : World D) : Prop :=
  RestK A (TiefK P A (n - unten.length)) T.rest.2.2.2.2 ∧
  Anspruch P O passes n fn S unten T.f
    (semK O passes (rufRumpf P O passes (n - unten.length)) T.rest.2.2.2.2 σ T.rest.2.2.2.1) ∧
  (unten = [] → RufSchluesselG T = ⟨fn, rho, s0⟩)

/-- **The run invariant of the converse with calls**: the frame of `fn` is on
    the stack of thread `f` above `caller :: rst`, the frames above it form
    a well-formed pending call chain, and the log grew from `log`. -/
def InvK (f : Faden) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (log : List (RufEreignisF D)) (M : RufMaschineG D) : Prop :=
  ∃ (unten : List (RufRahmenG D)) (ext : List (RufEreignisF D)),
    (M.faeden f).stapel = unten ++ caller :: rst ∧ (M.faeden f).log = ext ++ log ∧
    KetteOk P A n fn rho s0 unten ∧ TopOk P O passes A n fn rho s0 S unten (M.faeden f).kopf (M.weltVon f)

/-- The demand only sees results up to the trace. -/
theorem anspruch_gleich : ∀ {unten : List (RufRahmenG D)} {g : D.Fn} {res res' : REnde (vertragVon D g)},
    KetteOk P A n fn rho s0 unten → Anspruch P O passes n fn S unten g res → res.gleich res' →
    Anspruch P O passes n fn S unten g res' := by
  intro unten g res res' hK h hg
  induction h with
  | basis res hS =>
    exact Anspruch.basis res' (REnde.gleich_trans (REnde.gleich_symm hg) hS)
  | sonst unten g =>
    cases res' with
    | sonst => exact Anspruch.sonst unten g
    | zurueck => exact hg.elim
  | wie F unten g σ1 v1 hnw h ih =>
    cases res' with
    | sonst => exact hg.elim
    | zurueck σ2 v2 =>
      obtain ⟨hs, rfl⟩ := hg
      cases hK with
      | cons _ _ hF hkey hK' =>
        rcases hF with ⟨_, hcov⟩ | ⟨_, _, _, _, _, _, _, _, hc, _⟩
        · refine Anspruch.wie F unten g σ2 v1 hnw (ih hK' ?_)
          exact semK_SG O passes _ A (TiefK P A (n - unten.length))
            (rufRumpf_SG P O passes A _) _ hcov σ1 σ2 _ hs
        · rw [wartend_of_wartet hc] at hnw
          cases hnw
  | bind F unten g σ1 v1 restb k ρc hc he h ih =>
    cases res' with
    | sonst => exact hg.elim
    | zurueck σ2 v2 =>
      obtain ⟨hs, rfl⟩ := hg
      cases hK with
      | cons _ _ hF hkey hK' =>
        rcases hF with ⟨hnw, _⟩ | ⟨_, _, _, _, _, restb', k', ρc', hc', hcov⟩
        · rw [wartend_of_wartet hc] at hnw
          cases hnw
        · rw [hc] at hc'
          cases hc'
          refine Anspruch.bind F unten g σ2 v1 restb k ρc hc he (ih hK' ?_)
          exact semK_SG O passes _ A (TiefK P A (n - unten.length))
            (rufRumpf_SG P O passes A _) _ hcov σ1 σ2 _ hs

/-- The demand at the bottom: agreement with `S`. -/
theorem anspruch_nil {g : D.Fn} {res : REnde (vertragVon D g)}
    (h : Anspruch P O passes n fn S [] g res) :
    res = .sonst ∨ ∃ hg : g = fn, (hg ▸ res).gleich S := by
  cases h with
  | basis _ hS => exact Or.inr ⟨rfl, hS⟩
  | sonst => exact Or.inl rfl

/-- The demand on a return, one frame up: how the frame below resumes. -/
theorem anspruch_cons {F : RufRahmenG D} {unten : List (RufRahmenG D)} {g : D.Fn}
    {σ1 : World D} {v1 : ErgVal D (D.erg g)}
    (h : Anspruch P O passes n fn S (F :: unten) g (.zurueck σ1 v1)) :
    (F.wartend = false ∧ Anspruch P O passes n fn S unten F.f
      (semK O passes (rufRumpf P O passes (n - unten.length)) F.rest.2.2.2.2 σ1
        F.rest.2.2.2.1)) ∨
    (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ)
      (_ : F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg g = some τ),
      Anspruch P O passes n fn S unten F.f
        (semK O passes (rufRumpf P O passes (n - unten.length)) (.dann restb (.schrumpf k)) σ1
          (.cons (ergWert he v1) ρc))) := by
  cases h with
  | wie _ _ _ _ _ hnw h => exact Or.inl ⟨hnw, h⟩
  | bind _ _ _ _ _ restb k ρc hc he h => exact Or.inr ⟨_, _, _, _, _, restb, k, ρc, hc, he, h⟩

/-- The bottom frame pops: its logged value agrees with `S`. -/
theorem schluss_basis {T : RufRahmenG D} (hkey : RufSchluesselG T = ⟨fn, rho, s0⟩)
    {res : REnde (vertragVon D T.f)} (han : Anspruch P O passes n fn S [] T.f res)
    (v : ErgVal D (D.erg T.f)) (s1 : World D) (hg : res.gleich (.zurueck s1 v)) :
    ∃ v' : ErgVal D (D.erg fn), RufEreignisF.rueck T.f T.rho v T.s0 s1 =
      RufEreignisF.rueck fn rho v' s0 s1 ∧ (REnde.zurueck (V := vertragVon D fn) s1 v').gleich S := by
  obtain ⟨Tf, Trho, Ts0, Trest⟩ := T
  simp only [RufSchluesselG, Sigma.mk.injEq] at hkey
  obtain ⟨rfl, h2⟩ := hkey
  have h3 : (Trho, Ts0) = (rho, s0) := eq_of_heq h2
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hres := anspruch_gleich P O passes (fun _ => True) n Tf Trho Ts0 S KetteOk.nil han hg
  rcases anspruch_nil P O passes n Tf S hres with h | ⟨_, hS⟩
  · cases h
  · exact ⟨v, rfl, hS⟩

end Kette
/-! ## 6. Every step keeps the chain; the first pop of the frame -/

section Lauf

variable (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (n : Nat)
  (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D) (S : REnde (vertragVon D fn))
  (f : Faden) (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (log : List (RufEreignisF D))

/-- The frame of `fn` has been popped: thread `f` is back at the caller's
    stack `rst`, and its log carries the frame's return with a value and a
    world that agree with `S`. -/
def GepopptK (M : RufMaschineG D) : Prop :=
  ∃ (v : ErgVal D (D.erg fn)) (s1 : World D) (ext : List (RufEreignisF D)),
    (M.faeden f).stapel = rst ∧
    (M.faeden f).log = RufEreignisF.rueck fn rho v s0 s1 :: (ext ++ log) ∧
    (REnde.zurueck (V := vertragVon D fn) s1 v).gleich S

/-- **One step keeps the pending call chain**, or it is the pop of the frame
    of `fn` itself -- with the value `S` demands. -/
theorem invK_schritt {M M' : RufMaschineG D} (hs : RufSchrittG P O passes M f M')
    (h : InvK P O passes A n fn rho s0 S f caller rst log M) :
    InvK P O passes A n fn rho s0 S f caller rst log M' ∨ GepopptK fn rho s0 S f rst log M' := by
  obtain ⟨unten, ext, hst, hlog, hK, hcovT, hanT, hkeyT⟩ := h
  rcases hT : (M.faeden f).kopf.rest with ⟨lT, ΓT, ΛT, ρT, rT⟩
  rw [hT] at hcovT hanT
  rcases schrittErhaltK (rufRumpf_SG P O passes A (n - unten.length)) hs (M.faeden f) rfl ρT rT hT
      hcovT with
    ⟨l', Γ', Λ', ρ', r', sp, hM', hcov', hsem⟩ |
    ⟨v, s1, caller', neu, rst', hpop, hwa, hM', hsp', hsem⟩ |
    ⟨g, rhoG, σc, Fw, hC, hM', hsp', hwk⟩
  · -- the frame stays on top
    left
    refine ⟨unten, ext, by rw [hM']; exact hst, by rw [hM']; exact hlog, hK, ?_, ?_, ?_⟩
    · rw [hM']
      exact hcov'
    · rw [hM']
      exact anspruch_gleich P O passes A n fn rho s0 S hK hanT (REnde.gleich_symm hsem)
    · intro hu
      rw [hM']
      exact hkeyT hu
  · -- a pop
    have hW' : M'.weltVon f = s1 := by
      unfold RufMaschineG.weltVon
      rw [hsp', hM']
      exact Speicher.welt_speicher s1
    cases unten with
    | nil =>
      right
      rw [hst] at hpop
      simp only [List.nil_append, List.cons.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      obtain ⟨v', he, hS⟩ := schluss_basis P O passes n fn rho s0 S (hkeyT rfl) hanT v s1 hsem
      refine ⟨v', s1, ext, by rw [hM'], ?_, hS⟩
      rw [hM', hlog, he]
    | cons F unten' =>
      left
      rw [hst] at hpop
      simp only [List.cons_append, List.cons.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      cases hK with
      | cons _ _ hF hkey hK' =>
      have hres := anspruch_gleich P O passes A n fn rho s0 S (KetteOk.cons F unten' hF hkey hK')
        hanT hsem
      refine ⟨unten', RufEreignisF.rueck _ _ v _ s1 :: ext, by rw [hM'],
        by rw [hM', hlog]; rfl, hK', ?_⟩
      rcases anspruch_cons P O passes n fn S hres with
        ⟨hnw, han'⟩ | ⟨l, Γ, Λ, Λ', τ, restb, k, ρc, hc, he, han'⟩
      · cases hwa with
        | wie _ =>
          refine ⟨?_, ?_, ?_⟩
          · rw [hM']
            rcases hF with ⟨_, hcov⟩ | ⟨_, _, _, _, _, _, _, _, hc0, _⟩
            · exact hcov
            · rw [wartend_of_wartet hc0] at hnw
              cases hnw
          · rw [hM', hW']
            exact han'
          · intro hu
            rw [hM']
            exact hkey hu
        | bind restb' k' ρc' hc' he' =>
          rw [wartend_of_wartet hc'] at hnw
          cases hnw
        | bindSonst n' err restb' k' ρc' hc' he' =>
          have hw1 : F.wartend = true := by
            unfold RufRahmenG.wartend
            rw [hc']
            rfl
          rw [hw1] at hnw
          cases hnw
      · cases hwa with
        | wie hnw' =>
          rw [wartend_of_wartet hc] at hnw'
          cases hnw'
        | bind restb' k' ρc' hc' he' =>
          rw [hc] at hc'
          cases hc'
          refine ⟨?_, ?_, ?_⟩
          · rw [hM']
            rcases hF with ⟨hnw0, _⟩ | ⟨_, _, _, _, _, restb0, k0, ρc0, hc0, hcov0⟩
            · rw [wartend_of_wartet hc] at hnw0
              cases hnw0
            · rw [hc] at hc0
              cases hc0
              exact hcov0
          · rw [hM', hW']
            exact han'
          · intro hu
            rw [hM']
            exact hkey hu
        | bindSonst n' err restb' k' ρc' hc' he' =>
          rw [hc] at hc'
          cases hc'
  · -- a push
    left
    have hW' : M'.weltVon f = σc := by
      unfold RufMaschineG.weltVon
      rw [hsp', hM']
      exact Speicher.welt_speicher σc
    have hd : ∃ d', n - unten.length = d' + 1 := by
      cases hdd : n - unten.length with
      | zero =>
        rw [hdd] at hC
        exact hC.elim
      | succ d' => exact ⟨d', rfl⟩
    obtain ⟨d', hd⟩ := hd
    have hC' : TiefK P A (d' + 1) g := by rw [← hd]; exact hC
    obtain ⟨hbody, hko⟩ := hC'
    have hlen : n - (Fw :: unten).length = d' := by
      simp only [List.length_cons]
      omega
    have hFrame : FrameK P A (n - unten.length) Fw := by
      rcases hwk with ⟨l', Γ', Λ', ρ', rw, hFw, hnw, hcovw, _⟩ |
        ⟨l', Γ', Λ', Λ'', τ, ρ', restb, k, he, hFw, hcovw, _⟩
      · subst hFw
        exact Or.inl ⟨hnw, hcovw⟩
      · subst hFw
        exact Or.inr ⟨_, _, _, _, _, restb, k, ρ', rfl, hcovw⟩
    have hkeyW : unten = [] → RufSchluesselG Fw = ⟨fn, rho, s0⟩ := by
      intro hu
      rcases hwk with ⟨_, _, _, _, _, hFw, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hFw, _⟩ <;>
        (subst hFw; exact hkeyT hu)
    refine ⟨Fw :: unten, RufEreignisF.eintritt g rhoG σc :: ext, by rw [hM', hst]; rfl,
      by rw [hM', hlog]; rfl, KetteOk.cons Fw unten hFrame hkeyW hK, ?_, ?_, ?_⟩
    · rw [hM', hlen]
      exact RestK.ende _ hbody hko
    · rw [hM', hlen, hW']
      show Anspruch P O passes n fn S (Fw :: unten) g
        (endErg (execEnd O passes (rufRumpf P O passes d') (P.rumpf g) σc rhoG))
      cases hx : execEnd O passes (rufRumpf P O passes d') (P.rumpf g) σc rhoG with
      | zurueck σ1 v1 =>
        have hR1 : rufRumpf P O passes (n - unten.length) g σc rhoG = .ok σ1 v1 := by
          rw [hd]
          simp only [rufRumpf, hx]
        rcases hwk with ⟨l', Γ', Λ', ρ', rw, hFw, hnw, _, hsemw⟩ |
          ⟨l', Γ', Λ', Λ'', τ, ρ', restb, k, he, hFw, _, hsemw⟩
        · subst hFw
          refine Anspruch.wie _ unten g σ1 v1 hnw ?_
          rw [← hsemw σ1 v1 hR1]
          exact hanT
        · subst hFw
          refine Anspruch.bind _ unten g σ1 v1 restb k ρ' rfl he ?_
          rw [← hsemw σ1 v1 hR1]
          exact hanT
      | why => exact Anspruch.sonst _ _
      | leave h' => exact absurd h' (by decide)
      | next h' => exact absurd h' (by decide)
      | logik => exact Anspruch.sonst _ _
      | hardware => exact Anspruch.sonst _ _
    · intro hu
      cases hu

end Lauf
/-- A run of thread `f` during which the stack of `f` stays longer than
    `lo` in every state that steps: with `lo` the length of the caller's
    stack, a run up to (at most) the FIRST pop of the frame above it. -/
inductive RufLaufUeber (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (lo : Nat) :
    RufMaschineG D → RufMaschineG D → Prop where
  | refl (M : RufMaschineG D) : RufLaufUeber P O passes f lo M M
  | schritt {M M' M'' : RufMaschineG D} (hh : lo < (M.faeden f).stapel.length)
      (h : RufSchrittG P O passes M f M') (hr : RufLaufUeber P O passes f lo M' M'') :
      RufLaufUeber P O passes f lo M M''

/-- Such a run is a run of thread `f`. -/
theorem RufLaufUeber.lauf {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden} {lo : Nat}
    {M M'' : RufMaschineG D} (h : RufLaufUeber P O passes f lo M M'') :
    RufLaufG P O passes f M M'' := by
  induction h with
  | refl => exact RufLaufG.refl _
  | schritt _ hs _ ih => exact RufLaufG.schritt hs ih

/-- Along a run up to the first pop, the chain is kept; at a machine whose
    stack is no longer than the caller's, the frame has been popped. -/
theorem invK_lauf (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (n : Nat)
    (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D) (S : REnde (vertragVon D fn))
    (f : Faden) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (log : List (RufEreignisF D)) {M M'' : RufMaschineG D}
    (hl : RufLaufUeber P O passes f rst.length M M'') :
    InvK P O passes A n fn rho s0 S f caller rst log M →
    (M''.faeden f).stapel.length ≤ rst.length → GepopptK fn rho s0 S f rst log M'' := by
  induction hl with
  | refl M =>
    intro h hpop
    obtain ⟨unten, _, hst, _⟩ := h
    rw [hst] at hpop
    simp only [List.length_append, List.length_cons] at hpop
    omega
  | schritt hh hs hr ih =>
    intro h hpop
    rcases invK_schritt P O passes A n fn rho s0 S f caller rst log hs h with h' | hG
    · exact ih h' hpop
    · cases hr with
      | refl => exact hG
      | schritt hh' _ _ =>
        obtain ⟨_, _, _, hst', _⟩ := hG
        rw [hst'] at hh'
        exact absurd hh' (Nat.lt_irrefl _)

/-- **The converse with calls.** Thread `f` of `M` runs a frame of `fn`
    (parameters `rho`, entry world `s0`) above `caller :: rst`, with residue
    `.ende b` for an end block `b` covered at depth `n` by the fragment of
    the converse (calls and bind-calls, callees admitted by `TiefK P A n`:
    their bodies covered one level down, and so on). If ANY run of thread
    `f` alone leads from `M` to a machine
    whose stack of `f` is no longer than the caller's, every state before
    it keeping the frame on the stack (a run up to the FIRST pop of the
    frame, `RufLaufUeber`), then the log of that machine is the old log,
    extended by the events of the calls made on the way, topped by the
    frame's return `rueck fn rho v s0 s1`; and the sequential semantics
    with the body-running handler of depth `n`, started at the thread's
    world, returns THE SAME value `v`, in a world with the memory of `s1`.

    The depth: `n` is any depth at which `b` is covered (`TiefK`), i.e. at
    least the nesting depth of the calls; the run itself is not bounded. -/
theorem rufG_adaequat_ruf_umkehr (P : Programm D) (O : Orakel D) (passes : Nat) (n : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D)
    (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (spur : List (Ereignis D))
    (log : List (RufEreignisF D)) {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (b : Endblock D (vertragVon D fn) false Γ Λ) (A : D.Lock → Prop)
    (hb : EndR A (TiefK P A n) b) (hko : b.kOk = true)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (M'' : RufMaschineG D) (hl : RufLaufUeber P O passes f rst.length M M'')
    (hpop : (M''.faeden f).stapel.length ≤ rst.length) :
    ∃ (v : ErgVal D (D.erg fn)) (s1 : World D) (ext : List (RufEreignisF D)) (σ' : World D),
      (M''.faeden f).log = RufEreignisF.rueck fn rho v s0 s1 :: (ext ++ log) ∧
      execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ = .zurueck σ' v ∧
      σ'.speicher = s1.speicher := by
  have h0 : InvK P O passes A n fn rho s0
      (endErg (execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ)) f caller rst log M := by
    refine ⟨[], [], by rw [hM]; rfl, by rw [hM]; rfl, KetteOk.nil, ?_, ?_, ?_⟩
    · rw [hM]
      exact RestK.ende b hb hko
    · rw [hM]
      exact Anspruch.basis _ (REnde.gleich_refl _)
    · intro _
      rw [hM]
      rfl
  obtain ⟨v, s1, ext, _, hlog, hS⟩ := invK_lauf P O passes A n fn rho s0 _ f caller rst log hl h0
    hpop
  revert hS
  cases hx : execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ with
  | zurueck σ' w =>
    intro hS
    obtain ⟨hsg, hvw⟩ := hS
    subst hvw
    exact ⟨v, s1, ext, σ', hlog, rfl, hsg.speicher.symm⟩
  | _ => intro hS; exact absurd hS id



/-! ## 7. Runs up to the first pop, and the witnesses -/

theorem RufLaufUeber.trans {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {lo : Nat} {M M' M'' : RufMaschineG D} (h1 : RufLaufUeber P O passes f lo M M')
    (h2 : RufLaufUeber P O passes f lo M' M'') : RufLaufUeber P O passes f lo M M'' := by
  induction h1 with
  | refl => exact h2
  | schritt hh hs _ ih => exact RufLaufUeber.schritt hh hs (ih h2)

/-- Every run of thread `f` that ends with a stack no longer than `lo`
    passes through a FIRST such machine: its prefix up to there keeps the
    stack longer than `lo` in every state that steps. -/
theorem rufLaufG_erster {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden} (lo : Nat)
    {M M'' : RufMaschineG D} (hl : RufLaufG P O passes f M M'')
    (hpop : (M''.faeden f).stapel.length ≤ lo) :
    ∃ M1, RufLaufUeber P O passes f lo M M1 ∧ (M1.faeden f).stapel.length ≤ lo ∧
      RufLaufG P O passes f M1 M'' := by
  induction hl with
  | refl M => exact ⟨M, RufLaufUeber.refl M, hpop, RufLaufG.refl M⟩
  | @schritt M M' M2 hs hr ih =>
    by_cases hM : (M.faeden f).stapel.length ≤ lo
    · exact ⟨M, RufLaufUeber.refl M, hM, RufLaufG.schritt hs hr⟩
    · obtain ⟨M1, h1, h2, h3⟩ := ih hpop
      exact ⟨M1, RufLaufUeber.schritt (by omega) hs h1, h2, h3⟩

/-- The callee of the bind witness is covered by the converse at depth 1. -/
theorem t4G_tiefK (A : t4D.Lock → Prop) : TiefK t4P A 1 t4G :=
  ⟨show EndR A (TiefK t4P A 0) t4GRumpf from
    EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _), rfl⟩

/-- The bind caller is covered by the converse at depth 1. -/
theorem t4BRumpf_K (A : t4D.Lock → Prop) : EndR A (TiefK t4P A 1) t4BRumpf :=
  EndR.cons _ _
    (StmtR.ite _ _ _
      (BlockR.bindCall _ _ _ _ _ _ (t4G_tiefK A)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      BlockR.nil)
    (EndR.ret _ _)

theorem t4BRumpf_kOk : t4BRumpf.kOk = true := rfl

/-- **Witness for `rufG_adaequat_ruf_umkehr`.** All premises jointly, on the
    bind-caller program at depth 1: the machine `t4M t4B t4BRumpf`, the
    covered body (a bind-call of the writing callee under an `if`, the
    bound value written), and the run `rufG_adaequat_ruf` produces, cut at
    its FIRST pop of the caller's frame (`rufLaufG_erster`) -- a real run
    of the machine through the push, the callee's writing leaf, the binding
    pop, the caller's writing leaf and the final pop. From the MACHINE's
    log alone the converse recovers that the sequential semantics returns
    the logged value `9`, in a world with the logged memory (slot 0 moved
    to 5 by the callee, slot 1 to 3 by the caller). -/
theorem rufG_adaequat_ruf_umkehr_zeuge :
    ∃ (M1 : RufMaschineG t4D) (v : ErgVal t4D (t4D.erg t4B)) (s1 : World t4D)
      (ext : List (RufEreignisF t4D)),
      RufLaufUeber t4P t4O 0 0 0 (t4M t4B t4BRumpf) M1 ∧ (M1.faeden 0).stapel = [] ∧
      (M1.faeden 0).log = RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) s1 :: (ext ++ []) ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 3 ∧
      ∃ σ', execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0)
          Env.nil = .zurueck σ' v ∧
        σ'.speicher = s1.speicher ∧ (show Zahl 0 100 from v).n = 9 := by
  obtain ⟨σ', v, hex, h5, h3, h9, M', ext', hl, hf, _, _⟩ := rufG_adaequat_ruf_zeuge_bind
  have hpop' : (M'.faeden 0).stapel.length ≤ ([] : List (RufRahmenG t4D)).length := by
    rw [hf]
    exact Nat.le_refl 0
  obtain ⟨M1, hu, hpop1, _⟩ := rufLaufG_erster 0 hl hpop'
  obtain ⟨v1, s1, ext, σ1, hlog, hex1, hsp⟩ := rufG_adaequat_ruf_umkehr t4P t4O 0 1
    (t4M t4B t4BRumpf) 0 t4B Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf
    (fun _ => False) (t4BRumpf_K _) t4BRumpf_kOk rfl M1 hu hpop1
  cases hex.symm.trans hex1
  have hst : (M1.faeden 0).stapel = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hs1 : s1.slots = σ'.slots := by
    have := congrArg Speicher.slots hsp
    exact this.symm
  refine ⟨M1, v, s1, ext, hu, hst, hlog, ?_, ?_, σ', hex, hsp, h9⟩
  · rw [hs1]; exact h5
  · rw [hs1]; exact h3


end Gabbro.Grammatik
