module
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T5.Teil1Basis
import all Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T5.Teil1Basis

public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T4

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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

end Gabbro.Grammatik
