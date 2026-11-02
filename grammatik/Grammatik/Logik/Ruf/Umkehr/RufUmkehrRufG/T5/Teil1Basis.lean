module

public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T4

@[expose] public section



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
end Gabbro.Grammatik
