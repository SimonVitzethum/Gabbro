import Grammatik.Zielsatz.Einbettung.Zeuge
import Grammatik.Zielsatz.Projekte.Komposition

/-!
  File:      Grammatik/Zielsatz/Einbettung/Projekt.lean
  Subject:   **A project's part of (b) from its proof over its own declaration** (stage E3, the
             link to `gabbro_ziel_projekte`).

  `gabbro_ziel_projekte` takes, for every project of a program, its `NutzerTeilO` over the link
  declaration. With the embedding theorem a project proves its logic once, over its OWN
  declaration, against the open-world rely; `nutzerTeilO_E` gives its `NutzerTeilO` in every
  program that links it through an embedding and keeps what it declared. The open-world rely
  needs no condition: on the image it is no larger than the project's (`offenA_E`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

/-- **The open-world rely of the program is no larger on the image than the project's.** -/
theorem offenA_E {c : D.Tab ⊕ D.Glob} (h : OffenA (E.ortE c)) : OffenA c := by
  obtain ⟨⟨g', hg', hat⟩, hb⟩ := h
  rcases c with t | g
  · simp only [ortE, Sum.map_inl, reduceCtorEq] at hg'
  · simp only [ortE, Sum.map_inr, Sum.inr.injEq] at hg'
    subst hg'
    refine ⟨⟨g, rfl, by rw [← E.atomar]; exact hat⟩, fun L hL => hb (E.lock L) ?_⟩
    show Sum.inl (E.lock L) ∈ D'.gbraucht (E.glob g)
    rw [E.gbraucht]
    exact List.mem_map_of_mem (f := Sum.map E.lock (Prod.map E.marke _root_.id)) hL

/-- **The start of a project's own unit carries over** (L4): the invariants of the image locks hold
    at the program's initial memory when its restriction is the project's own initial memory, and the
    `requires` of the images of the project's starts hold there when they held at the project's. -/
theorem startTeil_E (hZ : E.Rueck) (hS : E.SigTreu) {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    (p : Projekt D') (hU : E.Uebernahme hZ hS P S Q OffenA p.E.P p.E.S p.E.Q OffenA)
    (sp0 : Speicher D) (starts : List (Σ w : D.Fn, Env D (D.params w)))
    (hLS : ∀ L, S.inv L sp0 = true) (hLR : ∀ a ∈ starts, ReqAmEintritt P a.1 (sp0.welt []) a.2)
    (hsp : E.speicherZ hZ p.E.sp0 = sp0)
    (hst : p.E.starts ++ p.E.gestartet =
      starts.map (fun a => (⟨E.fn a.1, E.paramsUm hS a.1 a.2⟩ : Σ w : D'.Fn, Env D' (D'.params w))))
    (hsperr : ∀ L', p.sperren L' = true → ∃ L, E.lock L = L') : StartTeil p := by
  refine ⟨fun L' hL' => ?_, fun a' ha' => ?_⟩
  · obtain ⟨L, rfl⟩ := hsperr L' hL'
    rw [hU.inv, hsp]
    exact hLS L
  · rw [hst] at ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    unfold ReqAmEintritt
    have ht : E.Treu hZ (sp0.welt []).speicher (p.E.sp0.welt []) := by
      have := E.treu_speicherZ hZ (p.E.sp0.welt [])
      rw [speicher_welt_speicher, hsp] at this
      rw [speicher_welt_speicher]
      exact this
    exact (E.req_E hZ hS hU.fort ht a.1 a.2 _
      ((E.envR_um hZ (paramsE hS a.1) _ _).mpr (E.envR_envE hZ a.2))).trans (hLR a ha)

/-- **A project's `NutzerTeilO` in a linking program, from its proof over its own declaration**:
    its logic (open-world rely) and its own start -- its lock invariants at its own initial memory and
    its starts' `requires` -- carry over; the program's initial memory restricts to the project's. -/
theorem nutzerTeilO_E [DecidableEq D'.Fn] (hZ : E.Rueck) (hS : E.SigTreu) {P : Programm D}
    {S : SperrInv D} {Q : AxEns D} (hL : LogikPflichtA P S Q OffenA) (p : Projekt D')
    (hU : E.Uebernahme hZ hS P S Q OffenA p.E.P p.E.S p.E.Q OffenA) {pad : List (Ereignis D)}
    (hp : PadOk pad) (heigen : ∀ f', p.eigen f' = true → ∃ f, E.fn f = f')
    (hSL : SperrInvLokal p.E.S) (hQL : AxEnsLokal p.E.Q)
    (sp0 : Speicher D) (starts : List (Σ w : D.Fn, Env D (D.params w)))
    (hLS : ∀ L, S.inv L sp0 = true) (hLR : ∀ a ∈ starts, ReqAmEintritt P a.1 (sp0.welt []) a.2)
    (hsp : E.speicherZ hZ p.E.sp0 = sp0)
    (hst : p.E.starts ++ p.E.gestartet =
      starts.map (fun a => (⟨E.fn a.1, E.paramsUm hS a.1 a.2⟩ : Σ w : D'.Fn, Env D' (D'.params w))))
    (hsperr : ∀ L', p.sperren L' = true → ∃ L, E.lock L = L') :
    NutzerTeilO p :=
  ⟨⟨fun passes f' hf' => by
      obtain ⟨f, rfl⟩ := heigen f' hf'
      exact E.logikPflicht_E hZ hS hU hp hL passes f, hSL, hQL⟩,
    E.startTeil_E hZ hS p hU sp0 starts hLS hLR hsp hst hsperr⟩

end Einbettung

/-! ## The witness, for every library -/

variable (D : Deklaration) (g₀ : D.Fn) [DecidableEq D.Fn] (hA : Einbettung.AntwortFrei D)

instance : DecidableEq (erweitert D g₀).Fn := inferInstanceAs (DecidableEq (D.Fn ⊕ Unit))

/-- **The extension as a project owning the image of the library**: the extended program, the
    library's lock and axiom families on the restriction, the images of the library's starts, started
    in `sp0'`. -/
def projektE (P : Programm D) (S : SperrInv D) (Q : AxEns D) (starts : List (Σ w : D.Fn, Env D (D.params w)))
    (sp0' : Speicher (erweitert D g₀)) : Projekt (erweitert D g₀) where
  eigen := fun f => f.isLeft
  sperren := fun _ => true
  E :=
    { P := programmE D g₀ P
      S := sperrE D g₀ hA S
      Q := axE D g₀ hA Q
      starts := starts.map fun a =>
        (⟨(einE D g₀).fn a.1, (einE D g₀).paramsUm (sigTreu_einE D g₀) a.1 a.2⟩ :
          Σ w : (erweitert D g₀).Fn, Env (erweitert D g₀) ((erweitert D g₀).params w))
      sp0 := sp0' }

/-- **The witness**: every library proved against the open-world rely, with lock invariants and axiom
    ensures that read only their carriers, its lock invariants at its own initial memory and its starts'
    `requires` there, has its part of (b) in the program that adds a callback -- started in any memory
    that restricts to the library's. -/
theorem nutzerTeil_zeuge {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    (hL : LogikPflichtA P S Q OffenA) (hSL : SperrInvLokal S) (hQL : AxEnsLokal Q)
    {pad : List (Ereignis D)} (hp : Einbettung.PadOk pad)
    (sp0 : Speicher D) (starts : List (Σ w : D.Fn, Env D (D.params w)))
    (hLS : ∀ L, S.inv L sp0 = true) (hLR : ∀ a ∈ starts, ReqAmEintritt P a.1 (sp0.welt []) a.2)
    (sp0' : Speicher (erweitert D g₀)) (hsp : (einE D g₀).speicherZ (rueckE D g₀ hA) sp0' = sp0) :
    NutzerTeilO (projektE D g₀ hA P S Q starts sp0') :=
  (einE D g₀).nutzerTeilO_E (rueckE D g₀ hA) (sigTreu_einE D g₀) hL (projektE D g₀ hA P S Q starts sp0')
    (uebernahmeE D g₀ hA P S Q OffenA OffenA (fun _ h => (einE D g₀).offenA_E h)) hp
    (fun f' hf' => by
      cases f' with
      | inl f => exact ⟨f, rfl⟩
      | inr _ => cases hf')
    (sperrE_lokal D g₀ hA hSL) (axE_lokal D g₀ hA hQL) sp0 starts hLS hLR hsp
    (List.append_nil _) (fun L' _ => ⟨L', rfl⟩)

#print axioms nutzerTeil_zeuge

end Gabbro.Grammatik.Einbettung
