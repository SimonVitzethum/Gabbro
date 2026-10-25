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

/-- **A project's `NutzerTeilO` in a linking program, from its logic over its own declaration.**
    The project owns only image functions; its lock and axiom families in the program are local
    and its start holds there (both about the program's unit, decided or proved once). -/
theorem nutzerTeilO_E [DecidableEq D'.Fn] (hZ : E.Rueck) (hS : E.SigTreu) {P : Programm D}
    {S : SperrInv D} {Q : AxEns D} (hL : LogikPflichtA P S Q OffenA) (p : Projekt D')
    (hU : E.Uebernahme hZ hS P S Q OffenA p.E.P p.E.S p.E.Q OffenA) {pad : List (Ereignis D)}
    (hp : PadOk pad) (heigen : ∀ f', p.eigen f' = true → ∃ f, E.fn f = f')
    (hSL : SperrInvLokal p.E.S) (hQL : AxEnsLokal p.E.Q) (hstart : StartPflicht p.E) :
    NutzerTeilO p :=
  ⟨⟨fun passes f' hf' => by
      obtain ⟨f, rfl⟩ := heigen f' hf'
      exact E.logikPflicht_E hZ hS hU hp hL passes f, hSL, hQL⟩, hstart⟩

end Einbettung

/-! ## The witness, for every library -/

variable (D : Deklaration) (g₀ : D.Fn) [DecidableEq D.Fn] (hA : Einbettung.AntwortFrei D)

instance : DecidableEq (erweitert D g₀).Fn := inferInstanceAs (DecidableEq (D.Fn ⊕ Unit))

/-- **The extension as a project owning the image of the library**: the extended program, the
    library's lock and axiom families on the restriction, started in `sp0`. -/
def projektE (P : Programm D) (S : SperrInv D) (Q : AxEns D) (sp0 : Speicher (erweitert D g₀)) :
    Projekt (erweitert D g₀) where
  eigen := fun f => f.isLeft
  E := { P := programmE D g₀ P, S := sperrE D g₀ hA S, Q := axE D g₀ hA Q, starts := [], sp0 := sp0 }

/-- **The witness**: every library proved against the open-world rely, with lock invariants and axiom
    ensures that read only their carriers, has its part of (b) in the program that adds a callback --
    started in any memory whose restriction meets the library's lock invariants. -/
theorem nutzerTeil_zeuge {P : Programm D} {S : SperrInv D} {Q : AxEns D}
    (hL : LogikPflichtA P S Q OffenA) (hSL : SperrInvLokal S) (hQL : AxEnsLokal Q)
    {pad : List (Ereignis D)} (hp : Einbettung.PadOk pad) (sp0 : Speicher (erweitert D g₀))
    (hsp : ∀ L, S.inv L ((einE D g₀).speicherZ (rueckE D g₀ hA) sp0) = true) :
    NutzerTeilO (projektE D g₀ hA P S Q sp0) :=
  (einE D g₀).nutzerTeilO_E (rueckE D g₀ hA) (sigTreu_einE D g₀) hL (projektE D g₀ hA P S Q sp0)
    (uebernahmeE D g₀ hA P S Q OffenA OffenA (fun _ h => (einE D g₀).offenA_E h)) hp
    (fun f' hf' => by
      cases f' with
      | inl f => exact ⟨f, rfl⟩
      | inr _ => cases hf')
    (sperrE_lokal D g₀ hA hSL) (axE_lokal D g₀ hA hQL) ⟨hsp, fun _ h => by cases h⟩

#print axioms nutzerTeil_zeuge

end Gabbro.Grammatik.Einbettung
