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

namespace Zeuge

/-- The library's logic against the open-world rely: it has no global, so nothing is shared. -/
theorem hLO : LogikPflichtA libP (SperrInv.leer libD) (axWahr libD) OffenA :=
  logikPflichtA_of_frei (fun _ _ _ h => by obtain ⟨⟨g, _⟩, _⟩ := h; exact nomatch g)
    (logikPflicht_ohne (fs := [()]) (fun _ => List.mem_singleton.mpr rfl) (fun _ => rfl) (fun _ => rfl)
      rfl (by decide))

/-- The program's memory at the start: every slot `0`. -/
def sp0 : Speicher appD where
  slots := fun _ _ _ => (⟨0, by decide, by decide⟩ : Zahl 0 10)
  globs := fun g => nomatch g

/-- The program as a project owning the image of the library. -/
def pBild : Projekt appD where
  eigen := fun b => b
  E := { P := appP, S := SperrInv.leer appD, Q := axWahr appD, starts := [], sp0 := sp0 }

theorem hUO : E.Uebernahme hZ hS libP (SperrInv.leer libD) (axWahr libD) OffenA
    pBild.E.P pBild.E.S pBild.E.Q OffenA where
  fort := hU.fort
  orte := fun L => nomatch L
  inv := fun L => nomatch L
  atom := fun _ h => E.offenA_E h
  ax := fun a => nomatch a
  invBild := fun i => nomatch i
  rueck := hU.rueck

/-- **The witness**: the library's part of (b) in the linking program, from its proof over its
    own declaration. -/
theorem nutzerTeil_zeuge : NutzerTeilO pBild :=
  E.nutzerTeilO_E hZ hS hLO pBild hUO (Einbettung.padOk_tab (D := libD) ())
    (fun f' hf' => ⟨(), by cases f' <;> simp_all [pBild]; rfl⟩)
    (fun _ _ _ _ => rfl) axEnsLokal_wahr ⟨(fun L => nomatch L), fun _ h => by cases h⟩

#print axioms nutzerTeil_zeuge

end Zeuge

end Gabbro.Grammatik.Einbettung
