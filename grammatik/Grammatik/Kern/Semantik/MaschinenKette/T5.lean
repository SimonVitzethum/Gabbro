/- Part 5 of 5 of `MaschinenKette` (split by instrumente/teile/lean-teilen.py; the umbrella `MaschinenKette.lean` imports all parts). -/
import Grammatik.Kern.Semantik.MaschinenKette.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

/-- **Seed joint run J0.** The start machine as a chain by construction: empty
    thread list, constant code, generated worlds and the empty run, empty step
    list. Identifications (`welten`, `l`) and the base premises (`hempty`,
    `hcode`) hold by `rfl`. Every parameter is load-bearing: `Nb` indexes the
    run, `sp` builds worlds and entry, `fn0` builds the code. -/
def samen_J0 (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    GemeinsamerLauf (D := D) Nb :=
  { faeden := []
    code := fun _ => fn0
    eintritt := fun _ => (GenStart sp).start
    welten := (GenStart sp).welten
    schrittFaden := []
    l := (GenStart sp).lauf
    hKette := by simp [GenStart]
    hSchritt := by
      intro k f vor nach hk _ _
      simp at hk
    hPaar := by
      intro f hf
      simp at hf
    hGesittet := by
      show Gesittet ([] : Lauf D)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro f j
        have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
        rw [hsp]
        exact konsistent_nil
      · intro f j e he
        have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
        rw [hsp] at he
        simp at he
      · intro j f L h hi g hne
        simp at hi
      · intro i j f g m s s' ei ej hi hj hm hm'
        simp at hi
      · intro i j f g o ei ej hi hj ht1 ht2 hu
        simp at hi
    hBeschraenkt := by
      show BeschraenkteVerschraenkung (D := D) Nb ([] : Lauf D)
      intro i j f g ei ej hi hj hne
      simp at hi
    hEintritt := by
      intro f hf
      simp at hf
    hSchuld := by
      intro f hf
      simp at hf
    hInvSicht := by
      intro f hf
      simp at hf
  }

/-- The seed owes no thread steps: `hempty` by construction. -/
theorem samen_J0_schritt_leer (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    (samen_J0 Nb sp fn0).schrittFaden = [] := rfl

/-- The seed carries the supplied code: `hcode` by construction. -/
theorem samen_J0_code (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    (samen_J0 Nb sp fn0).code = fun _ => fn0 := rfl

/-- The seed tracks the start worlds by construction. -/
theorem samen_J0_welten (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    (samen_J0 Nb sp fn0).welten = (GenStart sp).welten := rfl

/-- The seed tracks the start run by construction. -/
theorem samen_J0_lauf (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    (samen_J0 Nb sp fn0).l = (GenStart sp).lauf := rfl

/-- The seed has no member threads by construction. -/
theorem samen_J0_faeden (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn) :
    (samen_J0 Nb sp fn0).faeden = [] := rfl

/-- Base-instantiation corollary for `hwit_leer`: the prefix witness duty at
    the seed holds vacuously over any run -- no thread steps are owed, so no
    witness is owed. The fold base is the instance at
    `run := (GenStart sp).lauf` with `hempty`/`hcode` by `rfl`. Every premise
    is load-bearing: `Nb`/`sp`/`fn0` build the seed, `run`/`t₀` type the
    conclusion. -/
theorem samen_J0_hwit_base (Nb : Nebeneinander) (sp : Speicher D) (fn0 : D.Fn)
    (run : Lauf D) (t₀ : D.Tab) :
    ∀ (k : Nat) (g : Faden),
      (samen_J0 Nb sp fn0).schrittFaden[k]? = some g →
      TraegerSchreibt ((samen_J0 Nb sp fn0).code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  intro k g hk _
  have hempty : (samen_J0 Nb sp fn0).schrittFaden = [] := rfl
  rw [hempty] at hk
  simp at hk

#print axioms Gabbro.Grammatik.samen_J0
#print axioms Gabbro.Grammatik.samen_J0_hwit_base

end Gabbro.Grammatik

/-! ## Fold instance at the seed J0: the fold and the seed meet.

    `Extraktion.hwit_alt_faltung` takes its base from a posited empty joint run
    `J₀` (`hempty : J₀.schrittFaden = []`, `hcode : J₀.code = code`); the seed
    `samen_J0` above constructs that run, so both premises close by `rfl`
    (`samen_J0_schritt_leer`, `samen_J0_code`), narrowing the code to
    `fun _ => fn0`, and the vacuous base is `samen_J0_hwit_base`. This section
    wires the two: the fold at `J₀ := samen_J0 Nb sp fn0`, yielding the
    instantiated prefix duty over whole `PCReach` runs, ready for consumers.
    Every premise is load-bearing (each feeds the fold it instantiates); there
    is no `have _ :=` discard.

    Read-only reuse, nothing existing moves: `hwit_alt_faltung`
    (`Extraktion.lean`), `samen_J0` / `samen_J0_hwit_base` (above). -/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Fold instance at the seed J0.** The `hwit_alt_faltung` fold with its
    posited joint run fixed to the constructed seed (`J₀ := samen_J0 Nb sp fn0`):
    `hempty` closes by `samen_J0_schritt_leer` (by `rfl`), `hcode` by
    `samen_J0_code` (by `rfl`), narrowing the code to `fun _ => fn0`; the vacuous
    base is `samen_J0_hwit_base`. The conclusion is the instantiated prefix duty
    over whole single-thread `PCReach` runs, ready for consumers. Every premise
    is load-bearing: each feeds the fold it instantiates. -/
theorem hwit_falt_instanz_J0
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Nb : Nebeneinander) (fn0 : D.Fn)
    (t₀ : D.Tab) (f : Faden)
    (tabs : List D.Tab) (globs : List D.Glob)
    (hsingle_prog : ∀ g, g ≠ f → prog g = [])
    (hax_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      (match s with | .axiomCall _ _ _ _ _ _ _ => False | _ => True))
    (hmem_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (_hleaf : s.istBlatt = true),
      .inl t₀ ∈ Extraktion.stmtTraeger tabs globs s)
    (hbytes_all : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ'),
      (match s with | .putBytes _ _ _ n _ _ _ _ _ _ => 0 < n | _ => True))
    (hwit_lock : ∀ (Mx : GenMaschine D) (pcx : PCStand),
      PCReach P O passes prog (GenStart sp) Mx pcx →
      TraegerSchreibt ((fun _ => fn0) f) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
        Mx.lauf[j]? = some (Schritt.mk f (.zugriff t₀ w Λe he)))
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    ∃ (sched : List Faden),
      ∀ (k : Nat) (g : Faden), sched[k]? = some g →
        TraegerSchreibt ((fun _ => fn0) g) (.inl t₀) = true →
        ∃ (j : Nat) (w : Bool) (Λe : List (Res D)) (he : List D.Lock),
          M.lauf[j]? = some (Schritt.mk g (.zugriff t₀ w Λe he)) := by
  exact Extraktion.hwit_alt_faltung P O passes prog sp Nb
    (samen_J0 Nb sp fn0) (samen_J0_schritt_leer Nb sp fn0)
    (fun _ => fn0) (samen_J0_code Nb sp fn0)
    t₀ f tabs globs hsingle_prog hax_all hmem_all hbytes_all hwit_lock M pc h

#print axioms Gabbro.Grammatik.hwit_falt_instanz_J0


end Gabbro.Grammatik
