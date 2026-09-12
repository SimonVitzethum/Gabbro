/-
  File:      Grammatik/KetteVoll.lean
  Subject:   **THE CHAIN FROM A MACHINE RUN, N THREADS** -- every `PCReach`
              run carries a joint chain with the same worlds and step threads.

  Lane 104 (D4): iterate the witnessed step (`kette_mit_zeugen`,
  `Ziel.lean`) over a whole `PCReach` run for any number of threads.
  The chain runs with an empty recorded run (`J.l = []`), so `Gesittet`
  and `BeschraenkteVerschraenkung` close vacuously; entry is built to
  fit the code (`eintrittOf`); debt holds for every function by U003
  (`schuldnerHaelt_gilt`); the invariant sight follows from the entry
  (`heldIn_invarianten` bridge); each step frame comes from the fired
  step (`blatt_rahmen_vertrag` widened by the full-rights code, locks
  by unchanged memory). No premise quantifies over program syntax.
-/
import Grammatik.Maschine

namespace Gabbro.Grammatik

namespace KetteVoll

variable {D : Deklaration}

/-- The permissive pair set: every thread pair is co-declared, so the
    pair leg (`hPaar`) and the bounded interleaving over the empty run
    close by construction. -/
def ketteNb : Nebeneinander := fun _ _ => True

/-- A trace holding exactly the locks named by `Λ`: one `nimmt` per
    held lock (marks are dropped; `offen` ignores the snapshots). -/
def spurFuer (Λ : List (Res D)) : List (Ereignis D) :=
  (Λ.filterMap fun r => match r with
    | .held L => some L
    | _ => none).map fun L => Ereignis.nimmt L []

/-- The entry world for thread `g`: start memory with a trace holding
    exactly the locks its code declares at entry (`Signatur.anfang`). -/
def eintrittOf (sp : Speicher D) (code : Faden → D.Fn) (g : Faden) : World D :=
  sp.welt (spurFuer (Signatur.anfang D (D.signatur (code g))))

/-- `offen` of the built trace is the lock list it was built from. -/
theorem offen_spurFuer (ls : List D.Lock) :
    offen ((ls.map fun L => Ereignis.nimmt L []) : List (Ereignis D)) = ls := by
  induction ls with
  | nil => rfl
  | cons L rest ih => simp [offen, ih]

/-- Membership in the built trace is membership of the held locks in `Λ`. -/
theorem mem_offen_spurFuer (Λ : List (Res D)) (L : D.Lock) :
    L ∈ offen (spurFuer Λ) ↔ Res.held L ∈ Λ := by
  unfold spurFuer
  rw [offen_spurFuer]
  constructor
  · intro hmem
    obtain ⟨r, hr, hfr⟩ := List.mem_filterMap.mp hmem
    cases r with
    | held L' =>
      simp at hfr
      subst hfr
      exact hr
    | marke _ _ => simp at hfr
  · intro hmem
    exact List.mem_filterMap.mpr ⟨Res.held L, hmem, rfl⟩

/-- The built entry world holds exactly the declared entry locks. -/
theorem eintrittOf_passt (sp : Speicher D) (code : Faden → D.Fn) (g : Faden) :
    EintrittPasst (code g) (eintrittOf sp code g) := by
  intro L
  show Res.held L ∈ Signatur.anfang D (D.signatur (code g)) ↔
    L ∈ offen (eintrittOf sp code g).spur
  unfold eintrittOf
  have hspur : (sp.welt (spurFuer (Signatur.anfang D (D.signatur (code g))))).spur =
      spurFuer (Signatur.anfang D (D.signatur (code g))) := rfl
  rw [hspur]
  exact (mem_offen_spurFuer _ L).symm

/-- The invariant sight follows from the entry: no separate sight premise
    is owed (`heldIn_invarianten` over the two-sided entry set). -/
theorem sicht_aus_eintritt (P : Programm D) (fn : D.Fn) (σ : World D)
    (hE : EintrittPasst (D := D) fn σ) : InvSichtHaelt (D := D) fn σ :=
  fun i hi => heldIn_invarianten P fn (eintrittHeldIn_aus_Passt hE) i hi

/-- Every spur has one step per thread entry: the world history counts steps. -/
theorem spurLaenge (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
    (hspur : PCSpur P O passes prog (GenStart sp) Mx pcx trx) :
    Mx.welten.length = trx.length + 1 := by
  induction hspur with
  | leer => simp [GenStart]
  | schritt M M' pc pc' g _hs hs _trx _htr ih =>
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩ <;>
      simp_all

/-- The last recorded world carries the live memory: every step appends
    its post-world and installs its memory. -/
theorem letzteSpeicher (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Mx : GenMaschine D) (pcx : PCStand)
    (h : PCReach P O passes prog (GenStart sp) Mx pcx) :
    ∀ w : World D, Mx.welten.getLast? = some w → w.speicher = Mx.speicher := by
  induction h with
  | start =>
    intro w hw
    simp [GenStart] at hw ⊢
    subst hw
    rfl
  | step M M' pc pc' g _hmid hs _ih =>
    intro w hw
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
    · simp_all
    · simp only [List.getLast?_append] at hw
      simp at hw
      subst hw
      exact speicher_welt_speicher _ _
    · simp only [List.getLast?_append] at hw
      simp at hw
      subst hw
      exact speicher_welt_speicher _ _

end KetteVoll

end Gabbro.Grammatik
