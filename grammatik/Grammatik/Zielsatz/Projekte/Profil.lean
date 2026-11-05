module

public import Grammatik.Zielsatz.Atomar.BeweisAtomar
public import Grammatik.Parser.Profil.Pipeline
public import Grammatik.Parser.Profil.Platzierung

@[expose] public section

/-!
  File:      Grammatik/Zielsatz/Projekte/Profil.lean
  Subject:   **THE GOAL FOR A SELECTED, PROFILE-BOUND UNIT (C14).** The statement about the unit a build mode
             selects out of the ORIGINAL parsed items, whose profile is bound, whose statics are placed and
             whose hardware assumptions are the profile-selected named set.

  The meaning change this file records (a diff of the statements of `Spec.lean`, described there):

  * **Assumption provenance.** (c) is stated through the named components of `HardwareAnnahmen` --
    `GutO`, `RegLokal`, `AxVertragO` (`HwKomponente`, `hwAlle`) -- and the components the admitted profile
    supplies are exactly these (`profilKomponenten_eq`): the profile adds no software assumption and no
    unlisted one, a linked library requires profile entries by name and adds none
    (`bindung_fuegt_nichts_hinzu_bindung`, `profil_bindung_einheit`). Free prose of an `assume` stays outside
    Lean; the keyed modes have a consistent model (`profil_modell_einheit`). The guest boundary and every
    OS service stay user logic: nothing here assumes them.
  * **The selected-program statement.** The unit is a `ProfilEinheit`: the unit `E` together with the
    build mode, the ORIGINAL items, and the checked policy of its image sections. The certificate
    (`ProfilEinheit.zert`: selection, profile binding of the selected tree) and the placement requests are
    COMPUTED from these, never carried as data. Premise (a) is the checker's Bool on `E` together with the
    structural admission of the certificate (`profilAkzeptiert`); `Akzeptiert` itself still judges the
    selected program. Both build modes are separate instances; nothing about the shipping build follows from
    a test-build proof or conversely, because the selection differs.
  * **Not here.** That `E` IS the translation of the selected tree (`uebersetzeWahl`) is the correspondence
    of the source-to-unit pipeline (`CanonicalSourceProgram`), not restated; the layout, startup and
    relocation proofs that discharge placement (IR-03/06/12); the entry/service binding and the guest
    boundary (C08/C12 services), which stay refused.
-/

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell
open Gabbro.Grammatik.Parser.ProfilBindung (bindungB bindungB_zerlegt blockOk_einig modusProfil modusBibliothek
  modusProfil_modell bindung_fuegt_nichts_hinzu_bindung modi ProfilBlock platzierungVon platzB)

variable {D : Deklaration}

/-! ## The named hardware components -/

/-- The named hardware components of `HardwareAnnahmen`, one by one. -/
inductive HwKomponente where
  | gut
  | regLokal
  | axVertrag
  | nativeFloat
  deriving DecidableEq, Repr

/-- What each component says (Spec.lean, THE ONE ASSUMPTION LIST). -/
def HwKomponente.gilt (O : Orakel D) (Q : AxEns D) : HwKomponente → Prop
  | .gut => GutO O
  | .regLokal => RegLokal O
  | .axVertrag => AxVertragO Q O
  | .nativeFloat => RootNativeFloat.Hardware

/-- All named components. -/
def hwAlle : List HwKomponente := [.gut, .regLokal, .axVertrag, .nativeFloat]

/-- **`HardwareAnnahmen` is exactly the conjunction of the named components.** -/
theorem hardware_iff_komponenten (O : Orakel D) (Q : AxEns D) :
    HardwareAnnahmen O Q ↔ ∀ k ∈ hwAlle, k.gilt O Q := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ k hk
    simp only [hwAlle, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · intro h
    exact ⟨h .gut (by simp [hwAlle]), h .regLokal (by simp [hwAlle]),
      h .axVertrag (by simp [hwAlle]), h .nativeFloat (by simp [hwAlle])⟩

/-! ## The selected unit -/

/-- **A unit with the source it was selected from**: the unit `E`, the build mode, the ORIGINAL parsed items
    and the checked policy of the image's sections. -/
structure ProfilEinheit (D : Deklaration) where
  E : Einheit D
  modus : Parser.Auswahl.BauModus
  original : List Parser.SItemTief
  politik : List (String × Zugriff) := []

/-- The certificate, computed from the mode and the original items. -/
def ProfilEinheit.zert (PE : ProfilEinheit D) : ProfilZert := ProfilZert.von PE.modus PE.original

/-- **The structural admission**: the selection declares no reserved name, the profile binding passes, and
    the statics' placement requests of the selected tree are admitted by the policy. -/
def ProfilEinheit.zulaessig (PE : ProfilEinheit D) : Bool :=
  PE.zert.zulaessig &&
    match platzierungVon PE.zert.auswahl.ausgewaehlt with
    | .ok es => platzB PE.politik es
    | .error _ => false

/-- **Premise (a) for a selected unit**: the checker's Bool on `E` together with the certificate's
    structural admission. -/
def profilAkzeptiert (C : PrueferX) [DecidableEq D.Fn] (PE : ProfilEinheit D) (fs : List D.Fn)
    (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) : Bool :=
  C.akzeptiert PE.E fs ls cs && PE.zulaessig

/-- The hardware components the admitted profile supplies: the named ones, no more (linking adds none). -/
def profilKomponenten (_ : ProfilEinheit D) : List HwKomponente := hwAlle

theorem profilKomponenten_eq (PE : ProfilEinheit D) : profilKomponenten PE = hwAlle := rfl

/-- **Premise (c) for a selected unit**: the profile-selected named components hold of the oracle. -/
def ProfilAnnahmen (PE : ProfilEinheit D) (O : Orakel D) : Prop :=
  ∀ k ∈ profilKomponenten PE, k.gilt O PE.E.Q

/-- **The profile-selected assumptions are `HardwareAnnahmen`**, exactly. -/
theorem profilAnnahmen_iff (PE : ProfilEinheit D) (O : Orakel D) :
    ProfilAnnahmen PE O ↔ HardwareAnnahmen O PE.E.Q :=
  (hardware_iff_komponenten O PE.E.Q).symm

/-- An admitted unit has an admitted profile binding. -/
theorem ProfilEinheit.bindung_zulaessig (PE : ProfilEinheit D) (hz : PE.zulaessig = true) :
    bindungB PE.zert.bindung = true := by
  have h1 : PE.zert.zulaessig = true := by
    simp only [ProfilEinheit.zulaessig, Bool.and_eq_true] at hz
    exact hz.1
  simp only [ProfilZert.zulaessig, Bool.and_eq_true] at h1
  exact h1.2

/-- **An admitted profile has a model**: with its one profile block `p`, a mode assignment under which every
    decoded keyed mode holds (`profil_modell`). It proves no free prose and no hardware. -/
theorem profil_modell_einheit (PE : ProfilEinheit D) (hz : PE.zulaessig = true) {p : ProfilBlock}
    (hp : PE.zert.bindung.profile = [p]) :
    ∃ m : ModusBelegung, Profil.gilt (modusProfil D (modi p.eintraege)) m := by
  have hB := (bindungB_zerlegt (PE.bindung_zulaessig hz)).2.1 p
    (by rw [hp]; exact List.mem_singleton_self p)
  exact modusProfil_modell D (blockOk_einig hB)

/-- **Linking adds nothing** (`bindung_fuegt_nichts_hinzu` for the source-bound profile): under any mode
    assignment the profile's decoded modes hold under, every library's decoded requirements hold. -/
theorem profil_bindung_einheit (PE : ProfilEinheit D) (hz : PE.zulaessig = true) {p : ProfilBlock}
    (hp : PE.zert.bindung.profile = [p]) {lib : ProfilBlock} (hl : lib ∈ PE.zert.bindung.bedarfe)
    (name : String) (m : ModusBelegung) (hgilt : Profil.gilt (modusProfil D (modi p.eintraege)) m) :
    Bibliothek.gilt (modusBibliothek D name (modi lib.eintraege)) m :=
  bindung_fuegt_nichts_hinzu_bindung D name (PE.bindung_zulaessig hz) hp hl m hgilt

/-! ## The statement -/

/-- **GABBRO_ZIEL FOR A SELECTED, PROFILE-BOUND UNIT.** The conclusion of `GabbroZiel`, word for word, over
    the unit `PE.E`; (a) adds the structural admission of the selection/profile/placement certificate, (c) is
    the profile-selected named component set. -/
def GabbroZielProfil : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (PE : ProfilEinheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    profilAkzeptiert C PE fs.1 ls.1 cs.1 = true →               -- (a) the checker and the certificate
    NutzerPflichtA PE.E →                                       -- (b) the user, with the rely
    ∀ O : Orakel D, ProfilAnnahmen PE O →                       -- (c) the profile-selected hardware
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit PE.E sp init →                                   -- (d) the runtime, A4
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX PE.E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) PE.E.P PE.E.ws)
          (FadenStart PE.E.P.mitRuhe sp init lebt0) K →
          ZielFX PE.E.P.mitRuhe PE.E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) PE.E.P PE.E.ws)
            (RufStartG PE.E.P.mitRuhe sp init) (PE.E.arenen.map (·.mitRuhe)) K

/-- **GABBRO_ZIEL FOR A SELECTED, PROFILE-BOUND UNIT, PROVED**: `gabbro_ziel` on `PE.E`. -/
theorem gabbro_ziel_profil : GabbroZielProfil := by
  intro C D _ PE fs ls cs hC hN O hH passes sp init hL lebt0 K hK
  have hC' : C.akzeptiert PE.E fs.1 ls.1 cs.1 = true := by
    simp only [profilAkzeptiert, Bool.and_eq_true] at hC
    exact hC.1
  exact gabbro_ziel C D PE.E fs ls cs hC' hN O ((profilAnnahmen_iff PE O).mp hH) passes sp init hL lebt0 K hK

#print axioms gabbro_ziel_profil

/-! ## Entry roots -/

/-- A root the unit declares to start (an entry's dispatch root as a declared start), with its declared
    arguments. -/
def EintrittTreu (E : Einheit D) (w : D.Fn) (a : Env D (D.params w)) : Prop :=
  (⟨w, a⟩ : Σ w : D.Fn, Env D (D.params w)) ∈ E.starts ++ E.gestartet

/-- **The entry binding adds no thread the checker did not see**: a declared start is among the roots
    `Einheit.ws` that thread-locality, pool safety and write separation range over. -/
theorem eintritt_wurzel_in_ws {E : Einheit D} {w : D.Fn} {a : Env D (D.params w)}
    (h : EintrittTreu E w a) : w ∈ E.ws := by
  unfold Einheit.ws
  exact List.mem_map.mpr ⟨⟨w, a⟩, List.mem_append_left _ h, rfl⟩

/-- Under the runtime assumption (d) a thread that runs a root runs a DECLARED one: its start is a declared
    start of the unit. -/
theorem eintritt_laufzeit {E : Einheit D} {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hL : Laufzeit E sp init) (t : Faden) (w : D.Fn) (hne : (init t).1 = some w) :
    ∃ a ∈ E.starts ++ E.gestartet, a.1 = w := by
  rcases hL.start t with h | ⟨a, ha, h⟩
  · rw [h] at hne
    exact absurd hne (by simp)
  · rw [h] at hne
    have h2 : some a.1 = some w := hne
    exact ⟨a, ha, Option.some.inj h2⟩

end Gabbro.Grammatik.Zielsatz
