/-
  File:      Core/Ziel/Form.lean
  Subject:   The SHAPE of the one goal theorem of `dokumente/PERFECT-MODEL.md` §2, as a Lean statement.

  `GabbroZielForm R` is the statement of PERFECT-MODEL §2 over the ingredients `R : Rahmen`. Every field of
  `Rahmen` names one definition of PERFECT-MODEL §3: the reference AST and its meaning (§3.1), acceptance (§3.2),
  the catalogue (§3.3), the ideal meaning `I` (§3.4), the implementation runs (§3.5), the refinement `Sim` (§3.6),
  progress (§3.7), the bounds and noninterference (§2, §3.8), and today's guarantee `ZielFX`.

  This file fixes the shape only; it proves nothing and claims nothing. The construction of `core/` (PERFECT-MODEL §8) builds the
  real definitions; its last step M12 states `gabbro_ziel` over those concrete constants and the closing guard
  checks that its type is `GabbroZielForm R₀` for the ONE value `R₀` whose every field is the pinned real
  definition, with every definition pinned down to the approved foundations. A statement over another `Rahmen`
  is no promise: with trivial fields `GabbroZielForm` is satisfiable without any run (review of 2026-11-23), so
  the force of the theorem lies in the pinned fields of `R₀`, never in this shape alone. `Rahmen` and
  `GabbroZielForm` are hash-pinned by the guards of `Core/Waechter/` (PERFECT-MODEL §6); changing them is a change of the goal's meaning and is
  the owner's decision (AGENTS.md §3).
-/
module
@[expose] public section

namespace Gabbro.Core.Ziel

/-- The ingredients the goal theorem speaks about (PERFECT-MODEL.md §3). -/
structure Rahmen where
  /-- Raw text, its well-formedness (defined independently of `Bezeichnet`, acceptance and the deployed parser),
  the forms of the language (derived from the constructors), and the registry's evidence that a form is used. -/
  Text : Type
  WohlgeformterText : Text → Prop
  Form : Type
  Einheit : Type
  enthaelt : Text → Form → Prop
  realisiert : Form → Text → Einheit → Prop
  /-- The meaning of raw text through the reference parser and elaboration rules, and acceptance (§3.1, §3.2). -/
  Bezeichnet : Text → Einheit → Prop
  Akzeptiert : Einheit → Prop
  /-- The catalogue (§3.3): selected rows, well-formedness, environments (row-conformant outside behaviour,
  mandatory answers included), and fair hardware histories, defined independently of any program. -/
  Katalog : Type
  katalog : Einheit → Katalog
  KatalogWohlgeformt : Katalog → Prop
  Umgebung : Type
  Hardware : Katalog → Umgebung → Prop
  HwLauf : Type
  FairLaeufe : Katalog → Umgebung → HwLauf → Prop
  /-- Implementation runs (§3.5): every prefix under row-conformant outside behaviour, also a failing or stuck
  one; their cuts, their hardware projection and their start. -/
  Lauf : Type
  Laeufe : Einheit → Umgebung → Lauf → Prop
  Schnitt : Lauf → Type
  hw : Lauf → HwLauf
  Start : Type
  start : Lauf → Start
  /-- The ideal meaning `I` (§3.4): its runs, determinacy and progress. -/
  IdealLauf : Type
  IdealLaeufe : Einheit → IdealLauf → Prop
  Bestimmt : Einheit → Prop
  IdealFortschritt : Einheit → Prop
  /-- The refinement (§3.6): one state-and-step simulation per run. -/
  Sim : Einheit → Lauf → IdealLauf → Prop
  /-- Today's guarantee, transported to every cut (§2.1). -/
  ZielFX : Einheit → Umgebung → (ρ : Lauf) → Schnitt ρ → Prop
  /-- Progress (§3.7): hanging per context, and progress per checked class. -/
  Kontext : Type
  Haengt : Einheit → Lauf → IdealLauf → Kontext → Prop
  Klasse : Type
  klasse : Einheit → Klasse
  Fortschritt : Klasse → Lauf → IdealLauf → Prop
  /-- Bounds on stack, memory, cost and time (§3.7). -/
  ImSchranken : Einheit → Lauf → Prop
  /-- Noninterference (§3.8): low equality of starts and environments, the same total public-history policies
  for the low outside choices, and the low observation (low termination and declared time included). -/
  NiedrigGleich : Einheit → Start → Start → Prop
  GleicheNiedrigeUmgebung : Einheit → Umgebung → Umgebung → Prop
  GleichePolitik : Einheit → Lauf → Lauf → Prop
  Beob : Type
  NiedrigeBeob : Einheit → Lauf → Beob
  /-- Equal up to each declared release, differing only as that release authorises (§2.1). -/
  NiedrigAequiv : Einheit → Beob → Beob → Prop

/-- §2.1: nothing in the promise holds vacuously — text, catalogues, acceptance and forms are jointly
satisfiable, every fair hardware history lifts to a run of every accepted program, and `I` is determined and
makes progress. -/
def NichtLeer (R : Rahmen) : Prop :=
    (∀ a, R.WohlgeformterText a ↔ ∃ E, R.Bezeichnet a E)
  ∧ (∀ a E E', R.Bezeichnet a E → R.Bezeichnet a E' → E = E')
  ∧ (∀ f : R.Form, ∃ a E, R.enthaelt a f ∧ R.Bezeichnet a E ∧ R.Akzeptiert E ∧ R.realisiert f a E)
  ∧ (∀ E, R.Akzeptiert E → R.KatalogWohlgeformt (R.katalog E))
  ∧ (∀ K, R.KatalogWohlgeformt K → ∃ H h, R.Hardware K H ∧ R.FairLaeufe K H h)
  ∧ (∀ a E, R.Bezeichnet a E → R.Akzeptiert E → ∀ H h, R.Hardware (R.katalog E) H →
        R.FairLaeufe (R.katalog E) H h → ∃ ρ, R.Laeufe E H ρ ∧ R.hw ρ = h)
  ∧ (∀ E, R.Akzeptiert E → R.Bestimmt E ∧ R.IdealFortschritt E)

/-- §2.1: an implementation run `ρ` refines the ideal run `ι` — same effects in the same order, today's guarantee
on every cut, no context hangs on a fair hardware history, and the run stays in its bounds. -/
def Verfeinert (R : Rahmen) (E : R.Einheit) (H : R.Umgebung) (ρ : R.Lauf) (ι : R.IdealLauf) : Prop :=
    R.Sim E ρ ι
  ∧ (∀ t : R.Schnitt ρ, R.ZielFX E H ρ t)
  ∧ (R.FairLaeufe (R.katalog E) H (R.hw ρ) → (∀ c, ¬ R.Haengt E ρ ι c) ∧ R.Fortschritt (R.klasse E) ρ ι)
  ∧ R.ImSchranken E ρ

/-- §3.8: noninterference. For every run and every low-equal start, a comparison run under the same
policies exists, and every such run shows a related low trace. -/
def NI (R : Rahmen) : Prop :=
  ∀ E H₁ H₂ ρ₁ s₂, R.Akzeptiert E → R.Hardware (R.katalog E) H₁ → R.Hardware (R.katalog E) H₂ →
    R.Laeufe E H₁ ρ₁ → R.GleicheNiedrigeUmgebung E H₁ H₂ → R.NiedrigGleich E (R.start ρ₁) s₂ →
      (∃ ρ₂, R.Laeufe E H₂ ρ₂ ∧ R.start ρ₂ = s₂ ∧ R.GleichePolitik E ρ₁ ρ₂)
    ∧ ∀ ρ₂, R.Laeufe E H₂ ρ₂ → R.start ρ₂ = s₂ → R.GleichePolitik E ρ₁ ρ₂ →
        R.NiedrigAequiv E (R.NiedrigeBeob E ρ₁) (R.NiedrigeBeob E ρ₂)

/-- The one goal theorem of PERFECT-MODEL.md §2, over the ingredients `R`: not vacuous; every run of every
accepted program refines ONE ideal run; no secret leaks. -/
def GabbroZielForm (R : Rahmen) : Prop :=
    NichtLeer R
  ∧ (∀ a E, R.Bezeichnet a E → R.Akzeptiert E → ∀ H, R.Hardware (R.katalog E) H →
      (∃ ρ, R.Laeufe E H ρ) ∧ ∀ ρ, R.Laeufe E H ρ → ∃ ι, R.IdealLaeufe E ι ∧ Verfeinert R E H ρ ι)
  ∧ NI R

end Gabbro.Core.Ziel
