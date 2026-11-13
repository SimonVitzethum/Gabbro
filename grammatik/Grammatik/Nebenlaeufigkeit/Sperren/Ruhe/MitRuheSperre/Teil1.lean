/-
  File:      Grammatik/MitRuheSperre.lean
  Subject:   THE LOCK-INVARIANT SEMANTICS OF P.mitRuhe BEHAVES AS THE ONE OF
             P (the open piece of MitRuheSemantik.lean's header): every
             statement, block and end block of a translated body runs under
             `execStmtH`/`execBlockH`/`execEndH` (acquire moves, release
             checks) from the translated world and environment to the
             translated outcome -- up to the LABEL of a logic failure that a
             call handler of `D.mitRuhe` answers (`AusRelRu`, `EndRel`).

  Why "up to the label": the user obligation (`KoerperGutS`) quantifies
  over EVERY handler of `D.mitRuhe`, and such a handler may answer a logic
  failure that names the idle root (`nachbedingung none`, `abstieg none`),
  which is the translation of no label of `D`. The relation keeps what the
  obligation reads: a normal, reason, `leave`/`next` or hardware outcome is
  exactly the translated one; a logic outcome is a logic outcome, and it
  blames a caller (`vorbedingung`) only if the one of `D` does
  (`LogikTreu`).

  The inverse direction (`worldZ`, `envZ`, `ergZ`, `rufZ`,
  `Orakel.zurueck`): every world, environment, oracle and move of
  `D.mitRuhe` is the translation of one of `D` (`worldR_worldZ`,
  `envR_envZ`, `zurueck_mitRuhe`).
-/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The inverse translations -/

theorem worldR_worldZ (σ : World D.mitRuhe) : worldR (worldZ σ) = σ := by
  cases σ with
  | mk slots globs spur =>
      simp only [worldZ, worldR, valR_valZ, List.map_map]
      congr 1
      conv => rhs; rw [← List.map_id spur]
      exact List.map_congr_left fun e _ => evR_evZ e

theorem offen_map_evZ : ∀ s : List (Ereignis D.mitRuhe), offen (s.map (evZ (D := D))) = offen s
  | [] => rfl
  | .nimmt L h :: s => congrArg (L :: ·) (offen_map_evZ s)
  | .gibt L :: s => congrArg (fun l => List.erase l L) (offen_map_evZ s)
  | .zugriff .. :: s => offen_map_evZ s
  | .gzugriff .. :: s => offen_map_evZ s
  | .fremd .. :: s => offen_map_evZ s

theorem haelt_worldZ (σ : World D.mitRuhe) : (worldZ σ).haelt = σ.haelt := offen_map_evZ σ.spur

theorem envR_envZ : ∀ {Γ : Ctx} (ρ : Env D.mitRuhe (Γ.map tyR)), envR (envZ ρ) = ρ
  | [], .nil => rfl
  | τ :: _, .cons v ρ => by
      show Env.cons (valR τ (valZ τ v)) (envR (envZ ρ)) = _
      rw [valR_valZ, envR_envZ ρ]

theorem speicherZ_worldR (σ : World D) : speicherZ (worldR σ).speicher = σ.speicher :=
  speicherZ_speicherR σ.speicher

/-- A result value of `D.mitRuhe`, translated back. -/
def ergZ : (e : Option Ty) → ErgVal D.mitRuhe (e.map tyR) → ErgVal D e
  | none, _ => ()
  | some τ, v => valZ τ v

theorem ergZ_ergR : ∀ (e : Option Ty) (v : ErgVal D e), ergZ e (ergR e v) = v
  | none, _ => rfl
  | some τ, v => valZ_valR τ v

theorem ergR_ergZ : ∀ (e : Option Ty) (v : ErgVal D.mitRuhe (e.map tyR)), ergR e (ergZ e v) = v
  | none, _ => rfl
  | some τ, v => valR_valZ τ v

/-- A hardware outcome of `D.mitRuhe`, translated back (every one is a
    translation: the hardware names axioms, assumptions and registers of `D`). -/
def hwZ : Hardware D.mitRuhe → Hardware D
  | .annahme a => .annahme a
  | .fortschritt a => .fortschritt a
  | .ieee => .ieee
  | .register r => .register r
  | .geraet r => .geraet r
  | .sichtbarkeit a => .sichtbarkeit a

theorem hwR_hwZ (e : Hardware D.mitRuhe) : hwR (hwZ e) = e := by cases e <;> rfl

/-- A logic label of `D.mitRuhe`, read back where the measure gate needs it: a descent at a translated function
    stays a descent; every other label becomes `schleife`. -/
def logikZ : Logik D.mitRuhe → Logik D
  | .abstieg (some h) => .abstieg h
  | _ => .schleife

/-- A call outcome of `D.mitRuhe` at `some g`, translated back; a logic
    failure keeps a descent's label (`logikZ`), every other becomes `schleife`. -/
def rufZ {g : D.Fn} : RufAusgang (D := D.mitRuhe) (some g) → RufAusgang g
  | .ok σ v => .ok (worldZ σ) (ergZ (D.erg g) v)
  | .why σ r => .why (worldZ σ) r
  | .logik e => .logik (logikZ e)
  | .hardware e => .hardware (hwZ e)

/-- **The handler of `D` a handler of `D.mitRuhe` answers with.** -/
def rufZuD (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
    RufAusgang f) : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ => rufZ (R' (some g) (worldR σ) (envR ρ))

/-- **The oracle of `D` an oracle of `D.mitRuhe` answers with.** -/
def Orakel.zurueck (O' : Orakel D.mitRuhe) : Orakel D where
  wirktL a σ ρ := (worldZ (O'.wirktL a (worldR σ) (envR ρ)).1, (O'.wirktL a (worldR σ) (envR ρ)).2)
  regLiesL r σ := O'.regLiesL r (worldR σ)
  regSchreib := O'.regSchreib
  sichtbarL g σ := O'.sichtbarL g (worldR σ)
  zeiger k := (O'.zeiger k).bind id

/-- **Every oracle of `D.mitRuhe` answers like one of `D`** (`OrakelRu`). Until 2026-09-15
    it WAS the translation of one (`(Orakel.zurueck O').mitRuhe = O'`); since the loaded image
    joined the oracle (G1 repair) an oracle of `D.mitRuhe` may place the root at an address,
    which the translation of an oracle of `D` never does -- but no translated type accepts
    the root, so every run agrees. -/
theorem orakelRu_zurueck (O' : Orakel D.mitRuhe) : OrakelRu (Orakel.zurueck O') O' :=
  ⟨fun a σ ρ => by
      show ((O'.wirktL a (worldR σ).ohneLese (envR ρ)).1.auf (worldR σ),
          (O'.wirktL a (worldR σ).ohneLese (envR ρ)).2) =
        (worldR ((worldZ (O'.wirktL a (worldR σ.ohneLese) (envR ρ)).1).auf σ),
          (O'.wirktL a (worldR σ.ohneLese) (envR ρ)).2)
      rw [worldR_ohneLese, ← worldR_auf, worldR_worldZ],
    fun r σ => by
      show O'.regLiesL r (worldR σ).ohneLese = O'.regLiesL r (worldR σ.ohneLese)
      rw [worldR_ohneLese],
    fun g σ => by
      show O'.sichtbarL g (worldR σ).ohneLese = O'.sichtbarL g (worldR σ.ohneLese)
      rw [worldR_ohneLese],
    fun _ => rfl⟩

/-- **The oracle of `D` an oracle of `D.mitRuhe` answers with, at any world**: `O'` at the translated world. -/
theorem wirkt_zurueck_welt (O' : Orakel D.mitRuhe) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    (Orakel.zurueck O').wirkt a σ ρ =
      (worldZ (O'.wirkt a (worldR σ) (envR ρ)).1, (O'.wirkt a (worldR σ) (envR ρ)).2) := by
  show ((worldZ (O'.wirktL a (worldR σ.ohneLese) (envR ρ)).1).auf σ, (O'.wirktL a (worldR σ.ohneLese) (envR ρ)).2) =
    (worldZ ((O'.wirktL a (worldR σ).ohneLese (envR ρ)).1.auf (worldR σ)),
      (O'.wirktL a (worldR σ).ohneLese (envR ρ)).2)
  rw [worldR_ohneLese, ← worldZ_auf, worldZ_worldR]

theorem regLies_zurueck_welt (O' : Orakel D.mitRuhe) (r : D.Reg) (σ : World D) :
    (Orakel.zurueck O').regLies r σ = O'.regLies r (worldR σ) := by
  show O'.regLiesL r (worldR σ.ohneLese) = O'.regLiesL r (worldR σ).ohneLese
  rw [worldR_ohneLese]

theorem sichtbar_zurueck_welt (O' : Orakel D.mitRuhe) (g : D.Glob) (σ : World D) :
    (Orakel.zurueck O').sichtbar g σ = O'.sichtbar g (worldR σ) := by
  show O'.sichtbarL g (worldR σ.ohneLese) = O'.sichtbarL g (worldR σ).ohneLese
  rw [worldR_ohneLese]

/-- **The oracle of `D.mitRuhe` at any of its worlds**: `O` at the translated-back world (the erasure commutes with the
    translation, `worldZ_ohneLese`). -/
theorem wirkt_mitRuhe_welt (O : Orakel D) (a : D.mitRuhe.Ax) (σ : World D.mitRuhe)
    (ρ : Env D.mitRuhe (D.mitRuhe.aparams a)) :
    O.mitRuhe.wirkt a σ ρ =
      (worldR (O.wirkt a (worldZ σ) (envZ (Γ := D.aparams a) ρ)).1, (O.wirkt a (worldZ σ) (envZ (Γ := D.aparams a) ρ)).2) := by
  show ((worldR (O.wirktL a (worldZ σ.ohneLese) (envZ (Γ := D.aparams a) ρ)).1).auf σ,
      (O.wirktL a (worldZ σ.ohneLese) (envZ (Γ := D.aparams a) ρ)).2) =
    (worldR ((O.wirktL a (worldZ σ).ohneLese (envZ (Γ := D.aparams a) ρ)).1.auf (worldZ σ)),
      (O.wirktL a (worldZ σ).ohneLese (envZ (Γ := D.aparams a) ρ)).2)
  rw [worldZ_ohneLese, ← worldR_auf, worldR_worldZ]

theorem regLies_mitRuhe_welt (O : Orakel D) (r : D.Reg) (σ : World D.mitRuhe) :
    O.mitRuhe.regLies r σ = O.regLies r (worldZ σ) := by
  show O.regLiesL r (worldZ σ.ohneLese) = O.regLiesL r (worldZ σ).ohneLese
  rw [worldZ_ohneLese]

theorem sichtbar_mitRuhe_welt (O : Orakel D) (g : D.Glob) (σ : World D.mitRuhe) :
    O.mitRuhe.sichtbar g σ = O.sichtbar g (worldZ σ) := by
  show O.sichtbarL g (worldZ σ.ohneLese) = O.sichtbarL g (worldZ σ).ohneLese
  rw [worldZ_ohneLese]

/-- The move of `D` a move of `D.mitRuhe` makes. -/
def umweltZ (U' : Umwelt D.mitRuhe) : Umwelt D := fun L σ => worldZ (U' L (worldR σ))

theorem umweltZ_ru (U' : Umwelt D.mitRuhe) (L : D.Lock) (σ : World D) :
    U' L (worldR σ) = worldR (umweltZ U' L σ) := (worldR_worldZ _).symm

/-! ## 2. Outcomes up to the label of a logic failure -/

/-- A logic label of `D.mitRuhe` blames a caller only if the one of `D` does, and is a descent at a translated
    function only if the one of `D` is that descent. -/
def LogikTreu (e' : Logik D.mitRuhe) (e : Logik D) : Prop :=
  (∀ g', e' = .vorbedingung g' → ∃ g, e = .vorbedingung g) ∧ ∀ h, e' = .abstieg (some h) → e = .abstieg h

theorem logikTreu_schleife {e' : Logik D.mitRuhe} (h1 : ∀ g', e' ≠ .vorbedingung g')
    (h2 : ∀ h, e' ≠ .abstieg (some h)) : LogikTreu e' .schleife :=
  ⟨fun g' he => absurd he (h1 g'), fun h he => absurd he (h2 h)⟩

section Rel

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- The translated outcome, or two logic failures (`LogikTreu`). -/
def AusRelRu (a' : Ausgang (vertragR V) l (Γ.map tyR)) (a : Ausgang V l Γ) : Prop :=
  a' = ausR a ∨ ∃ e' e, a' = .logik e' ∧ a = .logik e ∧ LogikTreu e' e

/-- The translated end outcome, or two logic failures (`LogikTreu`). -/
def EndRel (a' : EndAusgang (vertragR V) l (Γ.map tyR)) (a : EndAusgang V l Γ) : Prop :=
  a' = endR a ∨ ∃ e' e, a' = .logik e' ∧ a = .logik e ∧ LogikTreu e' e

theorem AusRelRu.schrumpf {τ : Ty} {a' : Ausgang (vertragR V) l ((τ :: Γ).map tyR)}
    {a : Ausgang V l (τ :: Γ)} (h : AusRelRu a' a) : AusRelRu a'.schrumpf a.schrumpf := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (ausR_schrumpf a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem EndRel.schrumpf {τ : Ty} {a' : EndAusgang (vertragR V) l ((τ :: Γ).map tyR)}
    {a : EndAusgang V l (τ :: Γ)} (h : EndRel a' a) : EndRel a'.schrumpf a.schrumpf := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (endR_schrumpf a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem EndRel.zuAusgang {a' : EndAusgang (vertragR V) l (Γ.map tyR)} {a : EndAusgang V l Γ}
    (h : EndRel a' a) : AusRelRu a'.zuAusgang a.zuAusgang := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (endR_zuAusgang a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

theorem sinv_worldR (S : SperrInv D) (L : D.Lock) (σ : World D) :
    S.mitRuhe.inv L (worldR σ).speicher = S.inv L σ.speicher := by
  show S.inv L (speicherZ (worldR σ).speicher) = _
  rw [speicherZ_worldR]

theorem freiH_ausR (S : SperrInv D) (L : D.Lock) (a : Ausgang V l Γ) :
    freiH S.mitRuhe L (ausR a) = ausR (freiH S L a) := by
  cases a with
  | ok σ ρ =>
      show (if S.mitRuhe.inv L (worldR σ).speicher = true then _ else _) = ausR (if _ then _ else _)
      rw [sinv_worldR]
      cases S.inv L σ.speicher <;> rfl
  | leave h σ ρ =>
      show (if S.mitRuhe.inv L (worldR σ).speicher = true then _ else _) = ausR (if _ then _ else _)
      rw [sinv_worldR]
      cases S.inv L σ.speicher <;> rfl
  | next h σ ρ =>
      show (if S.mitRuhe.inv L (worldR σ).speicher = true then _ else _) = ausR (if _ then _ else _)
      rw [sinv_worldR]
      cases S.inv L σ.speicher <;> rfl
  | zurueck => rfl
  | why => rfl
  | logik => rfl
  | hardware => rfl

theorem AusRelRu.frei (S : SperrInv D) (L : D.Lock) {a' : Ausgang (vertragR V) l (Γ.map tyR)}
    {a : Ausgang V l Γ} (h : AusRelRu a' a) : AusRelRu (freiH S.mitRuhe L a') (freiH S L a) := by
  rcases h with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]; exact Or.inl (freiH_ausR S L a)
  · rw [h1, h2]; exact Or.inr ⟨e', e, rfl, rfl, ht⟩

end Rel


end Gabbro.Grammatik
