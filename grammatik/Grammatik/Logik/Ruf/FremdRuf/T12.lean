/- Part 12 of `FremdRuf` (C08): a software witness with a non-trivial contract.

   The fixture `fdD`/`fdO` (T1) declares no software item and its contracts are
   trivial. Here a second fixture carries one SOFTWARE foreign item: `swD` is a
   one-table, one-gate declaration with `axHerkunft = some .software`, `swQ`
   relates the answer to the answer-world memory (the gate answers the current
   slot value -- result- and memory-dependent, never an invented number), and
   `swO` is the actual binding answering exactly that. `swQ_vertrag` proves the
   oracle meets the ensures, and `swQ_swO` places it as the software premise
   (b) of the split goal (`AxVertragOSw`, T8). The gate is nonfallible; the
   fallible/provider shapes are witnessed in T9. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T8
public import Grammatik.Logik.Ruf.FremdRuf.T7
public import Grammatik.Logik.Ruf.FremdRuf.T1

@[expose] public section

namespace Gabbro.Grammatik

/-- The software fixture: one table `konto` of one slot holding `0 .. 100`,
    no locks, no globals; one gate answering the current slot value. The
    gate is declared SOFTWARE with no named assumption. -/
def swD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Empty
  sig := fun e => nomatch e
  sigNr := fun _ => fdSigArbeit
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some (.int 0 100)
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e
  axHerkunft := fun _ => some AxOrigin.software
  axBeleg := fun _ => none

/-- The single software gate. -/
def swLesen : swD.Ax := ()

/-- The gate is declared software (provenance, never inferred). -/
theorem sw_software : swD.axHerkunft swLesen = some AxOrigin.software := rfl

/-- The declared ensures: the answer IS the current slot value in the answer
    world -- result- and memory-dependent, not an invented number. -/
def swQ : AxEns swD
  | (), σ', v => decide ((v : Zahl 0 100).n = (σ'.slots () 0 ()).n)

/-- The actual binding: memory untouched, recording only, raw answer the
    current slot value. -/
def swO : Orakel swD where
  wirkt
    | (), σ, _ => (σ.merke (axiomSpur [()] [] false [] σ.haelt), (σ.slots () 0 ()).n)
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- The fixture guards nothing, so every access is allowed with no holdings. -/
theorem swD_darf (t : swD.Tab) : darf swD t [] := by
  intro w hw
  have hb : swD.braucht t = [] := rfl
  rw [hb] at hw
  simp only [List.not_mem_nil] at hw

/-- No holdings are held anywhere: `HeldIn` of the empty list. -/
theorem swHeldIn_nil (h : List swD.Lock) : HeldIn ([] : List (Res swD)) h := by
  intro L hL
  simp only [List.not_mem_nil] at hL

/-- Frame of the software call: memory untouched, only the recording. -/
theorem swO_rahmen (σ : World swD) (ρ : Env swD (swD.aparams ())) :
    Rahmen (swD.aschreibt ()) (swD.agschreibt ()) σ (swO.wirkt () σ ρ).1 :=
  rahmen_gleich rfl rfl

/-- The software call keeps the held locks: recording only. -/
theorem swO_haelt (σ : World swD) (ρ : Env swD (swD.aparams ())) :
    (swO.wirkt () σ ρ).1.haelt = σ.haelt := by
  show offen (axiomSpur [()] [] false [] σ.haelt ++ σ.spur) = offen σ.spur
  exact offen_append_zugriffe σ.haelt _ _ (axiomSpur_zugriffMit _ _ _ _ _)

/-- Recording of the software call over the complete domains. -/
theorem swO_spur (σ : World swD) (ρ : Env swD (swD.aparams ()))
    (hgt : ∀ t, swD.aschreibt () t = true → ∀ L, Sum.inl L ∈ swD.braucht t → L ∈ σ.haelt)
    (hgg : ∀ g, swD.agschreibt () g = true → ∀ L, Sum.inl L ∈ swD.gbraucht g → L ∈ σ.haelt) :
    ∃ tabs : List swD.Tab, ∃ globs : List swD.Glob, ∃ Λe : List (Res swD),
      (∀ t, swD.aschreibt () t = true → t ∈ tabs) ∧
      (∀ g, swD.agschreibt () g = true → g ∈ globs) ∧
      (∀ t, swD.aschreibt () t = true → darf swD t Λe) ∧
      (∀ g, swD.agschreibt () g = true → gdarf swD g Λe) ∧
      (∀ m st, Res.marke m st ∉ Λe) ∧
      HeldIn Λe σ.haelt ∧
      (swO.wirkt () σ ρ).1.spur = axiomSpur tabs globs false Λe σ.haelt ++ σ.spur := by
  refine ⟨[()], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact List.Mem.head _
  · intro g hg
    exact nomatch g
  · intro t _
    exact swD_darf t
  · intro g hg
    exact nomatch g
  · intro m st hm
    exact nomatch m
  · exact swHeldIn_nil _
  · rfl

/-- The binding stays in its declared frame and records its write. -/
theorem swO_gut : GutO swO := by
  intro a σ ρ
  cases a with
  | () =>
    refine ⟨swO_rahmen σ ρ, swO_haelt σ ρ, fun hgt hgg => ?_⟩
    exact swO_spur σ ρ hgt hgg

/-- **ZEUGE** (non-trivial software contract): the binding meets the
    memory-dependent ensures -- the raw answer decodes to the slot value the
    answer world carries. Jointly over every world and argument. -/
theorem swQ_vertrag : AxVertragO swQ swO := by
  intro a σ ρ v h
  cases a with
  | () =>
    have hred : einpassenErg swO.zeiger (swD.aerg ()) (swO.wirkt () σ ρ).2
        = einpassen (D := swD) swO.zeiger (.int 0 100) (σ.slots () 0 ()).n := rfl
    rw [hred] at h
    simp only [einpassen] at h
    split at h
    next hcond =>
      have e : (⟨(σ.slots () 0 ()).n, hcond.1, hcond.2⟩ :
          Wert swD (.int 0 100)) = v :=
        Option.some_inj.mp h
      subst e
      show decide (((⟨(σ.slots () 0 ()).n, hcond.1, hcond.2⟩ :
          Wert swD (.int 0 100)) : Zahl 0 100).n
        = ((swO.wirkt () σ ρ).1.slots () 0 ()).n) = true
      exact decide_eq_true rfl
    next hcond =>
      have hslot : (0 : Int) ≤ (σ.slots () 0 ()).n ∧ (σ.slots () 0 ()).n ≤ (100 : Int) :=
        Val.int_bereich (σ.slots () 0 ())
      exact absurd hslot hcond

/-- **ZEUGE** (software premise (b)): the ensures holds as the software part of
    the split goal, about the actual binding -- no hardware assumption. -/
theorem swQ_swO : AxVertragOSw swQ swO :=
  axVertragOSw_of_O swQ_vertrag

end Gabbro.Grammatik
