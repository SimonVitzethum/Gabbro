/-
  File:      Grammatik/WacheGlobal.lean
  Subject:   D6 -- WATCHES FOR GLOBALS (lane 103).

  Mirror of `wache_aus_schuld` (InterferenzAllgemein.lean) for globals:
  a writer of global `x` holds every guard in its watch list, from the
  checker's per-thread touch discipline plus the guard fact. U003
  (`D.invarianten_gehalten`) is table-only, so the mirror routes via
  the touch rule (`WaechterGehalten`) instead of `J.hSchuld`.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The watch, discharged for globals.** A writer of global `x₀` holds
    every guard in `x₀`'s watch list: the touch discipline gives the
    held ceramony (`WaechterGehalten`) at `.inr x₀`, the guard fact picks
    `L`, and the `held`-membership in the signature holdings is exactly
    the declared hold. Tables route via `J.hSchuld` (`wache_aus_schuld`);
    globals have no `schuldet` coverage, so the discipline travels here
    as the explicit per-thread premise `hTouch`. -/
theorem wache_global_aus_schuld (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (x₀ : D.Glob) (L : D.Lock)
    (hGuardG : Sum.inl L ∈ D.gbraucht x₀)
    (g : Faden) (hg : g ∈ J.faeden)
    (hW : TraegerSchreibt (J.code g) (.inr x₀) = true)
    (hTouch : ∀ f ∈ J.faeden, TraegerSchreibt (J.code f) (.inr x₀) = true →
      WaechterGehalten (J.code f) (.inr x₀)) :
    L ∈ D.haelt (J.code g) := by
  have hWG : ∀ w ∈ D.gbraucht x₀,
      Res.von D w ∈ Signatur.anfang D (D.signatur (J.code g)) :=
    hTouch g hg hW
  have hmem := hWG (Sum.inl L) hGuardG
  change Res.held (D := D) L ∈ _ at hmem
  simp only [Signatur.anfang] at hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · obtain ⟨L', hL', heq⟩ := List.mem_map.mp hleft
    cases heq
    exact hL'
  · obtain ⟨⟨m, s⟩, _, heq⟩ := List.mem_map.mp hright
    simp only [Res.vonMarke] at heq
    cases heq

/-! ## Witness declaration: one table, one guarded global, one lock.

  `refD` (ReferenzB.lean) has `Glob := Empty`, so no global witness lives
  on it; `gD` extends its pattern minimally: the single function writes
  the table (non-degeneracy for rule 13) and the global (the watched
  write), both under the single lock. -/
def gD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 10
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => true
  ggeteilt := fun _ => true
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => [Sum.inl ()]
  gbraucht := fun _ => [Sum.inl ()]
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := [()]
      schreibt := fun _ => true
      gschreibt := fun _ => true
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by
    cases t
    show [Sum.inl ()] ≠ []
    simp
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g _ => by
    cases g
    refine Or.inl ?_
    show [Sum.inl ()] ≠ []
    simp

/-- The witness thread runs the single function. -/
def gCode : Faden → gD.Fn := fun _ => ()

/-- The global's guard is the lock. -/
theorem gGuardInst : Sum.inl () ∈ gD.gbraucht () :=
  List.mem_singleton.mpr rfl

/-- The function writes the global (the watched write). -/
theorem gWriteInst : TraegerSchreibt (D := gD) (gCode 0) (.inr ()) = true :=
  rfl

/-- Non-degeneracy: some function writes a table. -/
theorem gTabWrite : ∃ f t, gD.schreibt f t = true :=
  ⟨(), (), rfl⟩

/-- The signature holdings name exactly the lock. -/
theorem gAnfang : Signatur.anfang gD (gD.signatur ()) =
    [Res.held (D := gD) ()] := rfl

/-- The table slots: `0` everywhere. -/
def gSlots : ∀ t : gD.Tab, Int → ∀ f : gD.Feld t, Wert gD (gD.typ t f) :=
  fun _ _ _ => ⟨0, by decide, by decide⟩

/-- The global before the step: `0`. -/
def gGlobs0 : ∀ g : gD.Glob, Wert gD (gD.gtyp g) :=
  fun _ => ⟨0, by decide, by decide⟩

/-- The global after the step: `5` (memory moves). -/
def gGlobs1 : ∀ g : gD.Glob, Wert gD (gD.gtyp g) :=
  fun _ => ⟨5, by decide, by decide⟩

/-- Entry world: lock taken, global `0`. -/
def gW0 : World gD :=
  { slots := gSlots, globs := gGlobs0, spur := [Ereignis.nimmt () []] }

/-- Post world: the global write recorded as a `gzugriff` event. -/
def gW1 : World gD :=
  { slots := gSlots, globs := gGlobs1,
    spur := [Ereignis.gzugriff () true [Res.held (D := gD) ()] [()]] ++ gW0.spur }

/-- The witness neighbourhood: everything declared. -/
def gNb : Nebeneinander := fun _ _ => True

/-- The witness entry map: the lock world. -/
def gEintritt : Faden → World gD := fun _ => gW0

/-- The empty run is disciplined (same shape as `kette_aus_lauf_start`). -/
theorem gGes : Gesittet ([] : Lauf gD) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f j
    have hsp : Lauf.spur ([] : Lauf gD) f j = [] := by simp [Lauf.spur]
    rw [hsp]
    exact konsistent_nil
  · intro f j e he
    have hsp : Lauf.spur ([] : Lauf gD) f j = [] := by simp [Lauf.spur]
    rw [hsp] at he
    simp at he
  · intro j f L h hi g hne
    simp at hi
  · intro i j f g m s s' ei ej hi hj hm hm'
    simp at hi
  · intro i j f g o ei ej hi hj ht1 ht2 hu
    simp at hi

/-- The empty run interleaves only declared pairs. -/
theorem gBeschr : BeschraenkteVerschraenkung (D := gD) gNb ([] : Lauf gD) := by
  intro i j f g ei ej hi hj hne
  simp at hi

/-- The single chain step stays in the writer's frame: the function
    writes everything, so both frame conditions are vacuous. -/
theorem gSchritt : ∀ (k : Nat) (f' : Faden) (vor nach : World gD),
    ([0] : List Faden)[k]? = some f' →
      ([gW0, gW1] : List (World gD))[k]? = some vor →
      ([gW0, gW1] : List (World gD))[k + 1]? = some nach →
      f' ∈ ([0] : List Faden) ∧
        Rahmen (D := gD) (gD.schreibt (gCode f')) (gD.gschreibt (gCode f'))
          vor nach := by
  intro k f' vor nach hk hkv hkn
  cases k with
  | zero =>
      have hf' : 0 = f' := by simpa using hk
      have hv : gW0 = vor := by simpa using hkv
      have hn : gW1 = nach := by simpa using hkn
      subst hf'
      subst hv
      subst hn
      refine ⟨List.mem_singleton.mpr rfl, ?_, ?_⟩
      · intro t ht
        cases t
        have ht' : gD.schreibt () () = false := ht
        have hT : gD.schreibt () () = true := rfl
        rw [hT] at ht'
        exact absurd ht' (by decide)
      · intro g hg
        cases g
        have hg' : gD.gschreibt () () = false := hg
        have hG : gD.gschreibt () () = true := rfl
        rw [hG] at hg'
        exact absurd hg' (by decide)
  | succ n =>
      simp at hk

/-- The witness thread enters holding exactly the lock. -/
theorem gEintritt0 :
    EintrittPasst (D := gD) (gCode 0) (gEintritt 0) := by
  intro L
  cases L
  show Res.held (D := gD) () ∈ [Res.held (D := gD) ()] ↔ () ∈ [()]
  exact iff_of_true (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl)

/-! ## The witness chain: one thread, one memory-moving step. -/
def gJ : GemeinsamerLauf (D := gD) gNb :=
  { faeden := [0]
    code := gCode
    eintritt := gEintritt
    welten := [gW0, gW1]
    schrittFaden := [0]
    l := ([] : Lauf gD)
    hKette := rfl
    hSchritt := gSchritt
    hPaar := by
      intro f' hf' g' hg' hne
      have hf0 : f' = 0 := List.mem_singleton.mp hf'
      have hg0 : g' = 0 := List.mem_singleton.mp hg'
      subst hf0
      subst hg0
      exact absurd rfl hne
    hGesittet := gGes
    hBeschraenkt := gBeschr
    hEintritt := by
      intro f' hf'
      have hf0 : f' = 0 := List.mem_singleton.mp hf'
      subst hf0
      exact gEintritt0
    hSchuld := by
      intro f' hf'
      have hf0 : f' = 0 := List.mem_singleton.mp hf'
      subst hf0
      exact schuldnerHaelt_gilt _
    hInvSicht := by
      intro f' hf'
      have hf0 : f' = 0 := List.mem_singleton.mp hf'
      subst hf0
      intro i
      exact nomatch i }

/-- **Inhabitation.** Every premise of `wache_global_aus_schuld` holds
    jointly on `gD`: the single thread writes the guarded global under
    its lock, the touch discipline holds, and the concluded hold follows
    by the theorem. Non-degenerate: some function writes a table
    (`gTabWrite`), and the chain step moves memory (`0` to `5`). -/
theorem wache_global_aus_schuld_zeuge :
    ∃ (Nb : Nebeneinander) (J : GemeinsamerLauf (D := gD) Nb) (x : gD.Glob)
      (L : gD.Lock) (g : Faden),
      Sum.inl L ∈ gD.gbraucht x ∧ g ∈ J.faeden ∧
      TraegerSchreibt (D := gD) (J.code g) (.inr x) = true ∧
      (∀ f ∈ J.faeden, TraegerSchreibt (D := gD) (J.code f) (.inr x) = true →
        WaechterGehalten (D := gD) (J.code f) (.inr x)) ∧
      L ∈ gD.haelt (J.code g) ∧ (∃ f t, gD.schreibt f t = true) ∧
      J.welten[0]? ≠ J.welten[1]? := by
  have hTouchAll : ∀ f ∈ ([0] : List Faden),
      TraegerSchreibt (D := gD) (gCode f) (.inr ()) = true →
      WaechterGehalten (D := gD) (gCode f) (.inr ()) := by
    intro f hf hW'
    have hf0 : f = 0 := List.mem_singleton.mp hf
    subst hf0
    cases hW'
    intro w hw
    have hw' : w ∈ ([Sum.inl ()] : List (gD.Lock ⊕ (gD.Marke × Nat))) := hw
    have hw0 : w = Sum.inl () := List.mem_singleton.mp hw'
    subst hw0
    have e0 : gCode 0 = () := rfl
    show Res.held (D := gD) () ∈ Signatur.anfang gD (gD.signatur (gCode 0))
    rw [e0, gAnfang]
    exact List.mem_singleton.mpr rfl
  have h0 : gJ.welten[0]? = some gW0 := rfl
  have h1 : gJ.welten[1]? = some gW1 := rfl
  have hne : gJ.welten[0]? ≠ gJ.welten[1]? := by
    intro hcon
    rw [h0, h1] at hcon
    have heq : gW0 = gW1 := Option.some_inj.mp hcon
    have hg : gGlobs0 () = gGlobs1 () := congrArg (fun w => w.globs ()) heq
    have hn : (gGlobs0 ()).n = (gGlobs1 ()).n := congrArg Zahl.n hg
    have hn0 : (gGlobs0 ()).n = 0 := rfl
    have hn1 : (gGlobs1 ()).n = 5 := rfl
    rw [hn0, hn1] at hn
    exact absurd hn (by decide)
  have hmemJ : (0 : Faden) ∈ gJ.faeden := List.mem_singleton.mpr rfl
  have hWJ : TraegerSchreibt (D := gD) (gJ.code 0) (.inr ()) = true :=
    gWriteInst
  have hTJ : ∀ f ∈ gJ.faeden,
      TraegerSchreibt (D := gD) (gJ.code f) (.inr ()) = true →
      WaechterGehalten (D := gD) (gJ.code f) (.inr ()) :=
    hTouchAll
  refine ⟨gNb, gJ, (), (), 0, gGuardInst, hmemJ, hWJ, hTJ, ?_, gTabWrite, hne⟩
  exact wache_global_aus_schuld gNb gJ () () gGuardInst 0 hmemJ hWJ hTJ

/-! ## CUTS:
  - The per-body checker proof of `hTouch` (that every function body
    writing `x` establishes `WaechterGehalten` at `.inr x`) is carried
    as a premise, exactly as `wache_aus_schuld` carries coverage `hCov`
    as a premise: the discharge is per program, the theorem is the
    shape the checker feeds. The per-step instance rides on
    `fremdDisziplin_gilt` (from `TraegerInv.disziplin`), the per-body
    touch check itself stands nowhere yet.
  - STRUCTURAL DIFFERENCE (measured, not worked around): the exact
    mirror via `J.hSchuld` is impossible for globals. `SchuldnerHaelt`
    (`InterferenzAllgemein.lean`), `schuldet` (`Semantik.lean`), and
    U003 (`D.invarianten_gehalten`, `Syntax.lean`) quantify over TABLE
    carriers only (`D.traeger : Inv -> List Tab`); there is no global
    invariant-carrier list, hence no global coverage premise to mirror
    `hCov`. The mirror routes via the touch rule instead.
  - CONSTRUCTOR SURVEY (no falsifying form): every syntactic global
    writer carries `gdarf` -- `assignGlob` and `publish` via `hL`
    (`Syntax.lean`), `Block.awaits` via `hL` (it writes the received
    value through `schreibGlob`, `Semantik.lean`), `axiomCall` via
    `hgd`. All but the oracle write record a `gzugriff` event
    (`schreibGlob` = store + `merke`); the oracle write records none,
    but the mirror is static (declared holds) and needs no event, so
    no constructor falsifies it. A dynamic (world-held) analogue for
    oracle writes would route via `hgd` + `HeldGenau` (cf.
    `axiomCall_haelt_waechter`, `FremdSperre.lean`) and is not stated.
-/

#print axioms Gabbro.Grammatik.wache_global_aus_schuld
#print axioms Gabbro.Grammatik.wache_global_aus_schuld_zeuge

end Gabbro.Grammatik
