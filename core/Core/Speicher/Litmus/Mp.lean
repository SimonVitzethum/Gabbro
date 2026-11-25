/-
  File:      core/Core/Speicher/Litmus/Mp.lean
  Subject:   MESSAGE PASSING (MP) catalogue entry: the two-thread shape
             `x := 1; y := 1 ‖ rF := y; rD := x` with the flag read observing `1` and the data read
             observing the old `0`.

  Source: Lahav et al., "Repairing Sequential Consistency in C/C++11" (PLDI 2017), the standard MP
  test, and the RC11 model the paper repairs. The language has no fence form: the order of an access
  is the mode of its location.

  Modes: the forbidden half needs a synchronising flag (`Graph.sw`, i.e. the flag write and read are
  at least release/acquire: `.ra` or `.sc`); the allowed half has every access `.rlx`, so the flag
  read carries no synchronisation.

  Expected: FORBIDDEN with a synchronising flag (no consistent graph has the stale data read after
  seeing the flag), ALLOWED with `.rlx` (a consistent and complete graph has it). The pair keeps the
  forbidden half non-vacuous: the refusal comes from the strength of the mode, not from impossibility.

  A mismatch with the literature would be a model finding; the negation would be proved here and
  reported, never patched over.
-/
module

public import Core.Speicher.Trennung
public import Core.Speicher.Erfuellbar
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

open MpEv

/-- **Message passing is forbidden through a synchronising flag.** `wd` (data) precedes `wf` (flag)
    in program order; `sw` reads the flag from `wf` with release/acquire strength; `rd` follows that
    read in program order. Then `rd` cannot read a write older than `wd`. Feeds: `Graph.mp_verboten`. -/
def MpRaVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
    ∃ wd wf rf' rd : E, G.po wd wf ∧ G.sw wf rf' ∧ G.po rf' rd ∧ G.rb rd wd

theorem mp_ra_verboten_kat : MpRaVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, wd, wf, rf', rd, p₁, s, p₂, r⟩
  exact Graph.mp_verboten hk p₁ s p₂ r

/-- The banned shape is realisable: the existing message-passing graph has a synchronising flag and
    a fresh data read, so its first three premises hold jointly. Feeds: `mp_konsistent`, `mpPo`,
    `mpRf`. -/
theorem mp_ra_verboten_nichtTrivial :
    ∃ (E Ort Wert : Type) (G : Graph E Ort Wert), G.Konsistent ∧
      ∃ wd wf rf' rd : E, G.po wd wf ∧ G.sw wf rf' ∧ G.po rf' rd := by
  refine ⟨MpEv, Bool, Nat, mpGraph, mp_konsistent, wx, wy, ry, rx, ?_, ?_, ?_⟩
  · show mpPo wx wy
    decide
  · apply Graph.sw_von_klassisch
    refine ⟨trivial, trivial, trivial, trivial, wy, ?_, ?_⟩
    · exact Graph.Rs.selbst trivial trivial
    · show mpRf wy ry
      decide
  · show mpPo ry rx
    decide

/-! ## The relaxed message-passing graph -/

/-- The six events: the initial writes `iX`, `iY`; thread 1 `wd; wf`; thread 2 `rF; rD`. -/
inductive MpRlxEv where
  | iX | iY | wd | wf | rF | rD
  deriving DecidableEq, Repr

open MpRlxEv

/-- Location `false` is the data `x`, `true` the flag `y`. Thread 1 writes `x := 1` then `y := 1`;
    thread 2 reads `y = 1` then `x = 0`. Every access carries the mode `m`. -/
def mpRlxLab (m : Modus) : MpRlxEv → Etikett Bool Nat
  | iX => ⟨.schreiben, false, m, 0, 0⟩
  | iY => ⟨.schreiben, true, m, 0, 0⟩
  | wd => ⟨.schreiben, false, m, 0, 1⟩
  | wf => ⟨.schreiben, true, m, 0, 1⟩
  | rF => ⟨.lesen, true, m, 1, 0⟩
  | rD => ⟨.lesen, false, m, 0, 0⟩

abbrev mpRlxPo (a b : MpRlxEv) : Prop :=
  (a = iX ∧ b ≠ iX) ∨ (a = iY ∧ b ≠ iX ∧ b ≠ iY) ∨
    (a = wd ∧ b = wf) ∨ (a = rF ∧ b = rD)

/-- The flag read observes `wf`; the data read observes the initial `iX`. -/
abbrev mpRlxRf (a b : MpRlxEv) : Prop := (a = wf ∧ b = rF) ∨ (a = iX ∧ b = rD)

abbrev mpRlxMo (a b : MpRlxEv) : Prop := (a = iX ∧ b = wd) ∨ (a = iY ∧ b = wf)

/-- The extended coherence order of this graph, in closed form. -/
abbrev mpRlxEco (a b : MpRlxEv) : Prop :=
  (a = iX ∧ (b = wd ∨ b = rD)) ∨ (a = rD ∧ b = wd) ∨
    (a = iY ∧ (b = wf ∨ b = rF)) ∨ (a = wf ∧ b = rF)

def mpRlxRang : MpRlxEv → Nat
  | iX => 0
  | iY => 1
  | wd => 2
  | wf => 3
  | rF => 4
  | rD => 5

def mpRlxGraph (m : Modus) : Graph MpRlxEv Bool Nat := ⟨mpRlxLab m, mpRlxPo, mpRlxRf, mpRlxMo⟩

theorem mpRlx_wf (m : Modus) : (mpRlxGraph m).Wohlgeformt where
  po_trans := by
    intro a b c
    show mpRlxPo a b → mpRlxPo b c → mpRlxPo a c
    cases a <;> cases b <;> cases c <;> decide
  po_irrefl := by
    intro a
    show ¬ mpRlxPo a a
    cases a <;> decide
  rf_schreibt := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_liest := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact trivial
  rf_ort := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_wert := by
    rintro w r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  rf_eindeutig := by
    rintro w w' r (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      first | exact h1.symm | exact absurd h2 (by decide)
  mo_schreibt := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨trivial, trivial⟩
  mo_ort := by
    rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl
  mo_trans := by
    intro a b c
    show mpRlxMo a b → mpRlxMo b c → mpRlxMo a c
    cases a <;> cases b <;> cases c <;> decide
  mo_irrefl := by
    intro a
    show ¬ mpRlxMo a a
    cases a <;> decide
  mo_total := by
    intro a b ha hb ho hne
    show mpRlxMo a b ∨ mpRlxMo b a
    cases a <;> cases b <;>
      first
        | decide
        | exact False.elim ha
        | exact False.elim hb
        | exact absurd rfl hne
        | (simp only [Graph.ort, mpRlxGraph, mpRlxLab, Bool.false_eq_true, Bool.true_eq_false] at ho; done)

theorem mpRlx_kein_rmw (m : Modus) (u : MpRlxEv) : ¬ (mpRlxGraph m).istRmw u := by
  intro hu
  cases u <;> simp only [Graph.istRmw, mpRlxGraph, mpRlxLab, reduceCtorEq] at hu

/-- With `.rlx` no event is strong, so there is no `sw` edge. -/
theorem mpRlx_kein_sw (a b : MpRlxEv) : ¬ (mpRlxGraph .rlx).sw a b := by
  intro h
  have hs : ((mpRlxGraph .rlx).modus a).stark := Graph.sw_stark_links h
  cases a <;> exact hs

/-- Without `sw`, happens-before is program order. -/
theorem mpRlx_hb {a b : MpRlxEv} (h : (mpRlxGraph .rlx).hb a b) : mpRlxPo a b := by
  have htr : ∀ x y z, mpRlxPo x y → mpRlxPo y z → mpRlxPo x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  refine transGen_von_trans htr (transGen_mono (fun x y hxy => ?_) h)
  rcases hxy with hpo | hsw
  · exact hpo
  · exact False.elim (mpRlx_kein_sw x y hsw)

theorem mpRlx_rb {m : Modus} {r w : MpRlxEv} (h : (mpRlxGraph m).rb r w) :
    r = rD ∧ w = wd := by
  obtain ⟨w', h1, h2, -⟩ := h
  revert h1 h2
  show mpRlxRf w' r → mpRlxMo w' w → _
  cases w' <;> cases r <;> cases w <;> decide

theorem mpRlx_eco_schritt {m : Modus} {a b : MpRlxEv} (h : (mpRlxGraph m).ecoSchritt a b) :
    mpRlxEco a b := by
  rcases h with h | h | h
  · revert h
    show mpRlxRf a b → mpRlxEco a b
    cases a <;> cases b <;> decide
  · revert h
    show mpRlxMo a b → mpRlxEco a b
    cases a <;> cases b <;> decide
  · rcases mpRlx_rb h with ⟨rfl, rfl⟩ <;> decide

theorem mpRlx_eco {m : Modus} {a b : MpRlxEv} (h : (mpRlxGraph m).eco a b) : mpRlxEco a b := by
  have htr : ∀ x y z, mpRlxEco x y → mpRlxEco y z → mpRlxEco x z := by
    intro x y z
    cases x <;> cases y <;> cases z <;> decide
  exact transGen_von_trans htr (transGen_mono (fun _ _ h => mpRlx_eco_schritt h) h)

theorem mpRlx_kein_sc (e : MpRlxEv) : ¬ (mpRlxGraph .rlx).sc e := by
  cases e <;> simp only [Graph.sc, Graph.modus, mpRlxGraph, mpRlxLab, reduceCtorEq] <;> trivial

/-- The relaxed graph with the stale data read is RC11-consistent. -/
theorem mpRlx_konsistent : (mpRlxGraph .rlx).Konsistent where
  wf := mpRlx_wf .rlx
  hb_irrefl := by
    intro a h
    have hp := mpRlx_hb h
    revert hp
    cases a <;> decide
  kohaerent := by
    intro a b hab he
    have hp := mpRlx_hb hab
    have he' := mpRlx_eco he
    revert hp he'
    cases a <;> cases b <;> decide
  atomar := by
    intro w u _ _ hu
    exact absurd hu (mpRlx_kein_rmw .rlx u)
  psc := by
    intro a h
    obtain ⟨c, hc⟩ := transGen_kopf h
    exact (mpRlx_kein_sc a) (Graph.psc_sc_links hc)
  ohneLB := by
    refine azyklisch_von_rang mpRlxRang ?_
    intro a b
    show mpRlxPo a b ∨ mpRlxRf a b → mpRlxRang a < mpRlxRang b
    cases a <;> cases b <;> decide
  liest_vorher := by
    intro w u _ hu
    exact absurd hu (mpRlx_kein_rmw .rlx u)

theorem mpRlx_vollstaendig : (mpRlxGraph .rlx).Vollstaendig := by
  intro r hr
  cases r with
  | iX => exact (hr : False).elim
  | iY => exact (hr : False).elim
  | wd => exact (hr : False).elim
  | wf => exact (hr : False).elim
  | rF => exact ⟨wf, Or.inl ⟨rfl, rfl⟩⟩
  | rD => exact ⟨iX, Or.inr ⟨rfl, rfl⟩⟩

/-- **Message passing is allowed with `rlx`.** Some consistent and complete graph, all accesses
    `.rlx`, has the flag read from the flag write and the data read from the initial data write
    (`rb` of that read to the data write). Feeds: `mpRlx_konsistent`, `mpRlx_vollstaendig`. -/
def MpRlxErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧ (∀ a, G.modus a = .rlx) ∧
      ∃ wd wf rf' rd : E, G.po wd wf ∧ G.rf wf rf' ∧ G.po rf' rd ∧ G.rb rd wd

theorem mp_rlx_erlaubt_kat : MpRlxErlaubtAussage := by
  refine ⟨MpRlxEv, Bool, Nat, mpRlxGraph .rlx, mpRlx_konsistent, mpRlx_vollstaendig, ?_,
    wd, wf, rF, rD, ?_, ?_, ?_, ?_⟩
  · intro a
    cases a <;> rfl
  · show mpRlxPo wd wf
    decide
  · show mpRlxRf wf rF
    decide
  · show mpRlxPo rF rD
    decide
  · exact ⟨iX, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, by decide⟩

/-- **The message-passing litmus statement.** The synchronising-flag ban and the relaxed allowance. -/
def MpLitmusAussage : Prop := MpRaVerbotenAussage ∧ MpRlxErlaubtAussage

theorem mp_litmus : MpLitmusAussage := ⟨mp_ra_verboten_kat, mp_rlx_erlaubt_kat⟩

end Gabbro.Core.Speicher
