/-
  File:      Grammatik/ZielOrtGeraetAus.lean
  Subject:   THE COUNTEREXAMPLE OF `ZielOrtRegister.lean` IS EXCLUDED BY THE
             PREMISES OF `ziel_ort_geraet` -- and by which one.

  `ziel_ort_register_falsch` refutes `ziel_ort_voll` with register reads
  admitted: `rP` reads the register twice while thread 1 writes the table,
  and `rO` answers the register from that table.

  * As declared (`rD`, no device carriers for the register: the default of
    `Deklaration.rtraeger`), `rO` is NOT register-local: with no device
    carriers a local register answers the same in every world, and `rO`
    reads the table (`rO_nicht_lokal`). Every other premise of
    `ziel_ort_geraet` holds on `rP`, and a reached machine violates the
    conclusion (`ziel_ort_register_ausgeschlossen`): `RegLokal` is exactly
    the premise that fails.
  * For EVERY attribution `c` of device carriers to the register (`rDc c`,
    otherwise `rD`): if `c` is empty, the oracle is not local (and the
    footprint check passes); if `c` names the table, the oracle is local
    but the widened footprint check fails -- the reader would have the table
    in its footprint without holding its lock, and `schreiber` writes it
    (`ziel_ort_register_zuordnung`). No attribution lets the counterexample
    through.
-/
import Grammatik.ZielOrtRegister
import Grammatik.ZielOrtGeraet

namespace Gabbro.Grammatik

/-! ## 1. The counterexample as declared -/

/-- `rD` attributes no device carriers to its register (the default). -/
theorem rD_rtraeger : rD.rtraeger () = [] := rfl

/-- A world whose one slot holds `n`. -/
def rWeltN (n : Wert rD (.int 0 1)) : World rD := ⟨fun _ _ _ => n, (fun g => nomatch g), []⟩

/-- **The counterexample's oracle is not register-local**: with no device
    carriers any two worlds agree on them, yet `rO` answers `0` in one and
    `1` in the other. -/
theorem rO_nicht_lokal : ¬ RegLokal rO := by
  intro h
  have e := h.1 () (rWeltN rNull) (rWeltN rEinsW)
    ⟨fun _ ht => absurd ht List.not_mem_nil, fun g => nomatch g⟩
  have e' : (0 : Int) = 1 := e
  exact absurd e' (by decide)

theorem rP_fragmentG : programmImFragmentG rP rFs = true := by decide

theorem rP_fussG : fussOrtGB rP rFs = true := by decide

/-- **`ziel_ort_register_ausgeschlossen`.** On the counterexample of
    `ZielOrtRegister.lean` every premise of `ziel_ort_geraet` holds but
    register locality: the hardware assumption `GutO`, the complete member
    list, the widened fragment, the widened footprint check, the user
    obligation `KoerperGutG`, the start obligation and the exclusive start;
    `RegLokal rO` fails; and a reached machine violates `VertragAmOrtG`. So
    the counterexample is excluded by `RegLokal`, and by nothing else. -/
theorem ziel_ort_register_ausgeschlossen :
    ¬ RegLokal rO ∧
    GutO rO ∧ (∀ g : rD.Fn, g ∈ rFs) ∧ programmImFragmentG rP rFs = true ∧
    fussOrtGB rP rFs = true ∧ (∀ f : rD.Fn, KoerperGutG rP 0 f) ∧
    StartGut rP rSp rInit ∧ StartExklusiv (D := rD) rInit ∧
    ∃ M : RufMaschineG rD, RufErreichbarG rP rO 0 (RufStartG rP rSp rInit) M ∧
      ¬ VertragAmOrtG rP M := by
  obtain ⟨M, hr, rho, v, s0, s1, hmem, hens⟩ := rLauf
  exact ⟨rO_nicht_lokal, rO_gut, rFs_voll, rP_fragmentG, rP_fussG,
    fun f => koerperGutG_of_V (rP_koerper f), rP_start, rInit_exklusiv, M, hr,
    fun hV => hens ((hV 0 _ hmem).2 _ _ _ _ _ rfl)⟩

/-! ## 2. Every attribution of device carriers -/

/-- The declaration `rD` with the register attributed to the carriers `c`. -/
def rDc (c : List (Unit ⊕ Empty)) : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 1
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := RFn
  sig := fun | .haupt => 0 | .leser => 1 | .schreiber => 2
  sigNr := fun | 0 => rSigHaupt | 1 => rSigLeser | _ => rSigSchreiber
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Unit
  rtyp := fun _ => .int 0 1
  rklasse := fun _ => .r
  spiegel := fun _ => none
  rzusage := fun _ _ => true
  rtraeger := fun _ => c
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

section Zuordnung

variable (c : List (Unit ⊕ Empty))

abbrev rLc : List (Res (rDc c)) := [Res.held (D := rDc c) ()]

theorem rDarfC : darf (rDc c) () (rLc c) := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem rHpLeserC :
    RufPasst (rDc c) (vertragVon (rDc c) RFn.haupt) ((rDc c).signatur RFn.leser) [] where
  hw := fun t h => by cases t; exact nomatch h
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := RufPasst.hh_von (fun L => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)
  hx := RufPasst.hx_von (fun L => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)

def rLeserC : (rDc c).Fn := RFn.leser

def rLesBlockC : Block (rDc c) (vertragVon (rDc c) RFn.leser) false [] [] [] :=
  .regLies () rfl (.regLies () rfl
    (.cons (.ret (.wert (.eq (.var (.dort .hier)) (.var .hier))) List.Perm.nil) .nil))

def rRumpfLeserC : Endblock (rDc c) (vertragVon (rDc c) RFn.leser) false [] [] :=
  .cons (.ite .wahr (rLesBlockC c) .nil) (.ret (.wert .wahr) List.Perm.nil)

def rRumpfHauptC : Endblock (rDc c) (vertragVon (rDc c) RFn.haupt) false [] [] :=
  .cons (.call (rLeserC c) .nil (rHpLeserC c) rfl) (.ret .keine List.Perm.nil)

def rRumpfSchreiberC : Endblock (rDc c) (vertragVon (rDc c) RFn.schreiber) false [] (rLc c) :=
  .cons (.assignSlot () () (.weiter (by show (0 : Int) ≤ 0; decide)
      (by show (0 : Int) ≤ 1 - 1; decide) (.lit 0))
    (.weiter (by show (0 : Int) ≤ 1; decide) (by show (1 : Int) ≤ 1; decide) (.lit 1)) rfl
      (rDarfC c)) (.ret .keine (by rfl))

/-- The counterexample program over the attribution `c`. -/
def rPc : Programm (rDc c) where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .haupt => .wahr
    | .leser => .var .hier
    | .schreiber => .wahr
  rumpf
    | .haupt => rRumpfHauptC c
    | .leser => rRumpfLeserC c
    | .schreiber => rRumpfSchreiberC c

/-- The counterexample oracle over the attribution `c`: the register
    answers the table's slot. -/
def rOc : Orakel (rDc c) where
  wirkt := fun a => nomatch a
  regLies := fun _ σ => (σ.slots () 0 ()).n
  regSchreib := fun _ _ => ()
  sichtbar := fun g => nomatch g

def rFsc : List (rDc c).Fn := [RFn.haupt, RFn.leser, RFn.schreiber]

theorem rFsc_voll : ∀ g : (rDc c).Fn, g ∈ rFsc c := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem rLeserC_regs : ((rPc c).rumpf RFn.leser).regs = [(), ()] := rfl

end Zuordnung

/-- **Every attribution excludes the counterexample.** Without device
    carriers the oracle is not local (the footprint check passes); with the
    table as device carrier the oracle is local, but the reader then has
    the table in its widened footprint without holding its lock by
    signature, while `schreiber` writes it: the widened footprint check
    fails. -/
theorem ziel_ort_register_zuordnung (c : List (Unit ⊕ Empty)) :
    (c = [] → ¬ RegLokal (rOc c) ∧ fussOrtGB (rPc c) (rFsc c) = true) ∧
    (c ≠ [] → RegLokal (rOc c) ∧ fussOrtGB (rPc c) (rFsc c) = false) := by
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · subst hc
    refine ⟨fun h => ?_, by decide⟩
    have e := h.1 () ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, (fun g => nomatch g), []⟩
      ⟨fun _ _ _ => ⟨1, by decide, by decide⟩, (fun g => nomatch g), []⟩
      ⟨fun _ ht => absurd ht List.not_mem_nil, fun g => nomatch g⟩
    have e' : (0 : Int) = 1 := e
    exact absurd e' (by decide)
  · obtain ⟨x, xs, rfl⟩ : ∃ x xs, c = x :: xs := by
      cases c with
      | nil => exact absurd rfl hc
      | cons x xs => exact ⟨x, xs, rfl⟩
    have hx : x = Sum.inl () := by
      rcases x with ⟨⟩ | e
      · rfl
      · exact nomatch e
    subst hx
    refine ⟨⟨fun r σ σ' h => ?_, fun g => nomatch g⟩, ?_⟩
    · show (σ.slots () 0 ()).n = (σ'.slots () 0 ()).n
      rw [h.1 () List.mem_cons_self]
    · cases hB : fussOrtGB (rPc (Sum.inl () :: xs)) (rFsc (Sum.inl () :: xs)) with
      | false => rfl
      | true =>
          exfalso
          have hreg : () ∈ ((rPc (Sum.inl () :: xs)).rumpf RFn.leser).regs := by
            rw [rLeserC_regs]
            exact List.mem_cons_self
          have hmem : (Sum.inl () : (rDc (Sum.inl () :: xs)).Tab ⊕ (rDc (Sum.inl () :: xs)).Glob)
              ∈ fussOrteG (rPc (Sum.inl () :: xs)) RFn.leser :=
            fuss_regG (rPc (Sum.inl () :: xs)) RFn.leser () hreg (Sum.inl ()) List.mem_cons_self
          have hok := fussOrtGB_ok (rPc (Sum.inl () :: xs)) (rFsc (Sum.inl () :: xs))
            (rFsc_voll _) hB RFn.leser (Sum.inl ()) hmem
          rcases hok with ⟨L, _, hL⟩ | hfrei
          · exact nomatch hL
          · have h1 := hfrei RFn.schreiber
            exact nomatch h1

/-! ## CUTS:

  What is proved: the counterexample of `ZielOrtRegister.lean` satisfies
  every premise of `ziel_ort_geraet` except `RegLokal` and violates its
  conclusion (`ziel_ort_register_ausgeschlossen`); for every attribution of
  device carriers to its register, the counterexample fails `RegLokal` or
  the widened footprint check (`ziel_ort_register_zuordnung`).

  What is NOT proved: the analogous refutation for `awaits` (its visibility
  answer is local by `RegLokal`'s second half; no counterexample is built).
-/

#print axioms Gabbro.Grammatik.rO_nicht_lokal
#print axioms Gabbro.Grammatik.ziel_ort_register_ausgeschlossen
#print axioms Gabbro.Grammatik.ziel_ort_register_zuordnung

end Gabbro.Grammatik
