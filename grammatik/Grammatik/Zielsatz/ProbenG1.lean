/-
  File:    Grammatik/Zielsatz/ProbenG1.lean -- the G1 probes of the round-5 confirmation
           review, REFUTED as theorems.

  THE FINDING (G1). `einpassen` answered `none` for every raw word of a `tagged` sum, a float
  and a function pointer. So probe A's contracts (`ensures false`) behind ONE call of an axiom
  with an `ok | err` result, or behind ONE read of a float register, ended in `hardware` for
  every oracle -- (b) held, the checker accepted the program, and `gabbro_ziel` certified it.

  THE PROBES, over `g1D` (no table, no global, no lock; one function `haupt`; one axiom
  `holen() -> ok (0 .. 10) | err` writing nothing; one register `temp : f64 in 0 .. 1`
  without device carriers):
  * `g1PA` -- `if true { let x = holen(); } return;` under `ensures false`;
  * `g1PR` -- `if true { let t = temp; } return;` under `ensures false`.
  Both pass the checker (`g1PA_akzeptiert`, `g1PR_akzeptiert`), so a refusal is (b)'s.

  BOTH DIRECTIONS, per probe:
  * THE ORACLE CAN ANSWER: an oracle meeting every hardware assumption (c) whose answer FITS
    (`g1_holen_antwortet`, `g1_temp_antwortet`): the answer class is not empty any more, so
    `AxVertragO`/`RegLokal` constrain real answers;
  * THE PROGRAM IS REFUTED: no program with the code meets (b) -- `g1PA_widerlegt` whenever
    the declared ensures of `holen` holds at SOME answer (if it holds at none, (c) is the
    visible false named assumption `Q := false`, Spec's assumption list), `g1PR_widerlegt`
    for every program with that code, whatever its ensures, starts and memory.
  And the contrast (`g1_never_leer`): an axiom returning `never` has an empty answer class --
  its call is the named stop `HaltArt.nieZurueck`, not a hardware stop.
-/
import Grammatik.Zielsatz.SpecProben
import Grammatik.Zielsatz.Akzeptiert
import Grammatik.EinpassenVoll

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. The declaration -/

/-- The cases of `holen`'s result: `ok (0 .. 10)` and a bare `err`. -/
abbrev g1Fall : List (Option (Int × Int)) := [some (0, 10), none]

/-- `holen`'s result: `ok (0 .. 10) | err` -- a payload case and a bare case. -/
abbrev g1Erg : Ty := .sum g1Fall

/-- `temp`'s type: `f64 in 0 .. 1`. -/
abbrev g1Temp : Ty := .fl (0, 1) (1, 1)

/-- `haupt`: no parameter, no result, no reason, no lock, writes nothing. -/
def g1Sig : Signatur Empty Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun e => nomatch e
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def g1D : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun e => nomatch e
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun e => nomatch e
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun e => nomatch e
  eigner := fun e => nomatch e
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => g1Sig
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some g1Erg
  aschreibt := fun _ e => nomatch e
  agschreibt := fun _ e => nomatch e
  Reg := Unit
  rtyp := fun _ => g1Temp
  rklasse := fun _ => .r
  spiegel := fun _ => none
  rzusage := fun _ _ => true
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun e => nomatch e
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

instance g1D_fn_deq : DecidableEq g1D.Fn := inferInstanceAs (DecidableEq Unit)

abbrev g1Haupt : g1D.Fn := ()
abbrev g1Holen : g1D.Ax := ()
abbrev g1Reg : g1D.Reg := ()

/-! ## 2. The probes -/

/-- `if true { let x = holen(); }` -/
def g1AxStmt : Stmt g1D (vertragVon g1D g1Haupt) false [] [] [] :=
  .ite .wahr (.bindAxiom g1Holen .nil rfl (fun e => nomatch e) (fun e => nomatch e)
    (fun e => nomatch e) (fun e => nomatch e) .nil) .nil

/-- `if true { let t = temp; }` -/
def g1RegStmt : Stmt g1D (vertragVon g1D g1Haupt) false [] [] [] :=
  .ite .wahr (.regLies g1Reg rfl .nil) .nil

/-- **Probe G1-A**: probe A's contract (`ensures false`) behind one call of an axiom with an
    `ok | err` result. -/
def g1PA : Programm g1D where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf _ := .cons g1AxStmt (.ret .keine List.Perm.nil)

/-- **Probe G1-R**: probe A's contract behind one read of a float register. -/
def g1PR : Programm g1D where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf _ := .cons g1RegStmt (.ret .keine List.Perm.nil)

/-- The lock family of `g1D`: there is no lock. -/
def g1S : SperrInv g1D := ⟨fun L => (L : Empty).elim, fun L _ => (L : Empty).elim⟩

/-- Both probes pass the checker (with `haupt` declared): a refusal is (b)'s. -/
theorem g1PA_akzeptiert : Akzeptiert g1PA g1S [g1Haupt] [] [] [g1Haupt] = true := by decide

theorem g1PR_akzeptiert : Akzeptiert g1PR g1S [g1Haupt] [] [] [g1Haupt] = true := by decide

/-! ## 3. The oracles -/

/-- The raw word of `0.5` as IEEE-754 binary64 (`0x3FE0000000000000`). -/
def g1Halb : Int := 4602678819172646912

/-- An oracle: `holen` writes nothing and answers the raw word `w`; `temp` answers `t`. -/
def g1O (w t : Int) : Orakel g1D where
  wirkt := fun _ σ _ => (σ, w)
  regLies := fun _ _ => t
  regSchreib := fun _ _ => ()
  sichtbar := fun e => nomatch e

theorem g1O_gut (w t : Int) : GutO (g1O w t) := fun _ σ _ =>
  ⟨Rahmen.refl _ _ σ, rfl, fun _ _ =>
    ⟨[], [], [], ⟨fun t _ => (t : Empty).elim, fun g _ => (g : Empty).elim,
      fun t _ => (t : Empty).elim, fun g _ => (g : Empty).elim,
      fun _ _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, rfl⟩⟩⟩

theorem g1O_rahmen (w t : Int) : RahmenO (g1O w t) := gutO_rahmenO (g1O_gut w t)

theorem g1O_lokal (w t : Int) : RegLokal (g1O w t) :=
  ⟨fun _ _ _ _ => rfl, fun e => nomatch e⟩


/-- The decoded `0.5`, as a value of `f64 in 0 .. 1` (the three facts evaluated by the
    kernel: `decide +kernel`, no native code). -/
def g1HalbW : Gleit (0, 1) (1, 1) :=
  ⟨Gleitkomma.ausBits Gleitkomma.f64 g1Halb.toNat, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- The word of `0.5` decodes to `g1HalbW`. -/
theorem g1_temp_wort : gleitWortPasst (0, 1) (1, 1) g1Halb = some g1HalbW := by
  unfold gleitWortPasst
  rw [if_pos (by decide +kernel : 0 ≤ g1Halb ∧ g1Halb < gleitWortGrenze)]
  unfold gleitPasst
  rw [dif_pos ⟨g1HalbW.endlich, g1HalbW.lo_le, g1HalbW.le_hi⟩]
  rfl

theorem g1_temp_dekodiert (σ : World g1D) :
    einpassen (g1O 3 g1Halb).zeiger (g1D.rtyp g1Reg) ((g1O 3 g1Halb).regLies g1Reg σ) =
      some g1HalbW := g1_temp_wort

/-- `temp` answering `0.5`: the word decodes, in range. -/
theorem g1_temp_passt : ∃ v, einpassen (D := g1D) (fun _ => none) g1Temp g1Halb = some v :=
  ⟨g1HalbW, g1_temp_wort⟩

theorem g1_rzusage (v : Wert g1D (g1D.rtyp g1Reg)) : g1D.rzusage g1Reg v = true := rfl

/-- A word no `ok | err` value has: case `1` (`err`, bare) with payload `1`. -/
theorem g1_holen_schief : einpassenErg (D := g1D) (fun _ => none) (g1D.aerg g1Holen) 3 = none :=
  rfl

/-- The oracle answering the bad word meets EVERY declared ensures of `holen`. -/
theorem g1O_schief_vertrag (Q : AxEns g1D) (t : Int) : AxVertragO Q (g1O 3 t) := by
  intro a σ ρ v hv
  have h : einpassenErg (D := g1D) (fun _ => none) (g1D.aerg g1Holen) 3 = some v := hv
  rw [g1_holen_schief] at h
  cases h

/-- The value of the answer `summeRoh v`. -/
theorem g1_holen_dekodiert (v : Wert g1D g1Erg) (t : Int) (σ : World g1D) :
    axiomAntwort (g1O (summeRoh g1Fall v) t) g1Holen σ .nil = (σ, some v) := by
  show (σ, summePasst g1Fall (summeRoh g1Fall v)) = (σ, some v)
  exact congrArg (Prod.mk σ) (summePasst_voll g1Fall v)

/-! ## 4. Both directions -/

/-- **The oracle can answer `holen`** (G1, direction 1): for a declared ensures that holds at
    some answer, an oracle meets every hardware assumption (c) and its answer FITS the
    `ok | err` type -- the answer class is not empty any more. -/
theorem g1_holen_antwortet (Q : AxEns g1D) (hlok : AxEnsLokal Q)
    (v : Wert g1D g1Erg) (σ₀ : World g1D) (hq : Q g1Holen σ₀ v = true) :
    ∃ O : Orakel g1D, HardwareAnnahmen O Q ∧
      ∀ σ : World g1D, (axiomAntwort O g1Holen σ .nil).2 = some v := by
  refine ⟨g1O (summeRoh g1Fall v) 0, ⟨g1O_gut _ _, g1O_lokal _ _, ?_⟩, fun σ => ?_⟩
  · intro a σ ρ u hu
    cases a
    have hρ : ρ = .nil := by cases ρ; rfl
    subst hρ
    have e : some u = some v := by
      have := congrArg Prod.snd (g1_holen_dekodiert v 0 σ)
      exact hu.symm.trans this
    obtain rfl : u = v := Option.some.inj e
    exact (hlok g1Holen σ σ₀ u (fun t _ => (t : Empty).elim) (fun g _ => (g : Empty).elim)).trans hq
  · exact congrArg Prod.snd (g1_holen_dekodiert v 0 σ)

/-- **The oracle can answer `temp`**: an oracle meets every hardware assumption, whatever the
    declared ensures, and its register answer `0.5` FITS `f64 in 0 .. 1`. -/
theorem g1_temp_antwortet (Q : AxEns g1D) :
    ∃ O : Orakel g1D, HardwareAnnahmen O Q ∧
      ∀ σ : World g1D, ∃ v, einpassen O.zeiger (g1D.rtyp g1Reg) (O.regLies g1Reg σ) = some v :=
  ⟨g1O 3 g1Halb, ⟨g1O_gut _ _, g1O_lokal _ _, g1O_schief_vertrag Q _⟩, fun _ => g1_temp_passt⟩

/-- The handler that answers every call with a hardware stop (the probes call nothing). -/
def g1Ruf : ∀ f : g1D.Fn, World g1D → Env g1D (g1D.params f) → RufAusgang f :=
  fun _ _ _ => .hardware (.annahme g1Holen)

theorem g1Ruf_rahmen (P : Programm g1D) : RespektiertRahmen P g1Ruf :=
  ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩

theorem g1Ruf_ohne : OhneVorbedingung g1Ruf := fun _ _ _ _ h => by cases h

/-- The move class of the lock-free `g1D` is inhabited. -/
theorem g1_havoc (S : SperrInv g1D) : HavocOk S (fun L => nomatch L) := fun L => (L : Empty).elim

/-- Probe G1-A's body returns once `holen` answered a fitting value. -/
theorem g1PA_lauf0 (v : Wert g1D g1Erg) (σ : World g1D) :
    ∃ σ', execEnd (V := vertragVon g1D g1Haupt) (g1O (summeRoh g1Fall v) 0) 0 g1Ruf
      (g1PA.rumpf g1Haupt) σ .nil = .zurueck σ' () := by
  simp only [g1PA, g1AxStmt, execEnd, execStmt, execBlock, eval, wahr?, if_true, evalArgs,
    g1_holen_dekodiert, Ausgang.schrumpf, evalErg]
  exact ⟨_, rfl⟩

theorem g1PA_lauf (v : Wert g1D g1Erg) (S : SperrInv g1D) (σ : World g1D) :
    ∃ σ', execEndH (V := vertragVon g1D g1Haupt) S (g1O (summeRoh g1Fall v) 0) (fun L => nomatch L) 0
      g1Ruf (g1PA.rumpf g1Haupt) σ .nil = .zurueck σ' () := by
  obtain ⟨σ', h⟩ := g1PA_lauf0 v σ
  exact ⟨σ', (Endblock.execH_ohne S _ _ 0 g1Ruf _ rfl σ .nil).trans h⟩

/-- Probe G1-R's body returns once `temp` answered `0.5` -- by computation, the float decoded
    by the kernel. -/
theorem g1PR_lauf0 (σ : World g1D) :
    ∃ σ', execEnd (V := vertragVon g1D g1Haupt) (g1O 3 g1Halb) 0 g1Ruf
      (g1PR.rumpf g1Haupt) σ .nil = .zurueck σ' () := by
  simp only [g1PR, g1RegStmt, execEnd, execStmt, execBlock, eval, wahr?, if_true,
    g1_temp_dekodiert, Ausgang.schrumpf, evalErg]
  exact ⟨_, rfl⟩

theorem g1PR_lauf (S : SperrInv g1D) (σ : World g1D) :
    ∃ σ', execEndH (V := vertragVon g1D g1Haupt) S (g1O 3 g1Halb) (fun L => nomatch L) 0
      g1Ruf (g1PR.rumpf g1Haupt) σ .nil = .zurueck σ' () := by
  obtain ⟨σ', h⟩ := g1PR_lauf0 σ
  exact ⟨σ', (Endblock.execH_ohne S _ _ 0 g1Ruf _ rfl σ .nil).trans h⟩

/-- **Probe G1-A is refuted** (G1, direction 2): no program with its code meets (b) --
    whenever the declared ensures of `holen` holds at SOME answer. (If it holds at none,
    `AxVertragO` admits only oracles whose answers never fit: that is `Q := false`, the
    visible false named assumption of Spec's list, not a stop the model decides.) -/
theorem g1PA_widerlegt (E : Einheit g1D) (hP : E.P = g1PA)
    (hQ : ∃ (v : Wert g1D g1Erg) (σ₀ : World g1D), E.Q g1Holen σ₀ v = true) :
    ¬ NutzerPflicht E := by
  obtain ⟨P, S, Q, st, s⟩ := E
  obtain rfl : P = g1PA := hP
  intro h
  obtain ⟨v, σ₀, hq⟩ := hQ
  have hAV : AxVertragO Q (g1O (summeRoh g1Fall v) 0) := by
    intro a σ ρ u hu
    cases a
    have hρ : ρ = .nil := by cases ρ; rfl
    subst hρ
    have e : some u = some v := hu.symm.trans (congrArg Prod.snd (g1_holen_dekodiert v 0 σ))
    obtain rfl : u = v := Option.some.inj e
    exact (h.logik.2.2 g1Holen σ σ₀ u (fun t _ => (t : Empty).elim)
      (fun g _ => (g : Empty).elim)).trans hq
  have hK := (h.logik.1 0 g1Haupt).1.1 (g1O (summeRoh g1Fall v) 0) (g1O_rahmen _ _)
    (g1O_lokal _ _) hAV (fun L => nomatch L) (g1_havoc S) g1Ruf (g1Ruf_rahmen g1PA) g1Ruf_ohne
    (s.welt []) .nil rfl
  obtain ⟨σ', hrun⟩ := g1PA_lauf v S (s.welt [])
  exact Bool.false_ne_true (hK.1 σ' () hrun)

/-- **Probe G1-R is refuted**: no program with its code meets (b) -- whatever its lock
    family, declared axiom ensures, starts and initial memory. -/
theorem g1PR_widerlegt : NutzerWiderlegt g1PR := by
  rintro ⟨P, S, Q, st, s⟩ hP h
  obtain rfl : P = g1PR := hP
  have hK := (h.logik.1 0 g1Haupt).1.1 (g1O 3 g1Halb) (g1O_rahmen _ _) (g1O_lokal _ _)
    (g1O_schief_vertrag Q _) (fun L => nomatch L) (g1_havoc S) g1Ruf (g1Ruf_rahmen g1PR)
    g1Ruf_ohne (s.welt []) .nil rfl
  obtain ⟨σ', hrun⟩ := g1PR_lauf S (s.welt [])
  exact Bool.false_ne_true (hK.1 σ' () hrun)

/-! ## 5. The contrast: `never` -/

/-- An axiom returning `never` has an EMPTY answer class: its call does not return. G names
    that stop `HaltArt.nieZurueck`; it is not a hardware stop, and the obligation (b) still
    covers every statement before the call (outcomes before it are outcomes of the body). -/
theorem g1_never_leer : AntwortLeer g1D (some .never) := antwortLeer_never

/-- The G1 types are not empty: `ok | err` and `f64 in 0 .. 1` have answers. -/
theorem g1_nicht_leer : ¬ AntwortLeer g1D (some g1Erg) ∧ ¬ AntwortLeer g1D (some g1Temp) := by
  refine ⟨nicht_leer_von g1Erg (⟨⟨1, by decide⟩, ()⟩ : Wert g1D g1Erg) trivial, ?_⟩
  obtain ⟨v, hv⟩ := g1_temp_passt
  exact nicht_leer_von g1Temp v (einpassen_wertOk _ _ _ v hv)

#print axioms Gabbro.Grammatik.Zielsatz.g1PA_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.g1PR_akzeptiert
#print axioms Gabbro.Grammatik.Zielsatz.g1_holen_antwortet
#print axioms Gabbro.Grammatik.Zielsatz.g1_temp_antwortet
#print axioms Gabbro.Grammatik.Zielsatz.g1PA_widerlegt
#print axioms Gabbro.Grammatik.Zielsatz.g1PR_widerlegt
#print axioms Gabbro.Grammatik.Zielsatz.g1_nicht_leer

end Gabbro.Grammatik.Zielsatz
