/-
  File:      Grammatik/QLeer.lean
  Subject:   Q-CONTRACTS DEGENERATE -- the finding as theorems (lane 15).

  `Extraktion.QRequires P f` is `fun sig => forall rho, requires holds` and
  `Extraktion.QEnsures P f` is `fun sig => forall v rho, ensures holds`: the
  contract parameters (and the return value) are universally quantified AWAY
  at every world. A contract over a proper parameter therefore degenerates:
  `requires k != 0` must also hold at `k = 0`, and
  `ensures result = k + 1` must also hold at `result = 6, k = 0`.

  Proved below on a concrete one-function declaration (`qD`, parameter
  `k : int in 0 .. 5`, result `int in 1 .. 6`):

  * (1) `qRequires_nowhere`: the requires-Q is false at EVERY world;
  * (2) `qEnsures_nowhere`: the ensures-Q is false at EVERY world;
  * (3) `qSeedAll_unmoeglich_req` / `qSeedAll_unmoeglich_ens`: the `hSeedAll`
    premise of `Ziel.ziel_nutzer_last_aus_pc_Q` (head validity of both
    Q-contracts) has no inhabitant for any run that actually calls the
    function -- one theorem per leg, each deriving `False`.

  Note the bite: the body below RETURNS `k + 1` (the honest implementation),
  yet `QEnsures` is still false -- because it demands the postcondition at
  EVERY return value, including the wrong ones. That is the degeneration, not
  a bug in the body. The Q-predicates never look at the body at all.
-/
import Grammatik.Extraktion
import Grammatik.Maschine
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

/-- Signature of the single function: one parameter `k : int in 0 .. 5`,
    result `int in 1 .. 6` (so `k + 1` always fits its range). -/
def qSig : Signatur Empty Empty Empty Empty where
  params := [.int 0 5]
  erg := some (.int 1 6)
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun g => nomatch g
  konsumiert := []
  produziert := []

/-- The one-function declaration: no tables, globals, locks, marks,
    invariants, axioms, or registers. -/
def qD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun t => t.elim
  ggeteilt := fun g => nomatch g
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => qSig
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
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g
  geist := fun t => t.elim
  ggeist := fun g => nomatch g

/-- The function under test: the only inhabitant of `qD.Fn`. -/
def qfn : qD.Fn := ()

/-- `requires k != 0`: `k` is the only parameter, so this is
    `nicht (eq k 0)`. -/
def qRequires : Expr qD [.int 0 5] [] .bool :=
  .nicht (.eq (.var .hier) (.lit 0))

/-- `ensures result = k + 1`: the result (`hier`) against `k + 1`
    (`dort hier`, plus the literal `1`). -/
def qEnsures : Expr qD [.int 1 6, .int 0 5] [] .bool :=
  .eq (.var .hier) (.add (.var (.dort .hier)) (.lit 1))

/-- The honest body: it returns `k + 1`, which fits `int in 1 .. 6`. -/
def qRumpf : Endblock qD (vertragVon qD qfn) false (qD.params qfn)
    (Signatur.anfang qD (qD.signatur qfn)) :=
  .ret (.wert (.add (.var .hier) (.lit 1))) (List.Perm.refl [])

/-- The program: vacuous invariants, the two contracts above, the honest body. -/
def qP : Programm qD where
  invariante := fun i => nomatch i
  requires := fun _ => qRequires
  ensures := fun _ => qEnsures
  rumpf := fun _ => qRumpf

/-- The falsifying parameter environment: `k = 0`. -/
def rhoK0 : Env qD [.int 0 5] :=
  .cons ⟨0, by decide, by decide⟩ .nil

/-- The falsifying return value: `6` lies in `1 .. 6` (hence is a value the
    Q quantifies over) but is not `0 + 1`. -/
def vK6 : ErgVal qD (qD.erg qfn) :=
  ⟨6, by decide, by decide⟩

/-- Claim (1): `requires k != 0` as a Q-contract is false at EVERY world.
    The witness `rhoK0` (`k = 0`) is used; the world `sig` is arbitrary and
    the proof never inspects it. -/
theorem qRequires_nowhere (sig : World qD) :
    ¬ Extraktion.QRequires qP qfn sig := by
  intro h
  have he : wahr? (eval sig (qP.requires qfn) sig rhoK0) = false := rfl
  exact absurd (he.symm.trans (h rhoK0)) Bool.false_ne_true

/-- Claim (2): `ensures result = k + 1` as a Q-contract is false at EVERY
    world -- at `result = 6, k = 0`. The body returns `k + 1`, honestly; the
    Q still fails because it quantifies over every value. -/
theorem qEnsures_nowhere (sig : World qD) :
    ¬ Extraktion.QEnsures qP qfn sig := by
  intro h
  have he : wahr? (eval sig (qP.ensures qfn) sig
    (ergEnv (qD.erg qfn) vK6 rhoK0)) = false := rfl
  exact absurd (he.symm.trans (h vK6 rhoK0)) Bool.false_ne_true

/-- Claim (3a): the `hSeedAll` premise of `ziel_nutzer_last_aus_pc_Q` has no
    inhabitant for any run that calls `qfn` -- the requires leg already fails
    at the start head world. Every premise is used: `hg`/`hcode` locate the
    thread at `qfn`, `hSeedAll` supplies the head validity, `sp` names the
    head world. -/
theorem qSeedAll_unmoeglich_req {Nb : Nebeneinander}
    (J : GemeinsamerLauf (D := qD) Nb) (sp : Speicher qD) (g : Faden)
    (hg : g ∈ J.faeden) (hcode : J.code g = qfn)
    (hSeedAll : ∀ (g : Faden), g ∈ J.faeden →
      (∀ sig₀ : World qD, (GenStart sp).welten[0]? = some sig₀ →
        Extraktion.QRequires qP (J.code g) sig₀) ∧
      (∀ sig₀ : World qD, (GenStart sp).welten[0]? = some sig₀ →
        Extraktion.QEnsures qP (J.code g) sig₀)) : False := by
  obtain ⟨hReq, _⟩ := hSeedAll g hg
  have hhead : (GenStart sp).welten[0]? = some (sp.welt []) := rfl
  have hq := hReq (sp.welt []) hhead
  rw [hcode] at hq
  exact qRequires_nowhere _ hq

/-- Claim (3b): the same, through the ensures leg -- the return-value leg
    already fails at the start head world. -/
theorem qSeedAll_unmoeglich_ens {Nb : Nebeneinander}
    (J : GemeinsamerLauf (D := qD) Nb) (sp : Speicher qD) (g : Faden)
    (hg : g ∈ J.faeden) (hcode : J.code g = qfn)
    (hSeedAll : ∀ (g : Faden), g ∈ J.faeden →
      (∀ sig₀ : World qD, (GenStart sp).welten[0]? = some sig₀ →
        Extraktion.QRequires qP (J.code g) sig₀) ∧
      (∀ sig₀ : World qD, (GenStart sp).welten[0]? = some sig₀ →
        Extraktion.QEnsures qP (J.code g) sig₀)) : False := by
  obtain ⟨_, hEns⟩ := hSeedAll g hg
  have hhead : (GenStart sp).welten[0]? = some (sp.welt []) := rfl
  have hq := hEns (sp.welt []) hhead
  rw [hcode] at hq
  exact qEnsures_nowhere _ hq

end Gabbro.Grammatik

/- CUTS: what is not proved.
   - The empty-thread scope: if NO member thread runs `qfn`, `hSeedAll` is
     vacuously suppliable. Claims (3a)/(3b) are scoped to runs that call
     `qfn` (`hg`, `hcode`); the vacuous case is not ruled out and should not
     be -- it says nothing about the program.
   - No application to `ziel_nutzer_last_aus_pc_Q` itself: (3a)/(3b) show its
     `hSeedAll` premise uninhabited under the stated scope, but the corollary
     is not applied to the goal theorem (that would need the full run-side
     wiring, which is the booked remainder of section 13, not this lane).
   - No statement about `.wahr` contracts: a vacuous contract (`requires
     .wahr`) has a true Q at every world; the degeneration needs a proper
     parameter or result, as exhibited.
   - The body (`qRumpf` returns `k + 1`) is exhibited but its correctness is
     neither stated nor needed: the Q-falsity holds regardless of the body,
     which is exactly the finding.
-/
#print axioms Gabbro.Grammatik.qRequires_nowhere
#print axioms Gabbro.Grammatik.qEnsures_nowhere
#print axioms Gabbro.Grammatik.qSeedAll_unmoeglich_req
#print axioms Gabbro.Grammatik.qSeedAll_unmoeglich_ens
