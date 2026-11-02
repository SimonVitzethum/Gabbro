module

public import Grammatik.Bausteine.Kernzelle.KernAbfrageBindung
public import Grammatik.Bausteine.Kernzelle.Verlauf

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

/-! ## 1. A two-core declaration with a hardware core query

    The fixture: two unsigned `add` cells over `0 .. 255`, two locks, three
    generated functions (query wrapper, update, reduction) and ONE hardware
    foreign item answering the running core in `0 .. 1`. The query wrapper
    binds the axiom through the C08 foreign-call path and returns its answer;
    the update calls the wrapper (so the existing `reachB` edge holds); the
    reduction returns the neutral element (read-only, hence admitted; the
    sampled fold it should return is the quiescent leg below, not admission). -/

/-- The three generated functions: query wrapper, update, reduction. -/
inductive QFn
  | q
  | u
  | f
  deriving DecidableEq, Repr

/-- One signature: parameters, result, no reasons, no locks, no writes, no floor. -/
def qASig (ps : List Ty) (e : Option Ty) : Signatur Empty (Fin 2) (Fin 2) Empty where
  params := ps
  erg := e
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []
  boden := none

def qASigNr : Nat → Signatur Empty (Fin 2) (Fin 2) Empty
  | 0 => qASig [] (some (Ty.int 0 1))
  | 1 => qASig [Ty.int 0 255] none
  | 2 => qASig [] (some (Ty.int 0 255))
  | _ => qASig [] none

def qASigOf : QFn → Nat
  | .q => 0
  | .u => 1
  | .f => 2

/-- The fixture declaration: `Empty` tables, two `add` cells, two locks, one
    hardware core-query axiom answering `0 .. 1` with no writes. -/
def qD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => (nomatch t)
  Feld := fun t => nomatch t
  decFeld := fun t => nomatch t
  typ := fun t => nomatch t
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Fin 2
  decGlob := inferInstance
  gtyp := fun _ => Ty.int 0 255
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun t => nomatch t
  ggeteilt := fun _ => false
  Lock := Fin 2
  decLock := inferInstance
  rang := fun l => (l.val : Int)
  maskiert := fun _ => true
  Marke := Empty
  decMarke := inferInstance
  stufen := fun _ => 0
  braucht := fun t => nomatch t
  gbraucht := fun g => [Sum.inl ⟨g.val, g.isLt⟩]
  eigner := fun _ => []
  Fn := QFn
  sig := qASigOf
  sigNr := qASigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Fin 1
  aparams := fun _ => []
  aerg := fun _ => some (Ty.int 0 1)
  aschreibt := fun _ t => nomatch t
  agschreibt := fun _ _ => false
  agruende := fun _ => 0
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun e => nomatch e
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e
  axHerkunft := fun _ => some .hardware
  axBeleg := fun _ => some ()

instance : DecidableEq qD.Fn := inferInstanceAs (DecidableEq QFn)

/-- The hardware core-query axiom. -/
def qAX : qD.Ax := ⟨0, by decide⟩

def qQ : QFn := .q
def qU : QFn := .u
def qF : QFn := .f

/-- Literal `0` in `0 .. 255`: the `add` neutral the reduction returns. -/
def qALitN {Γ : Ctx} {Λ : List (Res qD)} : Expr qD Γ Λ (Ty.int 0 255) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The query wrapper: bind the hardware axiom, return its answer. -/
def qARumpfQ : Endblock qD (vertragVon qD qQ) false [] [] :=
  .bindAxiom qAX Args.nil rfl
    (fun t _ => nomatch t) (fun g h => by simp at h)
    (fun t _ => nomatch t) (fun g h => by simp at h)
    (.ret (.val (.var .here)) (List.Perm.refl _))

/-- The reduction body: return the neutral `0` (read-only, hence admitted). -/
def qARumpfF : Endblock qD (vertragVon qD qF) false [] [] :=
  .ret (.val qALitN) (List.Perm.refl _)

/-- The update body: call the wrapper, then return (no value). The call edge
    is what `reachB` needs; the wrapper binds the axiom. -/
def qARumpfU : Endblock qD (vertragVon qD qU) false [Ty.int 0 255] [] :=
  .bindCall qQ Args.nil rfl
    { hw := fun t _ => nomatch t, hg := fun g h => by simp at h, hk := ⟨[], List.Perm.refl _, by simp only [List.nil_sublist]⟩, hh := fun L h => absurd h (List.not_mem_nil _) } rfl
    (.ret .empty (List.Perm.refl _))

/-- The fixture program: query wrapper, update, reduction. -/
def qAP : Programm qD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .q => qARumpfQ
    | .u => qARumpfU
    | .f => qARumpfF

/-- The fixture accumulator: two unsigned `add` cells. -/
def qA : AccumulatorDecl qD where
  name := "summe"
  kernZahl := 2
  breite := 8
  vorzeichen := false
  lo := 0
  hi := 255
  op := .add
  zellen := fun i => ⟨i.val, i.isLt⟩
  sperren := fun i => ⟨i.val, i.isLt⟩
  kernAbfrage := qQ
  aktualisiere := qU
  falte := qF

def qATabs : List qD.Tab := []

def qAGlobs : List qD.Glob := [⟨0, by decide⟩, ⟨1, by decide⟩]

theorem qAGlobs_voll : ∀ g : qD.Glob, g ∈ qAGlobs := fun g => by
  fin_cases g <;> decide

/-! ## 2. The descriptor and the connected query, decided -/

/-- The fixture `add` descriptor is valid, decided. -/
theorem qA_okB : akkuOkB qA = true := by decide

/-- The fixture descriptor is valid (non-degenerate: two cells, `add` with
    neutral `0`). -/
theorem qA_ok : akkuOk qD qA := (akkuOkB_iff).mpr qA_okB

/-- The two cells are distinct and the neutral is `0`: non-degenerate. -/
theorem qA_nichtEntartet : qA.zellen ⟨0, by decide⟩ ≠ qA.zellen ⟨1, by decide⟩ ∧
    neutralInt qA.op qA.lo qA.hi qA.breite = 0 := by
  refine ⟨by decide, rfl⟩

/-- The core-query shape holds on the fixture, decided. -/
theorem qGestaltB : kernAbfrageGestaltB qD qAX 2 qATabs qAGlobs = true := by decide

/-- The core-query shape holds: no params, answer `0 .. 1`, no channel,
    no writes. -/
theorem qGestalt : KernAbfrageGestalt qD qAX 2 :=
  (kernAbfrageGestaltB_iff (fun t => nomatch t) qAGlobs_voll).mp qGestaltB

/-- The provenance holds on the fixture, decided: hardware with a named
    witness, the one hardware premise beside `AxVertragO`. -/
theorem qHerkunftB : kernAbfrageHerkunftB qD qAX = true := by decide

/-- The provenance holds. -/
theorem qHerkunft : KernAbfrageHerkunft qD qAX :=
  kernAbfrageHerkunftB_iff.mp qHerkunftB

/-- The wrapper binds the hardware axiom through the C08 foreign-call path,
    decided. -/
theorem qBindetB : bindetAxE qAX (qAP.rumpf qQ) = true := by decide

/-- **The connected core query `_zeuge`**: shape, hardware provenance and
    the wrapper's foreign bind. -/
theorem kernAbfrage_zeuge : KernAbfrageVerbunden qAP qA qAX :=
  (kernAbfrageEinzelB_iff (fun t => nomatch t) qAGlobs_voll).mp (by decide)

/-! ## 3. The identity and the quiescent reduction -/

/-- The identity witness: on the two-core assignment, thread `0` queries `0`. -/
theorem treue_zeuge : KernAbfrageTreue (fun _ => 0) 0 0 := by decide

/-- The identity gives the query range: the answer lies in `0 .. N - 1`. -/
theorem treueBereich_zeuge : 0 ≤ (0 : Int) ∧ (0 : Int) ≤ (2 : Int) - 1 :=
  treueImBereich (N := 2) treue_zeuge (by decide)

/-- **Quiescent reduction, applied to the two `add` cells**: the sampled
    fold (per-cell folds `[3]`, `[5]`) equals the neutral-start RMW chain
    over all contributions. Typing the contributions and establishing
    quiescence are user duties; the pure reduction is `ruhigFalte`. -/
theorem ruhigAdd_zeuge :
    faltet addIntMonoid [3, 5] =
      rmwKette addIntMonoid addIntMonoid.neutral [3, 5] := by
  have h := ruhigFalte addIntMonoid [[3], [5]] [3, 5] rfl
  exact h.2

/-! ## 4. Negative twins: what the query refuses -/

/-- `N = 0` is refused: no `Fin 0` core exists. -/
theorem qN0_abgelehnt : kernAbfrageGestaltB qD qAX 0 qATabs qAGlobs = false := by decide

/-- A wrong core identity is refused: thread `0` answering `1` is not the
    running core. -/
theorem qFalscherKern_abgelehnt : ¬ KernAbfrageTreue (fun _ => 0) 0 1 := by decide

/-- An out-of-range answer is refused: `5` lies outside `0 .. 1`. -/
theorem qAusserhalb_abgelehnt : ¬ (0 ≤ (5 : Int) ∧ (5 : Int) ≤ (2 : Int) - 1) := by decide

#print axioms Gabbro.Grammatik.Kernzelle.qA_ok
#print axioms Gabbro.Grammatik.Kernzelle.qA_nichtEntartet
#print axioms Gabbro.Grammatik.Kernzelle.qGestalt
#print axioms Gabbro.Grammatik.Kernzelle.qHerkunft
#print axioms Gabbro.Grammatik.Kernzelle.kernAbfrage_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.treue_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.treueBereich_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.ruhigAdd_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.qN0_abgelehnt
#print axioms Gabbro.Grammatik.Kernzelle.qFalscherKern_abgelehnt
#print axioms Gabbro.Grammatik.Kernzelle.qAusserhalb_abgelehnt

end Gabbro.Grammatik.Kernzelle
