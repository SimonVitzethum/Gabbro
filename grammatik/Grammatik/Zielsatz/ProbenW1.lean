/-
  File:    Grammatik/Zielsatz/ProbenW1.lean -- the round-6 probe (finding W1) REFUTED by the
           checker, and the contrast `never` still admitted.

  THE FINDING (W1, URTEIL-OPUS-2026-09-15d.md §3, URTEIL-MUSE-2026-09-15d.md). Probe A's
  contract (`ensures false`) behind `let p = hol();`, where `hol() -> fn(sig 5)` and no
  function has signature 5. The declared answer type is EMPTY, so every run of the body ends
  at the call (`AntwortLeer`), the body obligation (b) held vacuously, the checker accepted,
  and `gabbro_ziel` certified the program -- by the stop `nieZurueck`, whose reason ("the
  continuation is unreachable in the C as in G") holds only for `-> never`: the C prototype
  of `hol` is ordinary, the call returns, and the continuation runs, covered by nothing.

  THE REFUTATION, in premise group (a):
  * `w1_spec_nicht` -- no lock family, function list or start list makes the program meet
    `AkzeptiertSpec`: its one answer site is an axiom at an empty type other than `never`;
  * `w1_abgelehnt` -- so the checker of `GabbroZiel` (`akzeptiert_pruefer`) refuses EVERY
    program with this code, whatever its lock family, axiom ensures, starts and memory;
  * `w1_bool` / `w1_sonst_alles` -- computed: the Bool is `false`, and every OTHER component
    is `true` -- the refusal is the new component `antwortenB`'s alone;
  * the same for an empty register type (`w1r_spec_nicht`, `w1r_bool`: `u8 in 1 .. 0`) and an
    axiom returning `reason` with no reasons (`w1g_bool`: `.grund 0`).
  THE CONTRAST: the same code behind an axiom `-> never` is still accepted (`w1v_bool`), and
  the head is the named stop `nieZurueck` (`w1v_kopf`): there the call really does not
  return (`_Noreturn`), and the continuation is unreachable in the C as in G.
-/
import Grammatik.Zielsatz.ProbenG1

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. The round-6 probe: an axiom returning a pointer type no function has -/

/-- `g1D` whose one axiom returns `fn(sig 5)`: no function has signature 5 (`sig = 0`). -/
def w1D : Deklaration := { g1D with aerg := fun _ => some (.fnptr 5) }

instance w1D_fn_deq : DecidableEq w1D.Fn := inferInstanceAs (DecidableEq Unit)

/-- The answer class of `hol` is empty. -/
theorem w1_leer : AntwortLeer w1D (w1D.aerg ()) := by
  intro z n
  show zeigerPasst z 5 n = none
  unfold zeigerPasst
  cases z n with
  | none => rfl
  | some f => cases f; exact dif_neg (by decide)

/-- `if true { let p = hol(); }` -/
def w1Stmt : Stmt w1D (vertragVon w1D ()) false [] [] [] :=
  .ite .wahr (.bindAxiom (τ := .fnptr 5) () .nil rfl (fun e => nomatch e) (fun e => nomatch e)
    (fun e => nomatch e) (fun e => nomatch e) .nil) .nil

/-- **The round-6 probe**: probe A's contract behind `let p = hol();`. -/
def w1P : Programm w1D where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf _ := .cons w1Stmt (.ret .keine List.Perm.nil)

def w1S : SperrInv w1D := ⟨fun L => (L : Empty).elim, fun L _ => (L : Empty).elim⟩

theorem w1_ants : (w1P.rumpf ()).ants = [.inl ()] := rfl

/-- **No lock family, function list or start list makes the probe meet `AkzeptiertSpec`**:
    its one answer site is an axiom at an empty type that is not `never`. -/
theorem w1_spec_nicht (S : SperrInv w1D) (fs ws : List w1D.Fn) : ¬ AkzeptiertSpec w1P S fs ws :=
  fun h => by
    rcases h.antworten () (.inl ()) (by rw [w1_ants]; exact List.mem_singleton_self _) with e | e
    · cases e
    · exact e w1_leer

/-- **THE REFUTATION (W1)**: the checker of `GabbroZiel` refuses every program with the
    probe's code -- whatever its lock family, axiom ensures, declared starts and initial
    memory, and for every enumeration. Before W1 it accepted -- the old conjunction is every
    other component, and those accept (`w1_sonst_alles`; the reviewers' `n_akzeptiert`,
    URTEIL-OPUS-2026-09-15d §3) -- and `gabbro_ziel` certified the program. -/
theorem w1_abgelehnt (E : Einheit w1D) (hP : E.P = w1P) (fs : Aufzaehlung w1D.Fn)
    (ls : Aufzaehlung w1D.Lock) (cs : Aufzaehlung (w1D.Tab ⊕ w1D.Glob)) :
    akzeptiert_pruefer.akzeptiert E fs.1 ls.1 cs.1 = false := by
  cases h : akzeptiert_pruefer.akzeptiert E fs.1 ls.1 cs.1
  · rfl
  · have hA := akzeptiert_pruefer.korrekt E fs ls cs h
    rw [hP] at hA
    exact absurd hA (w1_spec_nicht _ _ _)

/-- Computed: the checker's Bool on the probe (with `haupt` declared) is `false`. -/
theorem w1_bool : Akzeptiert w1P w1S [()] [] [] [()] = false := by decide

/-- Computed: every OTHER component accepts the probe -- the refusal is `antwortenB`'s. -/
theorem w1_sonst_alles :
    (programmImFragmentG w1P [()] && abgAlleB w1P [()] && fussWB w1P w1S [()] [()] &&
      stufenB w1P [()] && sperrOrteB w1S [] && wurzelnB (D := w1D) [()] &&
      einzelnB (D := w1D) [()] && rennB w1P [()] [] [()]) = true ∧
    antwortenB w1P [()] = false := by
  constructor <;> decide

/-! ## 2. The register variant: a register whose type is an empty range -/

/-- `g1D` whose register is declared `u8 in 1 .. 0`: an empty range. -/
def w1rD : Deklaration := { g1D with rtyp := fun _ => .int 1 0, rzusage := fun _ _ => true }

instance w1rD_fn_deq : DecidableEq w1rD.Fn := inferInstanceAs (DecidableEq Unit)

/-- `if true { let t = temp; }` over the empty register. -/
def w1rP : Programm w1rD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf _ := .cons (.ite .wahr (.regLies () rfl .nil) .nil) (.ret .keine List.Perm.nil)

def w1rS : SperrInv w1rD := ⟨fun L => (L : Empty).elim, fun L _ => (L : Empty).elim⟩

/-- A register never "does not return" in C: an empty register type is refused outright. -/
theorem w1r_spec_nicht (S : SperrInv w1rD) (fs ws : List w1rD.Fn) :
    ¬ AkzeptiertSpec w1rP S fs ws := fun h =>
  h.antworten () (.inr ()) (by
    show Sum.inr () ∈ (([Sum.inr ()] ++ []) ++ []) ++ []
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_singleton_self _))))
    (antwortLeer_int_leer (by decide))

theorem w1r_bool : Akzeptiert w1rP w1rS [()] [] [] [()] = false := by decide

/-! ## 3. `reason` with no reasons -/

/-- `g1D` whose axiom returns `.grund 0`. -/
def w1gD : Deklaration := { g1D with aerg := fun _ => some (.grund 0) }

instance w1gD_fn_deq : DecidableEq w1gD.Fn := inferInstanceAs (DecidableEq Unit)

def w1gP : Programm w1gD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf _ := .cons (.ite .wahr (.bindAxiom (τ := .grund 0) () .nil rfl (fun e => nomatch e)
    (fun e => nomatch e) (fun e => nomatch e) (fun e => nomatch e) .nil) .nil)
    (.ret .keine List.Perm.nil)

def w1gS : SperrInv w1gD := ⟨fun L => (L : Empty).elim, fun L _ => (L : Empty).elim⟩

theorem w1g_bool : Akzeptiert w1gP w1gS [()] [] [] [()] = false := by decide

/-! ## 4. The contrast: `never` -/

/-- `g1D` whose axiom returns `never`. -/
def w1vD : Deklaration := { g1D with aerg := fun _ => some .never }

instance w1vD_fn_deq : DecidableEq w1vD.Fn := inferInstanceAs (DecidableEq Unit)

def w1vKopf : Block w1vD (vertragVon w1vD ()) false [] [] [] :=
  .bindAxiom (τ := .never) () .nil rfl (fun e => nomatch e) (fun e => nomatch e)
    (fun e => nomatch e) (fun e => nomatch e) .nil

def w1vP : Programm w1vD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .falsch
  rumpf _ := .cons (.ite .wahr w1vKopf .nil) (.ret .keine List.Perm.nil)

def w1vS : SperrInv w1vD := ⟨fun L => (L : Empty).elim, fun L _ => (L : Empty).elim⟩

/-- **The contrast**: the same code behind an axiom `-> never` is accepted -- there the call
    really does not return (the prototype is `_Noreturn`). -/
theorem w1v_bool : Akzeptiert w1vP w1vS [()] [] [] [()] = true := by decide

/-- And its head is the named stop `nieZurueck` at every oracle, budget and world. -/
theorem w1v_kopf (O : Orakel w1vD) (passes : Nat) (σ : World w1vD) :
    KopfHalt O passes σ (.nil : Env w1vD []) .nieZurueck w1vKopf := rfl

/-- `nieZurueck` holds at NO other head: not at the round-6 probe's `hol()` (W1). -/
theorem w1_kein_nie (O : Orakel w1D) (passes : Nat) (σ : World w1D) :
    ¬ KopfHalt O passes σ (.nil : Env w1D []) .nieZurueck
      (.bindAxiom (τ := .fnptr 5) (V := vertragVon w1D ()) (l := false) (Λ' := []) () .nil rfl
        (fun e => nomatch e) (fun e => nomatch e) (fun e => nomatch e) (fun e => nomatch e) .nil :
        Block w1D (vertragVon w1D ()) false [] [] []) :=
  fun h => by cases h

#print axioms Gabbro.Grammatik.Zielsatz.w1_spec_nicht
#print axioms Gabbro.Grammatik.Zielsatz.w1_abgelehnt
#print axioms Gabbro.Grammatik.Zielsatz.w1_bool
#print axioms Gabbro.Grammatik.Zielsatz.w1_sonst_alles
#print axioms Gabbro.Grammatik.Zielsatz.w1r_spec_nicht
#print axioms Gabbro.Grammatik.Zielsatz.w1r_bool
#print axioms Gabbro.Grammatik.Zielsatz.w1g_bool
#print axioms Gabbro.Grammatik.Zielsatz.w1v_bool
#print axioms Gabbro.Grammatik.Zielsatz.w1v_kopf
#print axioms Gabbro.Grammatik.Zielsatz.w1_kein_nie

end Gabbro.Grammatik.Zielsatz
