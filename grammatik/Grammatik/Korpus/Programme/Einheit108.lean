/-
  File:      Grammatik/Korpus/Programme/Einheit108.lean
  Subject:   `beispiele/108-disjoint-start-locks.gab` as the goal theorem's UNIT, through the
             generic Lean pipeline: the real source text (`src108`) is parsed, elaborated and
             lowered (`uebersetzeAllg`); one table `T` (4 slots, one `u32` field), no lock, two
             readers `read_a`/`read_c`, declared `concurrent { read_a, read_c }`. The unit holds
             the parsed code, no lock invariant, no axiom, the two DECLARED starts and the zero
             memory; the checker's Bool accepts it WITH both starts, and the user's logic
             `NutzerPflicht` is proved (each body returns what it reads, `ensures` is `true`).

  (Until 2026-10-18 this was `Kette108.lean`, the 108 instance of the C correspondence chain;
  the chain was deleted with the C emitter, tag `archiv/c-emitter-2026-10-17`. The unit and
  its user logic are source-level facts and stay.)
-/
import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.Zielsatz.Kern.Beweis
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Logik.Ruf.RufLogik

namespace Gabbro.Grammatik.Einheit108

open Gabbro.Grammatik Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2 Zielsatz

set_option maxRecDepth 100000

/-! ## 1. Parse -/

abbrev D8 : Deklaration := declOf uExp108

theorem low_some : (lowerAllg uExp108).toOption.isSome = true := by decide

def P8 : Programm D8 := ((lowerAllg uExp108).toOption.get low_some).1

def fs8 : List D8.Fn := ((lowerAllg uExp108).toOption.get low_some).2

theorem parse8 : parseTopTief toks108 = .ok items108 := rfl

theorem elab8 : elabU (pre108 items108) = .ok uExp108 := rfl

theorem low8 : lowerAllg uExp108 = .ok (P8, fs8) := except_ok_get low_some

/-- **PARSE FIDELITY** of the real text, through the generic stage lemma
    (`uebersetzeAllg_von_zeichen`) -- see the note at `uebersetzt4`: the
    unfolding happens at a variable character list, so the kernel never
    decodes the source `String` (O13). -/
theorem uebersetzt8 : uebersetzeAllg src108 = .ok ⟨uExp108, P8, fs8⟩ :=
  uebersetzeAllg_von_zeichen lexL108 parse8 elab8 low8

/-! ## 2. Members and bodies -/

def t8 : D8.Tab := ⟨0, by decide⟩
def f8 : D8.Feld t8 := ⟨0, by decide⟩
def a8 : D8.Fn := ⟨0, by decide⟩
def c8 : D8.Fn := ⟨1, by decide⟩

theorem tab_eins (t : D8.Tab) : t = t8 := Fin.ext (by have h : t.val < 1 := t.isLt; show t.val = 0; omega)

theorem feld_eins (f : D8.Feld t8) : f = f8 := Fin.ext (by have h : f.val < 1 := f.isLt; show f.val = 0; omega)

theorem fn_zwei (f : D8.Fn) : f = a8 ∨ f = c8 := by
  have h : f.val < 2 := f.isLt
  rcases (by omega : f.val = 0 ∨ f.val = 1) with e | e
  · exact Or.inl (Fin.ext e)
  · exact Or.inr (Fin.ext e)

theorem kein_lock (L : D8.Lock) : False := by have h : L.val < 0 := L.isLt; omega

theorem darf8 : darf D8 t8 [] := by unfold darf; decide

/-- `read_a`'s body: `return T.slots[0].v;`. -/
def bodyA8 : Endblock D8 (vertragVon D8 a8) false (D8.params a8) [] :=
  .ret (.val (Expr.widen (lo' := 0) (hi' := 4294967295) (by decide) (by decide)
    (Expr.slot t8 f8 (.widen (by decide) (by decide) (.lit 0)) darf8))) (List.Perm.refl _)

/-- `read_c`'s body: `return T.slots[1].v;`. -/
def bodyC8 : Endblock D8 (vertragVon D8 c8) false (D8.params c8) [] :=
  .ret (.val (Expr.widen (lo' := 0) (hi' := 4294967295) (by decide) (by decide)
    (Expr.slot t8 f8 (.widen (by decide) (by decide) (.lit 1)) darf8))) (List.Perm.refl _)

theorem rumpf_a8 : P8.rumpf a8 = bodyA8 := rfl
theorem rumpf_c8 : P8.rumpf c8 = bodyC8 := rfl
theorem ens8 (f : D8.Fn) : P8.ensures f = .tru := by rcases fn_zwei f with e | e <;> subst e <;> rfl
theorem req8 (f : D8.Fn) : P8.requires f = .tru := rfl

/-! ## 3. Enumerations, unit, checker -/

def fsA : Aufzaehlung D8.Fn := ⟨[a8, c8], fun f => by
  rcases fn_zwei f with e | e <;> subst e <;> simp⟩

def lsA : Aufzaehlung D8.Lock := ⟨[], fun L => (kein_lock L).elim⟩

def csA : Aufzaehlung (D8.Tab ⊕ D8.Glob) := ⟨[.inl t8], fun c => by
  rcases c with t | g
  · rw [tab_eins t]; simp
  · exact nomatch g⟩

/-- The zero memory. -/
def sp8 : Speicher D8 where
  slots := fun t _ f => by
    have e := tab_eins t
    subst e
    rw [feld_eins f]
    exact (⟨0, by decide, by decide⟩ : Zahl 0 4294967295)
  globs := fun g => nomatch g

/-- **108 as the goal theorem's unit**: the parsed code, no lock (hence the
    empty family), no axiom, its two DECLARED starts, the zero memory. -/
def E8 : Einheit D8 where
  P := P8
  S := SperrInv.leer D8
  Q := axWahr D8
  starts := [⟨a8, .nil⟩, ⟨c8, .nil⟩]
  sp0 := sp8

/-- The checker accepts the unit WITH its two concurrent starts. -/
theorem akzeptiert8 : akzeptiert_pruefer.akzeptiert E8 fsA.1 lsA.1 csA.1 = true := by decide

/-! ## 4. The user's logic -/

theorem koerperV8 (f : D8.Fn) : KoerperGutV P8 0 f := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · unfold EnsAmRueck
    rw [ens8 f]
    rfl
  · rcases fn_zwei f with e | e <;> subst e
    · rw [rumpf_a8] at hrun
      simp only [bodyA8, execEnd] at hrun
      cases hrun
    · rw [rumpf_c8] at hrun
      simp only [bodyC8, execEnd] at hrun
      cases hrun

theorem logikFrei8 : programmLogikFrei P8 fsA.1 = true := by decide

theorem ohneEwig8 : ohneEwigB P8 fsA.1 = true := by decide

theorem koerperS8 : ∀ f : D8.Fn, KoerperGutS P8 0 (axWahr D8) (SperrInv.leer D8) f := fun f =>
  koerperGutS_leer ⟨koerperGutRQ_of_R _ (koerperGutR_of_V (koerperV8 f)),
    programmLogikFrei_ok fsA.2 logikFrei8 0 _ f⟩

/-- **THE USER'S LOGIC on 108**: the bodies at every budget; the start
    obligation: no lock invariant, and each declared start's `requires`
    (`true`) at the zero memory. -/
theorem nutzer8 : NutzerPflicht E8 where
  logik := ⟨fun passes f => ⟨koerperGutS_alle fsA.2 ohneEwig8 koerperS8 passes f, invGutS_leer rfl f,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => by
        have h := r.isLt
        have h0 : D8.gruende f = 0 := sigGruende_zero uExp108 f
        omega⟩,
    fun _ _ _ _ => rfl, axEnsLokal_wahr⟩
  start := ⟨fun L => (kein_lock L).elim, fun _ _ => rfl⟩

/-! ## 5. Witness data: the oracle -/

def O8 : Orakel D8 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem hw8 : HardwareAnnahmen O8 E8.Q :=
  And.intro (fun a => nomatch a)
    (And.intro (And.intro (fun r => nomatch r) (fun g => nomatch g)) (axVertragO_wahr O8))

#print axioms Gabbro.Grammatik.Einheit108.nutzer8

end Gabbro.Grammatik.Einheit108
