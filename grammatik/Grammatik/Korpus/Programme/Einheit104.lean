/-
  File:      Grammatik/Korpus/Programme/Einheit104.lean
  Subject:   `beispiele/104-referenz.gab` as the goal theorem's UNIT, through the generic
             Lean pipeline: the real source text (`src104real`, byte-identical to the
             file) is parsed, elaborated and lowered (`uebersetzeAllg`), the program is
             an `Einheit`, the checker's Bool accepts it by `decide`, and the user's logic
             `NutzerPflicht` is proved for the parsed bodies at every budget.

  (Until 2026-10-18 this was `Kette104.lean` + `Kette104Satz.lean`, the 104 instance of the
  C correspondence chain; the chain -- emitter layout, correspondence certificate, closing
  theorem, emitted-text parse -- was deleted with the C emitter, tag
  `archiv/c-emitter-2026-10-17`. The unit, its bodies and its user logic are source-level
  facts and stay.)
-/
import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.Zielsatz.Kern.Beweis
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Logik.Ruf.RufLogik

namespace Gabbro.Grammatik.Einheit104

open Gabbro.Grammatik Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2 Zielsatz

set_option maxRecDepth 100000

/-! ## 1. Parse: the real source text, through the generic pipeline -/

abbrev D4 : Deklaration := declOf uExp104

theorem low_some : (lowerAllg uExp104).toOption.isSome = true := by decide

/-- The generically lowered program of 104. -/
def P4 : Programm D4 := ((lowerAllg uExp104).toOption.get low_some).1

def fs4 : List D4.Fn := ((lowerAllg uExp104).toOption.get low_some).2

theorem parse4 : parseTopTief tt104 = .ok items104 := rfl

/-- The lane-162 preprocessing leaves 104's elaboration unchanged. -/
theorem elab4 : elabU (pre108 items104) = .ok uExp104 := rfl

theorem low4 : lowerAllg uExp104 = .ok (P4, fs4) := except_ok_get low_some

/-- **PARSE FIDELITY** of the real text (comments included), through the
    generic stage lemma. Unfolding `uebersetzeAllg` HERE, at the concrete
    source, is what cost 70 GB (O13): `simp` looks at the discriminant
    `lex src104real` and the kernel runs the UTF-8 decoder over 2064
    bytes. `uebersetzeAllg_von_zeichen` does the unfolding once, at a
    VARIABLE character list, so nothing is decoded. -/
theorem uebersetzt4 : uebersetzeAllg src104real = .ok ⟨uExp104, P4, fs4⟩ :=
  uebersetzeAllg_von_zeichen lexL104real parse4 elab4 low4

/-! ## 2. The declaration's members, and the bodies as terms -/

def t4 : D4.Tab := ⟨0, by decide⟩
def f4 : D4.Feld t4 := ⟨0, by decide⟩
def ein4 : D4.Fn := ⟨0, by decide⟩
def lies4 : D4.Fn := ⟨1, by decide⟩
def m4 : D4.Lock := ⟨0, by decide⟩

theorem tab_eins (t : D4.Tab) : t = t4 := Fin.ext (by have h : t.val < 1 := t.isLt; show t.val = 0; omega)

theorem feld_eins (f : D4.Feld t4) : f = f4 := Fin.ext (by have h : f.val < 1 := f.isLt; show f.val = 0; omega)

theorem fn_zwei (f : D4.Fn) : f = ein4 ∨ f = lies4 := by
  have h : f.val < 2 := f.isLt
  rcases (by omega : f.val = 0 ∨ f.val = 1) with e | e
  · exact Or.inl (Fin.ext e)
  · exact Or.inr (Fin.ext e)

theorem ht4 : D4.tabNr 0 = some t4 := rfl

abbrev L4 : List (Res D4) := [Res.held (D := D4) m4]

theorem darf4 : darf D4 t4 L4 := by unfold darf; decide

theorem hp4 : RufPasst D4 (vertragVon D4 ein4) (D4.signatur lies4) L4 where
  hw := fun t _ => by rw [tab_eins t]; rfl
  hg := fun g => nomatch g
  hk := rufHk_ok uExp104 lies4 L4
  hh := fun L hL => by
    have e : L = m4 := Fin.ext (by have h : L.val < 1 := L.isLt; show L.val = 0; omega)
    subst e
    exact List.mem_singleton_self _
  hx := fun L _ hn => absurd (show L ∈ (D4.signatur lies4).haelt by
    have e : L = m4 := Fin.ext (by have h : L.val < 1 := L.isLt; show L.val = 0; omega)
    subst e
    exact List.mem_singleton_self _) hn
  hb := rufHb_ok uExp104 ein4 lies4 (by decide)

/-- `einzahlen`'s body, as the parser lowers it: the write through `k`, the
    call of `lies` on a fresh read-only pointer and `i`, the return. -/
def bodyEin4 : Endblock D4 (vertragVon D4 ein4) false (D4.params ein4) L4 :=
  .cons (Stmt.assignThru (.var .here) t4 ht4 f4 (.var (.there .here))
      (.widen (by decide) (by decide) (.lit 100)) rfl darf4)
    (.cons (Stmt.call lies4 (.cons (.ptrOf t4 0 ht4 false) (.cons (.var (.there .here)) .nil))
      hp4 rfl) (.ret .empty (List.Perm.refl _)))

/-- `lies`' body: the return of the slot read through `k`. -/
def bodyLies4 : Endblock D4 (vertragVon D4 lies4) false (D4.params lies4) L4 :=
  .ret (.val (Expr.widen (lo' := 0) (hi' := 100) (by decide) (by decide)
    (Expr.thru (.var .here) t4 ht4 f4 (.var (.there .here)) darf4))) (List.Perm.refl _)

def ensEin4 : Expr D4 (ErgCtx (D4.params ein4) (D4.erg ein4)) (vertragVon D4 ein4).ende .bool :=
  .le (Expr.oldS t4 f4 (.var (.there .here)) darf4)
    (Expr.thru (.var .here) t4 ht4 f4 (.var (.there .here)) darf4)

def ensLies4 : Expr D4 (ErgCtx (D4.params lies4) (D4.erg lies4)) (vertragVon D4 lies4).ende .bool :=
  .eq (.var .here) (Expr.thru (.var (.there .here)) t4 ht4 f4 (.var (.there (.there .here))) darf4)

/-- The lowered bodies and contracts ARE these terms (kernel-checked). -/
theorem rumpf_ein4 : P4.rumpf ein4 = bodyEin4 := rfl
theorem rumpf_lies4 : P4.rumpf lies4 = bodyLies4 := rfl
theorem ens_ein4 : P4.ensures ein4 = ensEin4 := rfl
theorem ens_lies4 : P4.ensures lies4 = ensLies4 := rfl
theorem req4 (f : D4.Fn) : P4.requires f = .tru := rfl

/-! ## 3. The enumerations of the declaration's members -/

def fsA : Aufzaehlung D4.Fn := ⟨[ein4, lies4], fun f => by
  rcases fn_zwei f with e | e <;> subst e <;> simp⟩

def lsA : Aufzaehlung D4.Lock := ⟨[m4], fun L => by
  have e : L = m4 := Fin.ext (by have h : L.val < 1 := L.isLt; show L.val = 0; omega)
  subst e; simp⟩

def csA : Aufzaehlung (D4.Tab ⊕ D4.Glob) := ⟨[.inl t4], fun c => by
  rcases c with t | g
  · rw [tab_eins t]; simp
  · exact nomatch g⟩

/-! ## 4. The unit: the parsed code, and what the source declares about its run -/

/-- The declared initial memory: every slot `0` (`static Konto Konto_speicher;`
    is zero-initialised storage). -/
def sp4 : Speicher D4 where
  slots := fun t _ f => by
    have e := tab_eins t
    subst e
    rw [feld_eins f]
    exact (⟨0, by decide, by decide⟩ : Zahl 0 100)
  globs := fun g => nomatch g

/-- **104 as the goal theorem's unit**: the parsed code; no lock invariant
    (`lock M` declares none: the empty family), no axiom (the trivial axiom
    ensures), no declared start (104 has no `concurrent`), the zero memory. -/
def E4 : Einheit D4 where
  P := P4
  S := SperrInv.leer D4
  Q := axWahr D4
  starts := []
  sp0 := sp4

/-- The checker accepts the unit, by computation. -/
theorem akzeptiert4 : akzeptiert_pruefer.akzeptiert E4 fsA.1 lsA.1 csA.1 = true := by decide

/-! ## 5. The user's logic on the parsed program -/

/-- `lies` meets its obligation: it returns the slot it reads. -/
theorem lies4_V : KoerperGutV P4 0 lies4 := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rw [rumpf_lies4] at hrun
    simp only [bodyLies4, execEnd] at hrun
    cases hrun
    unfold EnsAmRueck
    rw [ens_lies4]
    exact decide_eq_true rfl
  · rw [rumpf_lies4] at hrun
    simp only [bodyLies4, execEnd] at hrun
    cases hrun

/-- A call through the gate never fails the gate when the handler blames
    nobody (over `D4`, whose functions all require `true`). -/
theorem d4_call_tor {V : Vertrag D4} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D4)} (O : Orakel D4) (passes : Nat)
    (R : ∀ f : D4.Fn, World D4 → Env D4 (D4.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : D4.Fn) (args : Args D4 Γ Λ (D4.params g))
    (hp : RufPasst D4 V (D4.signatur g) Λ) (hr : D4.gruende g = 0) (σ : World D4)
    (ρ : Env D4 Γ) (g' : D4.Fn) :
    execStmt O passes (torRuf P4 R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf P4 R g σ1 ρ1 = R g σ1 ρ1 := fun _ _ => if_pos (by rw [req4]; rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

/-- **`einzahlen` of the parsed program meets its obligation** against
    declared frames: the write sets the slot to `100`, `lies` declares no
    write, so `old(stand) <= stand` is `old(stand) <= 100`, true by the range
    (the argument of `gP_einzahlen_R`, over the parser's declaration). -/
theorem ein4_R : KoerperGutR P4 0 ein4 := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rw [rumpf_ein4] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [execEnd] at hrun2
    simp only [execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      have hfr := (hR.2 lies4 _ _ σ2 w hRv).1.1 t4 rfl
      simp only [execStmt] at h1
      cases h1
      unfold EnsAmRueck
      rw [ens_ein4]
      show decide ((σ.slots t4 (ρ.get (.there .here)).n f4).n ≤
        (σ2.slots t4 (ρ.get (.there .here)).n f4).n) = true
      have e3 := (hfr (ρ.get (.there .here)).n f4).trans
        (storeSlot_hit (D := D4) _ t4 _ f4 _)
      have h100 : (σ2.slots t4 (ρ.get (.there .here)).n f4).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots t4 (ρ.get (.there .here)).n f4).le_hi (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · rw [rumpf_ein4] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact d4_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [execEnd] at h2
        cases h2

theorem logikFrei4 : programmLogikFrei P4 fsA.1 = true := by decide

theorem ohneEwig4 : ohneEwigB P4 fsA.1 = true := by decide

theorem koerperS4 : ∀ f : D4.Fn, KoerperGutS P4 0 (axWahr D4) (SperrInv.leer D4) f := by
  intro f
  refine koerperGutS_leer ⟨koerperGutRQ_of_R _ ?_, programmLogikFrei_ok fsA.2 logikFrei4 0 _ f⟩
  rcases fn_zwei f with e | e <;> subst e
  · exact ein4_R
  · exact koerperGutR_of_V lies4_V

/-- **THE USER'S LOGIC on 104** (the goal theorem's (b)): the bodies at every
    budget, the owed invariants (none) at value and reason exits (no reason
    exists), the empty lock family and the trivial axiom ensures read only
    their carriers; the start obligation (no lock invariant, no declared
    start). -/
theorem nutzer4 : NutzerPflicht E4 where
  logik := ⟨fun passes f => ⟨koerperGutS_alle fsA.2 ohneEwig4 koerperS4 passes f, invGutS_leer rfl f,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ r _ => by
        have h := r.isLt
        have h0 : D4.gruende f = 0 := sigGruende_zero uExp104 f
        omega⟩,
    fun _ _ _ _ => rfl, axEnsLokal_wahr⟩
  start := ⟨fun _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-! ## 6. Witness data: the oracle and the arguments of `einzahlen(k, 0, 7)` -/

/-- The oracle of `D4`: no axiom, register or global exists. -/
def O4 : Orakel D4 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem hw4 : HardwareAnnahmen O4 E4.Q :=
  And.intro (fun a => nomatch a)
    (And.intro (And.intro (fun r => nomatch r) (fun g => nomatch g)) (axVertragO_wahr O4))

/-- Gabbro's arguments of `einzahlen(k, 0, 7)`. -/
def rho7 : Env D4 (D4.params ein4) :=
  .cons () (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

#print axioms Gabbro.Grammatik.Einheit104.nutzer4

end Gabbro.Grammatik.Einheit104
