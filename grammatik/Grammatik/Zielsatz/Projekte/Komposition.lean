import Grammatik.Zielsatz.Atomar.BeweisAtomar

/-!
  File:      Grammatik/Zielsatz/Projekte/Komposition.lean
  Subject:   LINKING PROJECTS, the whole program as the guarantee carrier (`BUILD-SYSTEM.md` §7, 2026-10-25).

  A program linked from several PROJECTS -- each with its own source, its own build file, its own
  proofs -- is ONE unit for the checker and for `GabbroZiel`: every leg holds across project
  boundaries by the statement as it stands. What the boundary adds is REUSE: each project's own
  proof of its bodies, its own axiom ensures and its own start must compose into the program's,
  without re-proving a project in every program that links it.

  * `Projekt` -- a project: the functions it owns (`eigen`) and its unit (its bodies for its own
    functions; the heads of the link declaration for the rest).
  * `komponiere B ps` -- the composed unit over the link declaration `B` (contracts, lock
    families, initial memory): every function's body from the first project that owns it, every
    project's starts, run-time roots and arenas, and the CONJUNCTION of the projects' axiom
    ensures (`qAlle`) -- projects may declare different ensures for one axiom; the program
    assumes all of them.
  * `OffenA` -- the OPEN-WORLD rely: every unguarded atomic a body can read. It contains the
    shared atomics (`GeteiltA`) of EVERY program, so a body proved against it stays proved in
    every composition: a program that starts more threads into a library makes more atomics
    shared, never more than `OffenA`.
  * `NutzerTeilO` -- one project's user obligation: its own bodies against the open-world rely
    and its own axiom ensures, its lock and axiom families local, its start.
  * `nutzerPflichtA_komponiere` -- (b) of the composed unit from the projects' parts.
-/

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Projects and their composition -/

/-- **A project of a linked program**: the functions it owns, and its unit. -/
structure Projekt (D : Deklaration) where
  eigen : D.Fn → Bool
  E : Einheit D

/-- The body of `f` in the composed program: the one of the first project that owns `f`. -/
def koerperVon (B : Programm D) (ps : List (Projekt D)) (f : D.Fn) :
    Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) :=
  match ps.find? (fun p => p.eigen f) with
  | some p => p.E.P.rumpf f
  | none => B.rumpf f

/-- **The composed program**: the link declaration's contracts, every body from its owner. -/
def komponiereP (B : Programm D) (ps : List (Projekt D)) : Programm D :=
  mitRumpf B (koerperVon B ps)

/-- **The program's axiom ensures**: every project's, at once. -/
def qAlle (ps : List (Projekt D)) : AxEns D :=
  fun a σ v => ps.all (fun p => p.E.Q a σ v)

/-- **The composed unit.** -/
def komponiere (B : Einheit D) (ps : List (Projekt D)) : Einheit D where
  P := komponiereP B.P ps
  S := B.S
  Q := qAlle ps
  starts := ps.flatMap (·.E.starts)
  sp0 := B.sp0
  gestartet := ps.flatMap (·.E.gestartet)
  arenen := ps.flatMap (·.E.arenen)

/-- Every function is owned by some project of the list. -/
def Deckend (ps : List (Projekt D)) : Prop := ∀ f, ∃ p ∈ ps, p.eigen f = true

theorem koerperVon_besitzer {B : Programm D} {ps : List (Projekt D)} (h : Deckend ps) (f : D.Fn) :
    ∃ p ∈ ps, p.eigen f = true ∧ koerperVon B ps f = p.E.P.rumpf f := by
  unfold koerperVon
  cases hf : ps.find? (fun p => p.eigen f) with
  | none =>
    obtain ⟨p, hp, he⟩ := h f
    exact absurd he (by simpa using List.find?_eq_none.mp hf p hp)
  | some p =>
    exact ⟨p, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl⟩

/-! ## 2. The open-world rely -/

/-- **The open-world rely**: an unguarded atomic. -/
def OffenA (c : D.Tab ⊕ D.Glob) : Prop :=
  AtomarAusgenommen c ∧ ∀ L, ¬ Bewacht c L

/-- Every shared atomic of every program is in the open-world rely. -/
theorem geteiltA_offen [DecidableEq D.Fn] {P : Programm D} {ws : List D.Fn} {c : D.Tab ⊕ D.Glob}
    (h : GeteiltA P ws c) : OffenA c :=
  ⟨h.1, h.2.1⟩

/-- **One project's user obligation** (the part of (b) a project owes, reusable in every
    program that links it): its own bodies against the open-world rely. -/
structure NutzerTeilO (p : Projekt D) : Prop where
  logik : (∀ (passes : Nat) (f : D.Fn), p.eigen f = true →
      KoerperGutSA p.E.P passes p.E.Q p.E.S OffenA f ∧
        InvGutSA p.E.P passes p.E.Q p.E.S OffenA f ∧
        InvGutGrundA p.E.P passes p.E.Q p.E.S OffenA f) ∧
    SperrInvLokal p.E.S ∧ AxEnsLokal p.E.Q
  start : StartPflicht p.E

/-! ## 3. Monotonicity: stronger ensures, one body -/

/-- A stronger axiom ensures is a weaker obligation: fewer oracles to answer against. -/
theorem koerperGutSA_Q {P : Programm D} {passes : Nat} {Q Q' : AxEns D} {S : SperrInv D}
    {T : D.Tab ⊕ D.Glob → Prop} {f : D.Fn} (hQ : ∀ O, AxVertragO Q' O → AxVertragO Q O)
    (h : KoerperGutSA P passes Q S T f) : KoerperGutSA P passes Q' S T f :=
  ⟨fun O' a b c => h.1 O' a b (hQ O' c), fun O' a b c => h.2 O' a b (hQ O' c)⟩

theorem invGutSA_Q {P : Programm D} {passes : Nat} {Q Q' : AxEns D} {S : SperrInv D}
    {T : D.Tab ⊕ D.Glob → Prop} {f : D.Fn} (hQ : ∀ O, AxVertragO Q' O → AxVertragO Q O)
    (h : InvGutSA P passes Q S T f) : InvGutSA P passes Q' S T f :=
  fun O' a b c => h O' a b (hQ O' c)

theorem invGutGrundA_Q {P : Programm D} {passes : Nat} {Q Q' : AxEns D} {S : SperrInv D}
    {T : D.Tab ⊕ D.Glob → Prop} {f : D.Fn} (hQ : ∀ O, AxVertragO Q' O → AxVertragO Q O)
    (h : InvGutGrundA P passes Q S T f) : InvGutGrundA P passes Q' S T f :=
  fun O' a b c => h O' a b (hQ O' c)

theorem axVertragO_qAlle {ps : List (Projekt D)} {p : Projekt D} (hp : p ∈ ps) {O : Orakel D}
    (h : AxVertragO (qAlle ps) O) : AxVertragO p.E.Q O := by
  intro a σ ρ v hv
  have := h a σ ρ v hv
  simp only [qAlle, List.all_eq_true] at this
  exact this p hp

theorem axEnsLokal_qAlle {ps : List (Projekt D)} (h : ∀ p ∈ ps, AxEnsLokal p.E.Q) :
    AxEnsLokal (qAlle ps) := by
  intro a σ σ' v h1 h2
  unfold qAlle
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.all_cons]
    rw [h p List.mem_cons_self a σ σ' v h1 h2,
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

section Kongruenz

variable (P : Programm D)

/-- The body obligation reads the program's contracts and ONE body. -/
theorem koerperGutSA_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop) (f : D.Fn)
    (h : r f = r' f) :
    KoerperGutSA (mitRumpf P r) passes Q S T f ↔ KoerperGutSA (mitRumpf P r') passes Q S T f := by
  unfold KoerperGutSA
  have e : (mitRumpf P r).rumpf f = (mitRumpf P r').rumpf f := h
  rw [e]
  exact Iff.rfl

theorem invGutSA_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop) (f : D.Fn)
    (h : r f = r' f) :
    InvGutSA (mitRumpf P r) passes Q S T f ↔ InvGutSA (mitRumpf P r') passes Q S T f := by
  unfold InvGutSA
  have e : (mitRumpf P r).rumpf f = (mitRumpf P r').rumpf f := h
  rw [e]
  exact Iff.rfl

theorem invGutGrundA_mitRumpf2
    (r r' : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop) (f : D.Fn)
    (h : r f = r' f) :
    InvGutGrundA (mitRumpf P r) passes Q S T f ↔ InvGutGrundA (mitRumpf P r') passes Q S T f := by
  unfold InvGutGrundA
  have e : (mitRumpf P r).rumpf f = (mitRumpf P r').rumpf f := h
  rw [e]
  exact Iff.rfl

end Kongruenz

/-! ## 4. (b) composes -/

section Pflicht

variable [DecidableEq D.Fn] {B : Einheit D} {ps : List (Projekt D)}

/-- **The user's duty of the composed unit is the projects' duties.** Every body is proved by
    the project that owns it, against the open-world rely (which contains the program's shared
    atomics, however many threads the program starts into it) and its own axiom ensures (which
    the program's conjunction implies); the start is each project's. -/
theorem nutzerPflichtA_komponiere (hV : ∀ p ∈ ps, Verbindbar B p.E) (hne : ps ≠ [])
    (hD : Deckend ps) (hN : ∀ p ∈ ps, NutzerTeilO p) :
    NutzerPflichtA (komponiere B ps) := by
  obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil ps hne
  refine ⟨⟨fun passes f => ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨p, hp, he, hk⟩ := koerperVon_besitzer (B := B.P) hD f
    obtain ⟨k, i, g⟩ := (hN p hp).logik.1 passes f he
    have hP : p.E.P = mitRumpf B.P p.E.P.rumpf := p2_eq (hV p hp)
    have hS : p.E.S = B.S := (hV p hp).sperren.symm
    rw [hP, hS] at k i g
    have hQ : ∀ O, AxVertragO (qAlle ps) O → AxVertragO p.E.Q O := fun O => axVertragO_qAlle hp
    have hT : ∀ c, GeteiltA (komponiere B ps).P (komponiere B ps).ws c → OffenA c :=
      fun c hc => geteiltA_offen hc
    exact ⟨(koerperGutSA_mitRumpf2 B.P _ _ passes _ _ _ f hk).mpr
        (koerperGutSA_mono hT (koerperGutSA_Q hQ k)),
      (invGutSA_mitRumpf2 B.P _ _ passes _ _ _ f hk).mpr (invGutSA_mono hT (invGutSA_Q hQ i)),
      (invGutGrundA_mitRumpf2 B.P _ _ passes _ _ _ f hk).mpr
        (invGutGrundA_mono hT (invGutGrundA_Q hQ g))⟩
  · show SperrInvLokal B.S
    rw [(hV p0 hp0).sperren]
    exact (hN p0 hp0).logik.2.1
  · exact axEnsLokal_qAlle fun p hp => (hN p hp).logik.2.2
  · intro L
    show B.S.inv L B.sp0 = true
    rw [(hV p0 hp0).sperren, (hV p0 hp0).speicher]
    exact (hN p0 hp0).start.sperren L
  · intro a ha
    show ReqAmEintritt (komponiereP B.P ps) a.1 (B.sp0.welt []) a.2
    have hq : a ∈ (ps.flatMap (·.E.starts)) ++ ps.flatMap (·.E.gestartet) := ha
    obtain ⟨p, hp, hap⟩ : ∃ p ∈ ps, a ∈ p.E.starts ++ p.E.gestartet := by
      rcases List.mem_append.mp hq with h | h
      · obtain ⟨p, hp, h'⟩ := List.mem_flatMap.mp h
        exact ⟨p, hp, List.mem_append_left _ h'⟩
      · obtain ⟨p, hp, h'⟩ := List.mem_flatMap.mp h
        exact ⟨p, hp, List.mem_append_right _ h'⟩
    have := (hN p hp).start.req a hap
    unfold ReqAmEintritt at this ⊢
    have e1 : (komponiereP B.P ps).requires = p.E.P.requires := (hV p hp).requires
    rw [e1, (hV p hp).speicher]
    exact this

end Pflicht

#print axioms nutzerPflichtA_komponiere

end Gabbro.Grammatik.Zielsatz
