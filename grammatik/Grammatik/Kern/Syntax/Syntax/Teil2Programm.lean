module

public import Grammatik.Kern.Syntax.Syntax.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable (D : Deklaration)
variable (V : Vertrag D)

/-! ## 5. Das Programm -- Ruempfe und Vertraege zu den Signaturen -/

def vertragVon (f : D.Fn) : Vertrag D := Vertrag.vonSig D (D.signatur f)

/-- **A typed boundary clause (C08).** A closed capability annotation attached to a call
    contract alongside Boolean pre/post: input extents, output extents, fresh output
    grants and explicit releases. Bounds are nonnegative integer expressions over the
    original parameter context. Only `.ref` capabilities are representable before C12;
    any other shape stays refused, never asserted of a unit value. -/
inductive BoundaryClause (D : Deklaration) (S : Signatur D.Tab D.Glob D.Lock D.Marke) where
  | eingabe (idx : Fin S.params.length) (n : Nat) (t : D.Tab)
      (hcap : S.params.get idx = .ref n) (ht : D.tabNr n = some t)
      (m : Int) (len : Expr D S.params [] (.int 0 m))
  | ausgabe (n : Nat) (t : D.Tab) (herg : S.erg = some (.ref n)) (ht : D.tabNr n = some t)
      (m : Int) (len : Expr D S.params [] (.int 0 m))
  | frisch (n : Nat) (t : D.Tab) (herg : S.erg = some (.ref n)) (ht : D.tabNr n = some t)
  | freigabe (idx : Fin S.params.length) (n : Nat) (t : D.Tab)
      (hcap : S.params.get idx = .ref n) (ht : D.tabNr n = some t)

/-- A typed interface contract. Expressions live beside `Programm`, after
    `Expr` exists, so structural signatures remain independent of expressions.
    The postcondition covers normal returns and sees the original arguments
    together with the optional result; `old` uses the entry world. -/
structure CallContract (S : Signatur D.Tab D.Glob D.Lock D.Marke) where
  pre : Expr D S.params (Signatur.anfang D S) .bool
  post : Expr D (ErgCtx S.params S.erg) (Vertrag.vonSig D S).ende .bool
  /-- Typed boundary clauses (C08): input/output extents, fresh grants, releases. -/
  grenzen : List (BoundaryClause D S) := []

/-- Absence of predicate clauses means two true predicates. Target admission
    still owes refinement: this default never discharges a target's requires. -/
def CallContract.trivial (S : Signatur D.Tab D.Glob D.Lock D.Marke) : CallContract D S :=
  { pre := .tru, post := .tru }

/-- The trivial contract: pre/post `true`, no boundary clauses. -/
def callVertragWahr (D : Deklaration) (S : Signatur D.Tab D.Glob D.Lock D.Marke) :
    CallContract D S :=
  ⟨.tru, .tru, []⟩

def invSicht (i : D.Inv) : List (Res D) :=
  (D.traeger i).foldr (fun c acc => (Sum.elim D.braucht D.gbraucht c).map (Res.von D) ++ acc) []

/-- Ein Programm: je Funktion `requires`, `ensures` (mit `refines`: die `ensures` der
    Spezifikation sind darin enthalten -- eine Konjunktion, kein zweiter Kanal) und ein
    Rumpf, der nicht abfaellt; je Invariante ihr Praedikat. -/
structure Programm where
  invariante : ∀ i : D.Inv, Expr D [] (invSicht D i) .bool
  requires : ∀ f : D.Fn, Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool
  ensures : ∀ f : D.Fn, Expr D (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende .bool
  rumpf : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))
  /-- `entry … via idt dispatch f` (Opus agent H, 2026-09-26, OFFEN O19): `f` is entered by
      HARDWARE -- an interrupt handler, the `Kontext::unterbricht` of the Rust checker
      (`kontexte.rs`, `H102`). A thread whose root is such a function preempts the thread
      running on its core (`KernPlan`, `Zielsatz/Spec.lean`). Default: no handler, so every
      program written before this field is the program of before. -/
  unterbricht : D.Fn → Bool := fun _ => false
  /-- Contracts of function-pointer interfaces. Every admitted target needs
      `PtrVerfeinert`; structural `Deklaration.passt_ok` alone proves no
      implication between these predicates and concrete function contracts. -/
  ptrVertrag : ∀ n, CallContract D (D.sigNr n) := fun n => CallContract.trivial D (D.sigNr n)
  /-- The proved contract of every foreign item (C08): pre/post over the canonical
      signature with original arguments and entry-world `old`, plus typed boundary
      clauses. Default: the trivial contract, so every program written before this
      field is the program of before. -/
  axVertrag : ∀ a : D.Ax, CallContract D (D.asignatur a) := fun _ => callVertragWahr D _

end Gabbro.Grammatik
