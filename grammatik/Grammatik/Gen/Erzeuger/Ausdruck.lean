/-
  File:      Grammatik/Gen/Erzeuger/Ausdruck.lean
  Subject:   The CLAUSES of the expression generator, one per constructor of `Expr` and `NutzlastExpr`, and the
             typed views of a stream of expressions they pick their parts from. A clause is a `Sz` (the items of
             exact size `k`); it reads the expressions of the sizes below `k` from the stream `E`, and the
             expressions at the bodies of a quantifier from `Q` (another context, same held resources).

             Every proof argument of a rule (`darf`, `gdarf`, the range premises of a division, a shift, a
             widening) is DECIDED (`Sz.wenn`), so a generated term carries the rule's own premise as a proof.
-/
import Grammatik.Gen.Erzeuger.Groesse

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {Γ : Ctx} {Λ : List (Res D)}

/-- A typed expression with its type: the elements the generator lists. -/
abbrev SE (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : Type := Σ τ, Expr D Γ Λ τ

/-! ## Typed views -/

/-- The integer-typed expressions of a stream. -/
def intS (E : Sz (SE D Γ Λ)) : Sz (Σ lo hi : Int, Expr D Γ Λ (.int lo hi)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.int lo hi, a⟩ => some ⟨lo, hi, a⟩
    | _ => none

theorem mem_intS {E : Sz (SE D Γ Λ)} {i : Nat} {lo hi : Int} {a : Expr D Γ Λ (.int lo hi)}
    (h : (⟨.int lo hi, a⟩ : SE D Γ Λ) ∈ E i) : (⟨lo, hi, a⟩ : Σ lo hi : Int, Expr D Γ Λ (.int lo hi)) ∈ intS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The float-typed expressions of a stream. -/
def flS (E : Sz (SE D Γ Λ)) : Sz (Σ lo hi : Int × Int, Expr D Γ Λ (.fl lo hi)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.fl lo hi, a⟩ => some ⟨lo, hi, a⟩
    | _ => none

theorem mem_flS {E : Sz (SE D Γ Λ)} {i : Nat} {lo hi : Int × Int} {a : Expr D Γ Λ (.fl lo hi)}
    (h : (⟨.fl lo hi, a⟩ : SE D Γ Λ) ∈ E i) :
    (⟨lo, hi, a⟩ : Σ lo hi : Int × Int, Expr D Γ Λ (.fl lo hi)) ∈ flS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The pointer-typed expressions of a stream. -/
def ptrS (E : Sz (SE D Γ Λ)) : Sz (Σ (n : Nat) (rw : Bool), Expr D Γ Λ (.ptr n rw)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.ptr n rw, a⟩ => some ⟨n, rw, a⟩
    | _ => none

theorem mem_ptrS {E : Sz (SE D Γ Λ)} {i : Nat} {n : Nat} {rw : Bool} {a : Expr D Γ Λ (.ptr n rw)}
    (h : (⟨.ptr n rw, a⟩ : SE D Γ Λ) ∈ E i) :
    (⟨n, rw, a⟩ : Σ (n : Nat) (rw : Bool), Expr D Γ Λ (.ptr n rw)) ∈ ptrS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The function-pointer-typed expressions of a stream. -/
def fnptrS (E : Sz (SE D Γ Λ)) : Sz (Σ n : Nat, Expr D Γ Λ (.fnptr n)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.fnptr n, a⟩ => some ⟨n, a⟩
    | _ => none

theorem mem_fnptrS {E : Sz (SE D Γ Λ)} {i : Nat} {n : Nat} {a : Expr D Γ Λ (.fnptr n)}
    (h : (⟨.fnptr n, a⟩ : SE D Γ Λ) ∈ E i) : (⟨n, a⟩ : Σ n : Nat, Expr D Γ Λ (.fnptr n)) ∈ fnptrS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The option-typed expressions of a stream. -/
def optS (E : Sz (SE D Γ Λ)) : Sz (Σ n : Int, Expr D Γ Λ (.opt n)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.opt n, a⟩ => some ⟨n, a⟩
    | _ => none

theorem mem_optS {E : Sz (SE D Γ Λ)} {i : Nat} {n : Int} {a : Expr D Γ Λ (.opt n)}
    (h : (⟨.opt n, a⟩ : SE D Γ Λ) ∈ E i) : (⟨n, a⟩ : Σ n : Int, Expr D Γ Λ (.opt n)) ∈ optS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The sum-typed expressions of a stream. -/
def sumS (E : Sz (SE D Γ Λ)) : Sz (Σ cs : List (Option (Int × Int)), Expr D Γ Λ (.sum cs)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.sum cs, a⟩ => some ⟨cs, a⟩
    | _ => none

theorem mem_sumS {E : Sz (SE D Γ Λ)} {i : Nat} {cs : List (Option (Int × Int))} {a : Expr D Γ Λ (.sum cs)}
    (h : (⟨.sum cs, a⟩ : SE D Γ Λ) ∈ E i) :
    (⟨cs, a⟩ : Σ cs : List (Option (Int × Int)), Expr D Γ Λ (.sum cs)) ∈ sumS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The reason-typed expressions of a stream. -/
def whyS (E : Sz (SE D Γ Λ)) : Sz (Σ n : Nat, Expr D Γ Λ (.why n)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.why n, a⟩ => some ⟨n, a⟩
    | _ => none

theorem mem_whyS {E : Sz (SE D Γ Λ)} {i : Nat} {n : Nat} {a : Expr D Γ Λ (.why n)}
    (h : (⟨.why n, a⟩ : SE D Γ Λ) ∈ E i) : (⟨n, a⟩ : Σ n : Nat, Expr D Γ Λ (.why n)) ∈ whyS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The expressions of a given type. -/
def tyS (E : Sz (SE D Γ Λ)) (τ : Ty) : Sz (Expr D Γ Λ τ) := fun i => ofTy (E i) τ

theorem mem_tyS {E : Sz (SE D Γ Λ)} {i : Nat} {τ : Ty} {e : Expr D Γ Λ τ}
    (h : (⟨τ, e⟩ : SE D Γ Λ) ∈ E i) : e ∈ tyS E τ i := mem_ofTy h

/-! ## Variables, sum cases -/

/-- The variables of a context with the size they cost. -/
def varS (Γ : Ctx) : Sz (Σ τ, Var Γ τ) := fun c => (genVar Γ).filter fun p => decide (groesseVar p.2 = c)

theorem mem_varS {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : (⟨τ, x⟩ : Σ τ, Var Γ τ) ∈ varS Γ (groesseVar x) :=
  List.mem_filter.2 ⟨genVar_vollst Γ τ x, by simp⟩

/-- A sum case: absent (cost one) or with a payload range. -/
def fallS : Sz (Option (Int × Int)) :=
  Sz.vereint (Sz.blatt [none]) (Sz.knoten (Sz.bind paarI fun p => Sz.pure (some p)))

theorem mem_fallS [Zahlen] {c : Option (Int × Int)} (h : groesseFall c < unendlich) :
    c ∈ fallS (groesseFall c) := by
  cases c with
  | none =>
    exact Sz.mem_vereint_l (Sz.mem_blatt (by simp))
  | some p =>
    obtain ⟨lo, hi⟩ := p
    simp only [groesseFall] at h ⊢
    have h1 : Zahlen.kost lo < unendlich := by omega
    have h2 : Zahlen.kost hi < unendlich := by omega
    have hp : (lo, hi) ∈ paarI (kostI (lo, hi)) := mem_paarI rfl (by unfold kostI; simp only; omega)
    have := Sz.mem_vereint_r (A := Sz.blatt [none])
      (Sz.mem_knoten (Sz.mem_bind hp (Sz.mem_pure (some (lo, hi))))  :
        some (lo, hi) ∈ Sz.knoten (Sz.bind paarI fun p => Sz.pure (some p)) _)
    exact Sz.mem_cast this (by unfold kostI; simp only; omega)

/-- The lists of sum cases by fuel (each case costs at least one, so the length is bounded by the size). -/
def faelleS : Nat → Sz (List (Option (Int × Int)))
  | 0 => Sz.pure []
  | f + 1 => Sz.vereint (Sz.pure []) (Sz.bind fallS fun c => Sz.map (c :: ·) (faelleS f))

/-- The lists of sum cases of exact cost `k`. -/
def faelle : Sz (List (Option (Int × Int))) := fun k => faelleS k k

theorem groesseFall_pos (c : Option (Int × Int)) : 1 ≤ groesseFall c := by
  cases c with
  | none => simp [groesseFall]
  | some p => simp only [groesseFall]; omega

theorem length_le_groesseFaelle (cs : List (Option (Int × Int))) : cs.length ≤ groesseFaelle cs := by
  induction cs with
  | nil => simp [groesseFaelle]
  | cons c cs ih =>
    have := groesseFall_pos c
    simp only [groesseFaelle, List.length_cons]
    omega

theorem mem_faelleS : ∀ (f : Nat) (cs : List (Option (Int × Int))), cs.length ≤ f →
    groesseFaelle cs < unendlich → cs ∈ faelleS f (groesseFaelle cs) := by
  intro f
  induction f with
  | zero =>
    intro cs h _
    cases cs with
    | nil => exact Sz.mem_pure []
    | cons c cs => simp at h
  | succ f ih =>
    intro cs h hu
    cases cs with
    | nil => exact Sz.mem_vereint_l (Sz.mem_pure [])
    | cons c cs =>
      simp only [groesseFaelle] at hu ⊢
      have hc : c ∈ fallS (groesseFall c) := mem_fallS (by omega)
      have hr := ih cs (by simpa using h) (by omega)
      have := Sz.mem_vereint_r (A := Sz.pure [])
        (Sz.mem_bind (F := fun c' => Sz.map (c' :: ·) (faelleS f)) hc (Sz.mem_map (f := (c :: ·)) hr))
      exact this

theorem mem_faelle {cs : List (Option (Int × Int))} (hu : groesseFaelle cs < unendlich) :
    cs ∈ faelle (groesseFaelle cs) :=
  mem_faelleS _ cs (by have := length_le_groesseFaelle cs; omega) hu

/-- The payload expression of a sum case. -/
def nutzS (E : Sz (SE D Γ Λ)) : (o : Option (Int × Int)) → Sz (NutzlastExpr D Γ Λ o)
  | none => Sz.blatt [.empty]
  | some (lo, hi) => Sz.knoten (Sz.map NutzlastExpr.num (tyS E (.int lo hi)))

/-! ## The clauses -/

section Klauseln

variable (E : Sz (SE D Γ Λ))

def gLit : Sz (SE D Γ Λ) := Sz.knoten (Sz.bind zS fun n => Sz.pure ⟨.int n n, .lit n⟩)

def gBool : Sz (SE D Γ Λ) := Sz.blatt [⟨.bool, .tru⟩, ⟨.bool, .fls⟩]

def gVar (Γ : Ctx) : Sz (SE D Γ Λ) := Sz.knoten (Sz.bind (varS Γ) fun p => Sz.pure ⟨p.1, .var p.2⟩)

def gGlob : Sz (SE D Γ Λ) :=
  Sz.blatt (Aufz.glob.flatMap fun g => if h : gdarf D g Λ then [⟨D.gtyp g, .glob g h⟩] else [])

def gOldG : Sz (SE D Γ Λ) :=
  Sz.blatt (Aufz.glob.flatMap fun g => if h : gdarf D g Λ then [⟨D.gtyp g, .oldG g h⟩] else [])

def gSlot : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
    Sz.bind (tyS E (.index (D.count t))) fun i => Sz.wenn (darf D t Λ) fun h => Sz.pure ⟨_, .slot t f i h⟩)

def gOldS : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
    Sz.bind (tyS E (.index (D.count t))) fun i => Sz.wenn (darf D t Λ) fun h => Sz.pure ⟨_, .oldS t f i h⟩)

def gThru : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (ptrS E) fun ⟨n, _, p⟩ => Sz.bind (Sz.wahl Aufz.tab) fun t =>
    Sz.wenn (D.tabNr n = some t) fun ht => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
      Sz.bind (tyS E (.index (D.count t))) fun i => Sz.wenn (darf D t Λ) fun hL =>
        Sz.pure ⟨_, .thru p t ht f i hL⟩)

def gPtrOf : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind nS fun n => Sz.bind (Sz.wahl Aufz.tab) fun t =>
    Sz.wenn (D.tabNr n = some t) fun ht => Sz.bind (Sz.wahl [true, false]) fun rw =>
      Sz.pure ⟨.ptr n rw, .ptrOf t n ht rw⟩)

def gFnref : Sz (SE D Γ Λ) := Sz.blatt (Aufz.fn.map fun f => ⟨.fnptr (D.sig f), .fnref f (D.sig f) rfl⟩)

def gWiden : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨lo, hi, e⟩ => Sz.bind zS fun lo' => Sz.bind zS fun hi' =>
    Sz.wenn (lo' ≤ lo) fun h1 => Sz.wenn (hi ≤ hi') fun h2 => Sz.pure ⟨.int lo' hi', .widen h1 h2 e⟩)

def gAdd : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨_, _, b⟩ => Sz.pure ⟨_, .add a b⟩)

def gSub : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨_, _, b⟩ => Sz.pure ⟨_, .sub a b⟩)

def gNeg : Sz (SE D Γ Λ) := Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.pure ⟨_, .neg a⟩)

def gMul : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨_, _, b⟩ => Sz.pure ⟨_, .mul a b⟩)

def gDiv : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨l1, _, a⟩ => Sz.bind (intS E) fun ⟨l2, _, b⟩ =>
    Sz.wenn (0 ≤ l1) fun p0 => Sz.wenn (1 ≤ l2) fun p1 => Sz.pure ⟨_, .div p0 p1 a b⟩)

def gRem : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨l1, _, a⟩ => Sz.bind (intS E) fun ⟨l2, _, b⟩ =>
    Sz.wenn (0 ≤ l1) fun p0 => Sz.wenn (1 ≤ l2) fun p1 => Sz.pure ⟨_, .rem p0 p1 a b⟩)

def gSdiv : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨l2, h2, b⟩ =>
    Sz.wenn (1 ≤ l2 ∨ h2 ≤ -1) fun hb => Sz.pure ⟨_, .sdiv hb a b⟩)

def gSrem : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨l2, h2, b⟩ =>
    Sz.wenn (1 ≤ l2 ∨ h2 ≤ -1) fun hb => Sz.pure ⟨_, .srem hb a b⟩)

def gGetBytes : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
    Sz.wenn (D.typ t f = .int 0 255) fun hf => Sz.bind nS fun n =>
      Sz.bind (intS E) fun ⟨lo, hi, i⟩ => Sz.wenn (0 ≤ lo) fun hlo => Sz.wenn (hi + (n : Int) ≤ D.count t) fun hhi =>
        Sz.wenn (darf D t Λ) fun hL => Sz.pure ⟨_, .getBytes t f hf n i hlo hhi hL⟩)

def gBand : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨l1, _, a⟩ => Sz.bind (intS E) fun ⟨l2, _, b⟩ =>
    Sz.wenn (0 ≤ l1) fun p0 => Sz.wenn (0 ≤ l2) fun p1 => Sz.pure ⟨_, .band p0 p1 a b⟩)

def gBor : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind nS fun w => Sz.bind (intS E) fun ⟨l1, h1, a⟩ => Sz.bind (intS E) fun ⟨l2, h2, b⟩ =>
    Sz.wenn (0 ≤ l1) fun p0 => Sz.wenn (0 ≤ l2) fun p1 => Sz.wenn (h1 < 2 ^ w) fun q1 =>
      Sz.wenn (h2 < 2 ^ w) fun q2 => Sz.pure ⟨_, .bor w p0 p1 q1 q2 a b⟩)

def gBxor : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind nS fun w => Sz.bind (intS E) fun ⟨l1, h1, a⟩ => Sz.bind (intS E) fun ⟨l2, h2, b⟩ =>
    Sz.wenn (0 ≤ l1) fun p0 => Sz.wenn (0 ≤ l2) fun p1 => Sz.wenn (h1 < 2 ^ w) fun q1 =>
      Sz.wenn (h2 < 2 ^ w) fun q2 => Sz.pure ⟨_, .bxor w p0 p1 q1 q2 a b⟩)

def gShl : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind nS fun w => Sz.bind (intS E) fun ⟨l1, h1, a⟩ => Sz.bind (intS E) fun ⟨l2, h2, b⟩ =>
    Sz.wenn (h1 < 2 ^ w) fun q1 => Sz.wenn (h2 < (w : Int)) fun q2 => Sz.wenn (0 ≤ l1) fun p0 =>
      Sz.wenn (0 ≤ l2) fun p1 => Sz.pure ⟨_, .shl w q1 q2 p0 p1 a b⟩)

def gShr : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind nS fun w => Sz.bind (intS E) fun ⟨l1, h1, a⟩ => Sz.bind (intS E) fun ⟨l2, h2, b⟩ =>
    Sz.wenn (h1 < 2 ^ w) fun q1 => Sz.wenn (h2 < (w : Int)) fun q2 => Sz.wenn (0 ≤ l1) fun p0 =>
      Sz.wenn (0 ≤ l2) fun p1 => Sz.pure ⟨_, .shr w q1 q2 p0 p1 a b⟩)

def gLt : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨_, _, b⟩ => Sz.pure ⟨.bool, .lt a b⟩)

def gLe : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨_, _, b⟩ => Sz.pure ⟨.bool, .le a b⟩)

def gEq : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (intS E) fun ⟨_, _, a⟩ => Sz.bind (intS E) fun ⟨_, _, b⟩ => Sz.pure ⟨.bool, .eq a b⟩)

def gFllt : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (flS E) fun ⟨_, _, a⟩ => Sz.bind (flS E) fun ⟨_, _, b⟩ => Sz.pure ⟨.bool, .fllt a b⟩)

def gFlle : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (flS E) fun ⟨_, _, a⟩ => Sz.bind (flS E) fun ⟨_, _, b⟩ => Sz.pure ⟨.bool, .flle a b⟩)

def gAnd : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (tyS E .bool) fun a => Sz.bind (tyS E .bool) fun b => Sz.pure ⟨.bool, .and a b⟩)

def gOr : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (tyS E .bool) fun a => Sz.bind (tyS E .bool) fun b => Sz.pure ⟨.bool, .or a b⟩)

def gNot : Sz (SE D Γ Λ) := Sz.knoten (Sz.bind (tyS E .bool) fun a => Sz.pure ⟨.bool, .not a⟩)

def gNone : Sz (SE D Γ Λ) := Sz.knoten (Sz.bind zS fun n => Sz.pure ⟨.opt n, .none n⟩)

def gSome : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind zS fun n => Sz.bind (tyS E (.index n)) fun e => Sz.pure ⟨.opt n, .some e⟩)

def gIstSome : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (optS E) fun ⟨_, e⟩ => Sz.pure ⟨.bool, .istSome e⟩)

def gCase : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind faelle fun cs => Sz.bind (Sz.wahl (List.finRange cs.length)) fun i =>
    Sz.bind (nutzS E (cs.get i)) fun nz => Sz.pure ⟨.sum cs, .case cs i nz⟩)

def gWhy : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind nS fun n => Sz.bind (Sz.wahl (List.finRange n)) fun r => Sz.pure ⟨.why n, .why n r⟩)

def gReaches : Sz (SE D Γ Λ) :=
  Sz.knoten (Sz.bind (Sz.wahl Aufz.tab) fun t => Sz.bind (Sz.wahl (Aufz.feld t)) fun f =>
    Sz.wenn (D.typ t f = .opt (D.count t)) fun hf => Sz.bind (tyS E (.index (D.count t))) fun a =>
      Sz.bind (tyS E (.index (D.count t))) fun b => Sz.wenn (darf D t Λ) fun hL =>
        Sz.pure ⟨.bool, .reaches t f hf a b hL⟩)

/-- The quantifiers: the body is an expression of the extended context, drawn from `Q` up to the bound the
    budget leaves (the body has size `k - 1`). -/
def gForall (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) : Sz (SE D Γ Λ) := fun k => match k with
  | 0 => []
  | r + 1 => Aufz.tab.flatMap fun t =>
      (tyS (Q (.index (D.count t) :: Γ) r) .bool r).flatMap fun body =>
        if h : darf D t Λ then [⟨.bool, .forallSlots t body h⟩] else []

def gExists (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) : Sz (SE D Γ Λ) := fun k => match k with
  | 0 => []
  | r + 1 => Aufz.tab.flatMap fun t =>
      (tyS (Q (.index (D.count t) :: Γ) r) .bool r).flatMap fun body =>
        if h : darf D t Λ then [⟨.bool, .existsSlots t body h⟩] else []

end Klauseln

/-- **The expressions of exact size `k`**, from the expressions of the sizes below (`E`) and the expressions at
    the bodies of a quantifier (`Q`). -/
def exprS (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) (E : Sz (SE D Γ Λ)) : Sz (SE D Γ Λ) :=
  Sz.alle [gLit, gBool, gVar Γ, gGlob, gSlot E, gThru E, gPtrOf, gFnref, gOldG, gOldS E, gWiden E, gAdd E,
    gSub E, gNeg E, gMul E, gDiv E, gRem E, gSdiv E, gSrem E, gGetBytes E, gBand E, gBor E, gBxor E, gShl E,
    gShr E, gLt E, gLe E, gEq E, gFllt E, gFlle E, gAnd E, gOr E, gNot E, gNone, gSome E, gIstSome E, gCase E,
    gWhy, gForall Q, gExists Q, gReaches E]

end Gabbro.Grammatik.Gen
