/-
  File:      Grammatik/Gen/Erzeuger/Hilfen.lean
  Subject:   The pieces the statement generators share: the recursion record `Rek` (the generated statements,
             blocks and end blocks of one fuel), generic matchers on integer-typed and optional-typed indices,
             the generators of argument lists, result expressions and match arms, each with its completeness
             lemma.
-/
import Grammatik.Gen.Erzeuger.AusdruckVollst
import Grammatik.Gen.Erzeuger.Entscheidung
import Grammatik.Gen.Erzeuger.Groesse

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A statement with its held resources after it. -/
abbrev SS (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : Type :=
  Σ Λ' : List (Res D), Stmt D V l Γ Λ Λ'

/-- A block with its held resources after it. -/
abbrev SB (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : Type :=
  Σ Λ' : List (Res D), Block D V l Γ Λ Λ'

/-- The generated statements, blocks and end blocks of one fuel, at every context. -/
structure Rek (V : Vertrag D) where
  st : ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)), List (SS D V l Γ Λ)
  bl : ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)), List (SB D V l Γ Λ)
  en : ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)), List (Endblock D V l Γ Λ)

/-! ## Matchers on indices -/

variable {Γ : Ctx} {Λ : List (Res D)}

/-- The integer-typed terms of a list, with any result type `R`. -/
def mitIntR {R : Type} (es : List (SE D Γ Λ)) (f : ∀ {lo hi : Int}, Expr D Γ Λ (.int lo hi) → List R) : List R :=
  es.flatMap fun p => match p with
    | ⟨.int _ _, a⟩ => f a
    | _ => []

theorem mem_mitIntR {R : Type} {es : List (SE D Γ Λ)} {f} {lo hi : Int} {a : Expr D Γ Λ (.int lo hi)} {x : R}
    (ha : (⟨.int lo hi, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitIntR es f := by
  unfold mitIntR
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

/-- The float-typed terms of a list. -/
def mitFlR {R : Type} (es : List (SE D Γ Λ)) (f : ∀ {lo hi : Int × Int}, Expr D Γ Λ (.fl lo hi) → List R) : List R :=
  es.flatMap fun p => match p with
    | ⟨.fl _ _, a⟩ => f a
    | _ => []

theorem mem_mitFlR {R : Type} {es : List (SE D Γ Λ)} {f} {lo hi : Int × Int} {a : Expr D Γ Λ (.fl lo hi)} {x : R}
    (ha : (⟨.fl lo hi, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitFlR es f := by
  unfold mitFlR
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

/-- Float pairs. -/
def mitFl2R {R : Type} (es : List (SE D Γ Λ))
    (f : ∀ {l1 h1 l2 h2 : Int × Int}, Expr D Γ Λ (.fl l1 h1) → Expr D Γ Λ (.fl l2 h2) → List R) : List R :=
  es.flatMap fun p => es.flatMap fun q => match p, q with
    | ⟨.fl _ _, a⟩, ⟨.fl _ _, b⟩ => f a b
    | _, _ => []

theorem mem_mitFl2R {R : Type} {es : List (SE D Γ Λ)} {f} {l1 h1 l2 h2 : Int × Int} {a : Expr D Γ Λ (.fl l1 h1)}
    {b : Expr D Γ Λ (.fl l2 h2)} {x : R}
    (ha : (⟨.fl l1 h1, a⟩ : SE D Γ Λ) ∈ es) (hb : (⟨.fl l2 h2, b⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a b) :
    x ∈ mitFl2R es f := by
  unfold mitFl2R
  rw [List.mem_flatMap]
  refine ⟨_, ha, ?_⟩
  rw [List.mem_flatMap]
  exact ⟨_, hb, hx⟩

/-- A term whose type is a pointer or a function pointer or an option or a sum or a reason... one matcher
    per index shape: the generic form is `ofTy` at a computed type; these four read the index off the term. -/
def mitPtrR {R : Type} (es : List (SE D Γ Λ)) (f : ∀ {n : Nat} {rw : Bool}, Expr D Γ Λ (.ptr n rw) → List R) :
    List R :=
  es.flatMap fun p => match p with
    | ⟨.ptr _ _, a⟩ => f a
    | _ => []

theorem mem_mitPtrR {R : Type} {es : List (SE D Γ Λ)} {f} {n : Nat} {rw : Bool} {a : Expr D Γ Λ (.ptr n rw)} {x : R}
    (ha : (⟨.ptr n rw, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitPtrR es f := by
  unfold mitPtrR
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

/-- A term of type `ptr n true` (a pointer with the right to write). -/
def mitPtrT {R : Type} (es : List (SE D Γ Λ)) (f : ∀ {n : Nat}, Expr D Γ Λ (.ptr n true) → List R) : List R :=
  es.flatMap fun p => match p with
    | ⟨.ptr _ true, a⟩ => f a
    | _ => []

theorem mem_mitPtrT {R : Type} {es : List (SE D Γ Λ)} {f} {n : Nat} {a : Expr D Γ Λ (.ptr n true)} {x : R}
    (ha : (⟨.ptr n true, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitPtrT es f := by
  unfold mitPtrT
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

def mitFnptrR {R : Type} (es : List (SE D Γ Λ)) (f : ∀ {n : Nat}, Expr D Γ Λ (.fnptr n) → List R) : List R :=
  es.flatMap fun p => match p with
    | ⟨.fnptr _, a⟩ => f a
    | _ => []

theorem mem_mitFnptrR {R : Type} {es : List (SE D Γ Λ)} {f} {n : Nat} {a : Expr D Γ Λ (.fnptr n)} {x : R}
    (ha : (⟨.fnptr n, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitFnptrR es f := by
  unfold mitFnptrR
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

def mitOptR {R : Type} (es : List (SE D Γ Λ)) (f : ∀ {n : Int}, Expr D Γ Λ (.opt n) → List R) : List R :=
  es.flatMap fun p => match p with
    | ⟨.opt _, a⟩ => f a
    | _ => []

theorem mem_mitOptR {R : Type} {es : List (SE D Γ Λ)} {f} {n : Int} {a : Expr D Γ Λ (.opt n)} {x : R}
    (ha : (⟨.opt n, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitOptR es f := by
  unfold mitOptR
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

def mitSumR {R : Type} (es : List (SE D Γ Λ))
    (f : ∀ {cs : List (Option (Int × Int))}, Expr D Γ Λ (.sum cs) → List R) : List R :=
  es.flatMap fun p => match p with
    | ⟨.sum _, a⟩ => f a
    | _ => []

theorem mem_mitSumR {R : Type} {es : List (SE D Γ Λ)} {f} {cs : List (Option (Int × Int))}
    {a : Expr D Γ Λ (.sum cs)} {x : R}
    (ha : (⟨.sum cs, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitSumR es f := by
  unfold mitSumR
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

def mitWhyR {R : Type} (es : List (SE D Γ Λ)) (f : ∀ {n : Nat}, Expr D Γ Λ (.why n) → List R) : List R :=
  es.flatMap fun p => match p with
    | ⟨.why _, a⟩ => f a
    | _ => []

theorem mem_mitWhyR {R : Type} {es : List (SE D Γ Λ)} {f} {n : Nat} {a : Expr D Γ Λ (.why n)} {x : R}
    (ha : (⟨.why n, a⟩ : SE D Γ Λ) ∈ es) (hx : x ∈ f a) : x ∈ mitWhyR es f := by
  unfold mitWhyR
  rw [List.mem_flatMap]
  exact ⟨_, ha, hx⟩

/-- The bounds of an integer type. -/
def tySchranken : Ty → Option (Int × Int)
  | .int lo hi => some (lo, hi)
  | _ => none

theorem tySchranken_eq {τ : Ty} {p : Int × Int} (h : tySchranken τ = some p) : τ = .int p.1 p.2 := by
  cases τ <;> simp [tySchranken] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- `τ = .int lo hi` read off a type that is not a variable (a field type, a register type). -/
def mitTypInt {R : Type} (τ : Ty) (f : ∀ {lo hi : Int}, τ = .int lo hi → List R) : List R :=
  (tySchranken τ).toList.attach.flatMap fun p => f (tySchranken_eq (by simpa using p.2))

theorem mem_mitTypInt {R : Type} {τ : Ty} {f} {lo hi : Int} {x : R} (h : τ = .int lo hi) (hx : x ∈ f h) :
    x ∈ mitTypInt τ f := by
  unfold mitTypInt
  rw [List.mem_flatMap]
  have hs : tySchranken τ = some (lo, hi) := by subst h; rfl
  exact ⟨⟨(lo, hi), by simp [hs]⟩, List.mem_attach _ _, hx⟩

/-- `o = some τ`, read off an optional type (a callee's result). -/
def mitSome {R : Type} (o : Option Ty) (f : ∀ {τ : Ty}, o = some τ → List R) : List R :=
  o.toList.attach.flatMap fun p => f (by simpa using p.2 : o = some p.1)

theorem mem_mitSome {R : Type} {o : Option Ty} {f} {τ : Ty} {x : R} (h : o = some τ) (hx : x ∈ f h) :
    x ∈ mitSome o f := by
  unfold mitSome
  rw [List.mem_flatMap]
  exact ⟨⟨τ, by simp [h]⟩, List.mem_attach _ _, hx⟩

/-! ## Arguments and results -/

/-- The argument lists of a parameter list. -/
def genArgs (es : List (SE D Γ Λ)) : (τs : List Ty) → List (Args D Γ Λ τs)
  | [] => [.nil]
  | τ :: τs => (ofTy es τ).flatMap fun e => (genArgs es τs).map fun r => .cons e r

theorem mem_genArgs {es : List (SE D Γ Λ)} {m : Nat}
    (hes : ∀ τ (e : Expr D Γ Λ τ), groesseExpr e ≤ m → (⟨τ, e⟩ : SE D Γ Λ) ∈ es) :
    ∀ (τs : List Ty) (a : Args D Γ Λ τs), groesseArgs a ≤ m + 1 → a ∈ genArgs es τs := by
  intro τs a
  induction a with
  | nil => intro _; simp [genArgs]
  | cons e rest ih =>
    intro h
    simp only [groesseArgs] at h
    simp only [genArgs, List.mem_flatMap, List.mem_map]
    exact ⟨e, mem_ofTy (hes _ e (by omega)), rest, ih (by omega), rfl⟩

/-- The result expressions of a result type. -/
def genErg (es : List (SE D Γ Λ)) : (o : Option Ty) → List (ErgExpr D Γ Λ o)
  | none => [.empty]
  | some τ => (ofTy es τ).map fun e => .val e

theorem mem_genErg {es : List (SE D Γ Λ)} {m : Nat}
    (hes : ∀ τ (e : Expr D Γ Λ τ), groesseExpr e ≤ m → (⟨τ, e⟩ : SE D Γ Λ) ∈ es) :
    ∀ (o : Option Ty) (a : ErgExpr D Γ Λ o), groesseErg a ≤ m + 1 → a ∈ genErg es o := by
  intro o a
  cases a with
  | empty => intro _; simp [genErg]
  | val e =>
    intro h
    simp only [groesseErg] at h
    simp only [genErg, List.mem_map]
    exact ⟨e, mem_ofTy (hes _ e (by omega)), rfl⟩

/-! ## Match arms -/

variable {V : Vertrag D}

/-- The arms of a tag type: the head block fixes the resources after the arms, the rest must end there too. -/
def genArms (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :
    (cs : List (Option (Int × Int))) → List (Σ Λ' : List (Res D), Arms D V l Γ Λ Λ' cs)
  | [] => [⟨Λ, .nil⟩]
  | c :: cs => (R.bl l (ArmCtx Γ c) Λ).flatMap fun p =>
      (ofTy (genArms R l Γ Λ cs) p.1).map fun r => ⟨p.1, .cons p.2 r⟩

theorem mem_genArms {R : Rek V} {m : Nat}
    (hbl : ∀ l Γ Λ Λ' (b : Block D V l Γ Λ Λ'), groesseBlock b ≤ m → (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ R.bl l Γ Λ) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {cs : List (Option (Int × Int))} {Λ' : List (Res D)}
      (a : Arms D V l Γ Λ Λ' cs),
      groesseArms a ≤ m + 1 → (⟨Λ', a⟩ : Σ Λ' : List (Res D), Arms D V l Γ Λ Λ' cs) ∈ genArms R l Γ Λ cs
  | _, _, _, _, _, .nil, _ => by simp [genArms]
  | _, _, _, _, _, .cons b rest, h => by
    simp only [groesseArms] at h
    simp only [genArms, List.mem_flatMap, List.mem_map]
    exact ⟨⟨_, b⟩, hbl _ _ _ _ b (by omega), _, mem_ofTy (mem_genArms hbl rest (by omega)), rfl⟩

/-- The arms of a reason type. -/
def genGrundArms (R : Rek V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :
    (n : Nat) → List (Σ Λ' : List (Res D), GrundArms D V l Γ Λ Λ' n)
  | 0 => [⟨Λ, .nil⟩]
  | n + 1 => (R.bl l Γ Λ).flatMap fun p =>
      (ofTy (genGrundArms R l Γ Λ n) p.1).map fun r => ⟨p.1, .cons p.2 r⟩

theorem mem_genGrundArms {R : Rek V} {m : Nat}
    (hbl : ∀ l Γ Λ Λ' (b : Block D V l Γ Λ Λ'), groesseBlock b ≤ m → (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ R.bl l Γ Λ) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {Λ' : List (Res D)} (a : GrundArms D V l Γ Λ Λ' n),
      groesseGrundArms a ≤ m + 1 →
        (⟨Λ', a⟩ : Σ Λ' : List (Res D), GrundArms D V l Γ Λ Λ' n) ∈ genGrundArms R l Γ Λ n
  | _, _, _, _, _, .nil, _ => by simp [genGrundArms]
  | _, _, _, _, _, .cons b rest, h => by
    simp only [groesseGrundArms] at h
    simp only [genGrundArms, List.mem_flatMap, List.mem_map]
    exact ⟨⟨_, b⟩, hbl _ _ _ _ b (by omega), _, mem_ofTy (mem_genGrundArms hbl rest (by omega)), rfl⟩

end Gabbro.Grammatik.Gen
