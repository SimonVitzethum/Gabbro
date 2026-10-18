/-
  File:      Grammatik/Gen/Erzeuger/Hilfen.lean
  Subject:   What the statement, block and end-block clauses share: the ORACLE (`Orakel`: the expressions, blocks and
             end blocks of OTHER contexts, up to a bound), the statements / blocks of the context at hand, the
             matchers on an optional type, the generators of argument lists, result expressions and match arms,
             each with its completeness lemma.
-/
import Grammatik.Gen.Erzeuger.AusdruckVollst
import Grammatik.Gen.Erzeuger.Entscheidung

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen]

/-- A statement with the resources held after it. -/
abbrev SS (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : Type :=
  Σ Λ' : List (Res D), Stmt D V l Γ Λ Λ'

/-- A block with the resources held after it. -/
abbrev SB (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : Type :=
  Σ Λ' : List (Res D), Block D V l Γ Λ Λ'

/-- **The oracle**: the expressions, blocks and end blocks of every OTHER context, by exact size, valid for the sizes
    up to the bound it is given. (The statements are always those of the context at hand.) -/
structure Orakel (V : Vertrag D) where
  ex : ∀ (Γ : Ctx) (Λ : List (Res D)), Nat → Sz (SE D Γ Λ)
  bl : ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)), Nat → Sz (SB D V l Γ Λ)
  en : ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)), Nat → Sz (Endblock D V l Γ Λ)

/-- The oracle holds every term of size below `K`, in the bucket of its size, for every bound that reaches it. -/
structure OUnter {V : Vertrag D} (O : Orakel V) (K : Nat) : Prop where
  ex : ∀ (m : Nat) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) (e : Expr D Γ Λ τ), groesseExpr e < K → groesseExpr e ≤ m →
    (⟨τ, e⟩ : SE D Γ Λ) ∈ O.ex Γ Λ m (groesseExpr e)
  bl : ∀ (m : Nat) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'), groesseBlock b < K →
    groesseBlock b ≤ m → (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ O.bl l Γ Λ m (groesseBlock b)
  en : ∀ (m : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Endblock D V l Γ Λ), groesseEnd e < K →
    groesseEnd e ≤ m → e ∈ O.en l Γ Λ m (groesseEnd e)

/-! ## Matchers on an optional or integer type -/

/-- The bounds of an integer type. -/
def tySchranken : Ty → Option (Int × Int)
  | .int lo hi => some (lo, hi)
  | _ => none

theorem tySchranken_eq {τ : Ty} {p : Int × Int} (h : tySchranken τ = some p) : τ = .int p.1 p.2 := by
  cases τ <;> simp [tySchranken] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- `τ = .int lo hi` read off a type that is not a variable (a field type, a register type). -/
def mitTypInt {R : Type} (τ : Ty) (f : ∀ {lo hi : Int}, τ = .int lo hi → Sz R) : Sz R := fun k =>
  (tySchranken τ).toList.attach.flatMap fun p => f (tySchranken_eq (by simpa using p.2)) k

theorem mem_mitTypInt {R : Type} {τ : Ty} {f : ∀ {lo hi : Int}, τ = .int lo hi → Sz R} {lo hi : Int} {x : R}
    {k : Nat} (h : τ = .int lo hi) (hx : x ∈ f h k) : x ∈ mitTypInt τ f k := by
  unfold mitTypInt
  rw [List.mem_flatMap]
  have hs : tySchranken τ = some (lo, hi) := by subst h; rfl
  exact ⟨⟨(lo, hi), by simp [hs]⟩, List.mem_attach _ _, hx⟩

/-- `o = some τ`, read off an optional type (a callee's result). -/
def mitSome {R : Type} (o : Option Ty) (f : ∀ {τ : Ty}, o = some τ → Sz R) : Sz R := fun k =>
  o.toList.attach.flatMap fun p => f (by simpa using p.2 : o = some p.1) k

theorem mem_mitSome {R : Type} {o : Option Ty} {f : ∀ {τ : Ty}, o = some τ → Sz R} {τ : Ty} {x : R} {k : Nat}
    (h : o = some τ) (hx : x ∈ f h k) : x ∈ mitSome o f k := by
  unfold mitSome
  rw [List.mem_flatMap]
  exact ⟨⟨τ, by simp [h]⟩, List.mem_attach _ _, hx⟩

/-! ## The pointer-with-write-right view -/

/-- The expressions of type `ptr n true`. -/
def ptrTS {Γ : Ctx} {Λ : List (Res D)} (E : Sz (SE D Γ Λ)) : Sz (Σ n : Nat, Expr D Γ Λ (.ptr n true)) := fun i =>
  (E i).filterMap fun p => match p with
    | ⟨.ptr n true, a⟩ => some ⟨n, a⟩
    | _ => none

theorem mem_ptrTS {Γ : Ctx} {Λ : List (Res D)} {E : Sz (SE D Γ Λ)} {i : Nat} {n : Nat}
    {a : Expr D Γ Λ (.ptr n true)} (h : (⟨.ptr n true, a⟩ : SE D Γ Λ) ∈ E i) :
    (⟨n, a⟩ : Σ n : Nat, Expr D Γ Λ (.ptr n true)) ∈ ptrTS E i :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-! ## Arguments and results -/

variable {Γ : Ctx} {Λ : List (Res D)}

/-- The argument lists of a parameter list. -/
def argsS (E : Sz (SE D Γ Λ)) : (τs : List Ty) → Sz (Args D Γ Λ τs)
  | [] => Sz.blatt [.nil]
  | τ :: τs => Sz.knoten (Sz.bind (tyS E τ) fun e => Sz.bind (argsS E τs) fun r => Sz.pure (.cons e r))

theorem mem_argsS {E : Sz (SE D Γ Λ)} {K : Nat} (hE : Unter E K) :
    ∀ (τs : List Ty) (a : Args D Γ Λ τs), groesseArgs a ≤ K → a ∈ argsS E τs (groesseArgs a) := by
  intro τs a
  induction a with
  | nil => intro _; exact Sz.mem_blatt (by simp)
  | cons e rest ih =>
    intro h
    simp only [groesseArgs] at h ⊢
    have he := hE _ e (by omega)
    exact Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_tyS he) (Sz.mem_bind (ih (by omega)) (Sz.mem_pure _))))
      (by omega)

/-- The result expressions of a result type. -/
def ergS (E : Sz (SE D Γ Λ)) : (o : Option Ty) → Sz (ErgExpr D Γ Λ o)
  | none => Sz.blatt [.empty]
  | some τ => Sz.knoten (Sz.map ErgExpr.val (tyS E τ))

theorem mem_ergS {E : Sz (SE D Γ Λ)} {K : Nat} (hE : Unter E K) {o : Option Ty} (a : ErgExpr D Γ Λ o)
    (h : groesseErg a ≤ K) : a ∈ ergS E o (groesseErg a) := by
  cases a with
  | empty => exact Sz.mem_blatt (by simp)
  | val e =>
    simp only [groesseErg] at h ⊢
    have he := hE _ e (by omega)
    have hm : ErgExpr.val e ∈ ergS E (some _) (groesseExpr e + 1) :=
      Sz.mem_knoten (Sz.mem_map (f := ErgExpr.val) (mem_tyS he))
    exact Sz.mem_cast hm (by omega)

/-! ## Match arms -/

variable {V : Vertrag D}

/-- The arms of a tag type: the head block fixes the resources after the arms, the rest must end there too. -/
def armsS (O : Orakel V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :
    (cs : List (Option (Int × Int))) → Sz (Σ Λ' : List (Res D), Arms D V l Γ Λ Λ' cs)
  | [] => Sz.blatt [⟨Λ, .nil⟩]
  | c :: cs => Sz.knoten (Sz.bindR (Sz.pure ()) (fun m => O.bl l (ArmCtx Γ c) Λ m) fun _ p =>
      Sz.bind (fun j => ofTy (armsS O l Γ Λ cs j) p.1) fun r => Sz.pure ⟨p.1, .cons p.2 r⟩)

theorem mem_armsS {O : Orakel V} {K : Nat} (hO : OUnter O K) {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {cs : List (Option (Int × Int))} {Λ' : List (Res D)}
      (a : Arms D V l Γ Λ Λ' cs), groesseArms a ≤ K →
      (⟨Λ', a⟩ : Σ Λ' : List (Res D), Arms D V l Γ Λ Λ' cs) ∈ armsS O l Γ Λ cs (groesseArms a)
  | _, _, _, _, .nil, _ => Sz.mem_blatt (by simp)
  | Γ, Λ, _, _, .cons b rest, h => by
    simp only [groesseArms] at h ⊢
    have hb := hO.bl _ _ _ _ _ b (by omega) (Nat.le_refl _)
    have hb' := hO.bl (groesseBlock b + groesseArms rest) _ _ _ _ b (by omega) (by omega)
    have hr := mem_armsS hO rest (by omega)
    have hm := Sz.mem_bindR (A := Sz.pure ()) (i := 0) (Sz.mem_pure ()) hb'
      (F := fun _ p => Sz.bind (fun j => ofTy (armsS O l Γ Λ _ j) p.1) fun r => Sz.pure ⟨p.1, .cons p.2 r⟩)
      (y := (⟨_, .cons b rest⟩ : Σ Λ' : List (Res D), Arms D V l Γ Λ Λ' _))
      (j' := groesseArms rest)
      (Sz.mem_cast (Sz.mem_bind (mem_ofTy hr) (Sz.mem_pure _)) (by omega))
    exact Sz.mem_cast (Sz.mem_knoten hm) (by omega)

/-- The arms of a reason type. -/
def grundArmsS (O : Orakel V) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :
    (n : Nat) → Sz (Σ Λ' : List (Res D), GrundArms D V l Γ Λ Λ' n)
  | 0 => Sz.blatt [⟨Λ, .nil⟩]
  | n + 1 => Sz.knoten (Sz.bindR (Sz.pure ()) (fun m => O.bl l Γ Λ m) fun _ p =>
      Sz.bind (fun j => ofTy (grundArmsS O l Γ Λ n j) p.1) fun r => Sz.pure ⟨p.1, .cons p.2 r⟩)

theorem mem_grundArmsS {O : Orakel V} {K : Nat} (hO : OUnter O K) {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {Λ' : List (Res D)}
      (a : GrundArms D V l Γ Λ Λ' n), groesseGrundArms a ≤ K →
      (⟨Λ', a⟩ : Σ Λ' : List (Res D), GrundArms D V l Γ Λ Λ' n) ∈ grundArmsS O l Γ Λ n (groesseGrundArms a)
  | _, _, _, _, .nil, _ => Sz.mem_blatt (by simp)
  | Γ, Λ, _, _, .cons b rest, h => by
    simp only [groesseGrundArms] at h ⊢
    have hb' := hO.bl (groesseBlock b + groesseGrundArms rest) _ _ _ _ b (by omega) (by omega)
    have hr := mem_grundArmsS hO rest (by omega)
    have hm := Sz.mem_bindR (A := Sz.pure ()) (i := 0) (Sz.mem_pure ()) hb'
      (F := fun _ p => Sz.bind (fun j => ofTy (grundArmsS O l Γ Λ _ j) p.1) fun r => Sz.pure ⟨p.1, .cons p.2 r⟩)
      (y := (⟨_, .cons b rest⟩ : Σ Λ' : List (Res D), GrundArms D V l Γ Λ Λ' _))
      (j' := groesseGrundArms rest)
      (Sz.mem_cast (Sz.mem_bind (mem_ofTy hr) (Sz.mem_pure _)) (by omega))
    exact Sz.mem_cast (Sz.mem_knoten hm) (by omega)

end Gabbro.Grammatik.Gen
