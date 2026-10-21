/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Teile.lean
  Subject:   REPRESENTATIVES IN THE STREAMS. The statements of the tables one per key are built from representatives:
             `ERU E k` says every expression of size below `k` has one in `E` (same type, same carriers read, not
             larger, in the bucket of its own size), `SRU`, `BRU`, `NRU` the same for the statements, blocks and end
             blocks of the context at hand, `ORU` for the oracle of the other contexts (in every bound that reaches the
             representative's size). From these, argument lists, results and arms have representatives in their
             streams (`argsS_rep`, `ergS_rep`, `armsS_rep`, `grundArmsS_rep`).
-/
import Grammatik.Gen.Erzeuger.Kompakt.Gleich
import Grammatik.Gen.Erzeuger.Hilfen

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Every expression of size below `k` has a representative in `E`. -/
def ERU (E : Sz (SE D Γ Λ)) (k : Nat) : Prop :=
  ∀ (τ : Ty) (e : Expr D Γ Λ τ), groesseExpr e < k →
    ∃ e' : Expr D Γ Λ τ, (⟨τ, e'⟩ : SE D Γ Λ) ∈ E (groesseExpr e') ∧ GlE e' e

/-- Every statement of the context at hand of size below `k` has a representative in `Ss`. -/
def SRU (Ss : Sz (SS D V l Γ Λ)) (k : Nat) : Prop :=
  ∀ (Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'), groesseStmt s < k →
    ∃ s' : Stmt D V l Γ Λ Λ', (⟨Λ', s'⟩ : SS D V l Γ Λ) ∈ Ss (groesseStmt s') ∧ GlS s' s

/-- Every block of the context at hand of size below `k` has a representative in `Bs`. -/
def BRU (Bs : Sz (SB D V l Γ Λ)) (k : Nat) : Prop :=
  ∀ (Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'), groesseBlock b < k →
    ∃ b' : Block D V l Γ Λ Λ', (⟨Λ', b'⟩ : SB D V l Γ Λ) ∈ Bs (groesseBlock b') ∧ GlB b' b

/-- Every end block of the context at hand of size below `k` has a representative in `Ns`. -/
def NRU (Ns : Sz (Endblock D V l Γ Λ)) (k : Nat) : Prop :=
  ∀ (e : Endblock D V l Γ Λ), groesseEnd e < k → ∃ e' : Endblock D V l Γ Λ, e' ∈ Ns (groesseEnd e') ∧ GlN e' e

/-- The oracle holds a representative of every term of size below `k`, in every bound that reaches its size. -/
structure ORU (O : Orakel V) (k : Nat) : Prop where
  ex : ∀ (Γ' : Ctx) (Λ' : List (Res D)) (τ : Ty) (e : Expr D Γ' Λ' τ), groesseExpr e < k →
    ∃ e' : Expr D Γ' Λ' τ, (∀ m, groesseExpr e' ≤ m → (⟨τ, e'⟩ : SE D Γ' Λ') ∈ O.ex Γ' Λ' m (groesseExpr e')) ∧
      GlE e' e
  bl : ∀ (l' : Bool) (Γ' : Ctx) (Λ' Λ'' : List (Res D)) (b : Block D V l' Γ' Λ' Λ''), groesseBlock b < k →
    ∃ b' : Block D V l' Γ' Λ' Λ'', (∀ m, groesseBlock b' ≤ m →
      (⟨Λ'', b'⟩ : SB D V l' Γ' Λ') ∈ O.bl l' Γ' Λ' m (groesseBlock b')) ∧ GlB b' b
  en : ∀ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (e : Endblock D V l' Γ' Λ'), groesseEnd e < k →
    ∃ e' : Endblock D V l' Γ' Λ', (∀ m, groesseEnd e' ≤ m → e' ∈ O.en l' Γ' Λ' m (groesseEnd e')) ∧ GlN e' e

theorem ERU.mono {E : Sz (SE D Γ Λ)} {k k' : Nat} (h : ERU E k) (hk : k' ≤ k) : ERU E k' :=
  fun τ e he => h τ e (by omega)

/-- **Closing a stands-for goal**: unfold every summary and size of both sides, rewrite with the parts' facts. -/
macro "glfertig" : tactic =>
  `(tactic| (constructor <;> (intros; simp_all [mS, mB, mE, mArms, mGArms, Stmt.gOk, Block.gOk, Endblock.gOk,
    Arms.gOk, GrundArms.gOk, Stmt.ants, Block.ants, Endblock.ants, Arms.ants, GrundArms.ants, Stmt.regs, Block.regs,
    Endblock.regs, Arms.regs, GrundArms.regs, koerperS, koerperB, koerperE, koerperArms, koerperGArms, groesseStmt,
    groesseBlock, groesseEnd, groesseArms, groesseGrundArms, groesseArgs, groesseErg, Args.orte, ErgExpr.orte]) <;>
    omega))

theorem argsS_rep {E : Sz (SE D Γ Λ)} {K : Nat} (hE : ERU E K) :
    ∀ (τs : List Ty) (a : Args D Γ Λ τs), groesseArgs a ≤ K →
      ∃ a' : Args D Γ Λ τs, a' ∈ argsS E τs (groesseArgs a') ∧ GlArgs a' a := by
  intro τs a
  induction a with
  | nil => intro _; exact ⟨.nil, Sz.mem_blatt (by simp), ⟨fun _ => Iff.rfl, Nat.le_refl _⟩⟩
  | cons e rest ih =>
    intro h
    simp only [groesseArgs] at h
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    obtain ⟨r', hr, ⟨_, _⟩⟩ := ih (by omega)
    refine ⟨.cons e' r', ?_, ?_⟩
    · simp only [groesseArgs]
      exact Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_tyS he) (Sz.mem_bind hr (Sz.mem_pure _)))) (by omega)
    · glfertig

theorem ergS_rep {E : Sz (SE D Γ Λ)} {K : Nat} (hE : ERU E K) {o : Option Ty} (a : ErgExpr D Γ Λ o)
    (h : groesseErg a ≤ K) : ∃ a' : ErgExpr D Γ Λ o, a' ∈ ergS E o (groesseErg a') ∧ GlErg a' a := by
  cases a with
  | empty => exact ⟨.empty, Sz.mem_blatt (by simp), ⟨fun _ => Iff.rfl, Nat.le_refl _⟩⟩
  | val e =>
    simp only [groesseErg] at h
    obtain ⟨e', he, ⟨_, _⟩⟩ := hE _ e (by omega)
    refine ⟨.val e', ?_, ?_⟩
    · have hm : ErgExpr.val e' ∈ ergS E (some _) (groesseExpr e' + 1) :=
        Sz.mem_knoten (Sz.mem_map (f := ErgExpr.val) (mem_tyS he))
      simp only [groesseErg]
      exact Sz.mem_cast hm (by omega)
    · glfertig

theorem armsS_rep {O : Orakel V} {K : Nat} (hO : ORU O K) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {cs : List (Option (Int × Int))} {Λ' : List (Res D)}
      (a : Arms D V l Γ Λ Λ' cs), groesseArms a ≤ K →
      ∃ a' : Arms D V l Γ Λ Λ' cs,
        (⟨Λ', a'⟩ : Σ Λ' : List (Res D), Arms D V l Γ Λ Λ' cs) ∈ armsS O l Γ Λ cs (groesseArms a') ∧ GlArms a' a
  | _, _, _, _, .nil, _ => ⟨.nil, Sz.mem_blatt (by simp), GlArms.mk (fun _ => rfl) (fun _ _ => rfl)
      (fun _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl) (Nat.le_refl _)⟩
  | Γ, Λ, _, _, .cons b rest, h => by
    simp only [groesseArms] at h
    obtain ⟨b', hbm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ b (by omega)
    obtain ⟨r', hr, ⟨_, _, _, _, _, _⟩⟩ := armsS_rep hO rest (by omega)
    refine ⟨.cons b' r', ?_, ?_⟩
    · have hb' := hbm (groesseBlock b' + groesseArms r') (by omega)
      have hm := Sz.mem_bindR (A := Sz.pure ()) (i := 0) (Sz.mem_pure ()) hb'
        (F := fun _ p => Sz.bind (fun j => ofTy (armsS O l Γ Λ _ j) p.1) fun r => Sz.pure ⟨p.1, .cons p.2 r⟩)
        (y := (⟨_, .cons b' r'⟩ : Σ Λ' : List (Res D), Arms D V l Γ Λ Λ' _))
        (j' := groesseArms r')
        (Sz.mem_cast (Sz.mem_bind (mem_ofTy hr) (Sz.mem_pure _)) (by omega))
      simp only [groesseArms]
      exact Sz.mem_cast (Sz.mem_knoten hm) (by omega)
    · glfertig

theorem grundArmsS_rep {O : Orakel V} {K : Nat} (hO : ORU O K) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {Λ' : List (Res D)}
      (a : GrundArms D V l Γ Λ Λ' n), groesseGrundArms a ≤ K →
      ∃ a' : GrundArms D V l Γ Λ Λ' n,
        (⟨Λ', a'⟩ : Σ Λ' : List (Res D), GrundArms D V l Γ Λ Λ' n) ∈ grundArmsS O l Γ Λ n (groesseGrundArms a') ∧
          GlGArms a' a
  | _, _, _, _, .nil, _ => ⟨.nil, Sz.mem_blatt (by simp), GlGArms.mk (fun _ => rfl) (fun _ _ => rfl)
      (fun _ => Iff.rfl) (fun _ => Iff.rfl) (fun _ => Iff.rfl) (Nat.le_refl _)⟩
  | Γ, Λ, _, _, .cons b rest, h => by
    simp only [groesseGrundArms] at h
    obtain ⟨b', hbm, ⟨_, _, _, _, _, _⟩⟩ := hO.bl _ _ _ _ b (by omega)
    obtain ⟨r', hr, ⟨_, _, _, _, _, _⟩⟩ := grundArmsS_rep hO rest (by omega)
    refine ⟨.cons b' r', ?_, ?_⟩
    · have hb' := hbm (groesseBlock b' + groesseGrundArms r') (by omega)
      have hm := Sz.mem_bindR (A := Sz.pure ()) (i := 0) (Sz.mem_pure ()) hb'
        (F := fun _ p => Sz.bind (fun j => ofTy (grundArmsS O l Γ Λ _ j) p.1) fun r => Sz.pure ⟨p.1, .cons p.2 r⟩)
        (y := (⟨_, .cons b' r'⟩ : Σ Λ' : List (Res D), GrundArms D V l Γ Λ Λ' _))
        (j' := groesseGrundArms r')
        (Sz.mem_cast (Sz.mem_bind (mem_ofTy hr) (Sz.mem_pure _)) (by omega))
      simp only [groesseGrundArms]
      exact Sz.mem_cast (Sz.mem_knoten hm) (by omega)
    · glfertig

end Gabbro.Grammatik.Gen
