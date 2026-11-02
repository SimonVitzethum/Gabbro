module
public import Grammatik.Zielsatz.Einbettung.Syntax
@[expose] public section


/-!
  File:      Grammatik/Zielsatz/Einbettung/Welt.lean
  Subject:   Values, memories and environments under an embedding (stage E1).

  A value of `D` stands beside a value of `D'` (`VRel`): equal through the embedding, except at a
  function pointer, where a HEAD of its signature (`Rueck.rep`, stage E4) stands beside every
  function of `D'` outside the image that conforms to the signature. Every value of `D'` goes
  back to one of `D` beside it (`valZ`). A memory of
  `D'` restricts to `D` (`speicherZ`); a memory of `D` embeds into `D'` around a fixed CONTEXT
  for everything outside the image (`speicherE`). Restricting an embedding gives the memory back
  (`speicherZ_speicherE`), and outside the image the embedding is the context (`slotE_fremd`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

mutual
/-- A type whose complete value contains no function-pointer leaf. -/
def _root_.Gabbro.Grammatik.Ty.zeigerfrei : Ty → Bool
  | .fnptr _ => false
  | .arr τ _ => τ.zeigerfrei
  | .sum cs => Ty.casesZeigerfrei cs
  | _ => true

/-- Sum traversal for the same pointer-free predicate, without a depth bound. -/
def _root_.Gabbro.Grammatik.Ty.casesZeigerfrei : List (Option Ty) → Bool
  | [] => true
  | none :: cs => Ty.casesZeigerfrei cs
  | some τ :: cs => τ.zeigerfrei && Ty.casesZeigerfrei cs
end

@[simp] theorem _root_.Gabbro.Grammatik.Ty.casesZeigerfrei_eq_all (cs : List (Option Ty)) :
    Ty.casesZeigerfrei cs = cs.all (fun | none => true | some τ => τ.zeigerfrei) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [Ty.casesZeigerfrei, List.all_cons, ih, Bool.true_and]

/-- A value transported along a type equation. -/
def castW {τ σ : Ty} (h : τ = σ) (v : Wert D τ) : Wert D σ := h ▸ v

theorem castW_castW {τ σ ρ : Ty} (h : τ = σ) (h' : σ = ρ) (v : Wert D τ) :
    castW h' (castW h v) = castW (h.trans h') v := by subst h; subst h'; rfl

theorem castW_self {τ : Ty} (h : τ = τ) (v : Wert D τ) : castW h v = v := by rfl

/-- A result value transported along an equation of its type. -/
def castV {e e' : Option Ty} (h : e = e') (v : ErgVal D e) : ErgVal D e' := h ▸ v

theorem castW_symm {τ σ : Ty} (h : τ = σ) (x : Wert D σ) : castW h (castW h.symm x) = x := by
  subst h; rfl

/-- An environment transported along an equation of its scope. -/
def castE {Γ Γ' : Ctx} (h : Γ = Γ') (ρ : Env D Γ) : Env D Γ' := h ▸ ρ

/-- An outcome transported along an equation of its scope. -/
def castAus {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} (h : Γ = Γ') (o : Ausgang V l Γ) :
    Ausgang V l Γ' := h ▸ o

/-- An end outcome transported along an equation of its scope. -/
def castEnd {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} (h : Γ = Γ') (o : EndAusgang V l Γ) :
    EndAusgang V l Γ' := h ▸ o

namespace Einbettung

/-- **What `D` reads as a value from the hardware or the environment holds no function pointer**:
    the carriers of a register, an atomic global, an axiom's arguments and result, a register's
    type. Two foreign functions are one head in `D`; an answer that depended on which one `D`
    could not repeat (stage E4). A condition on `D` alone. -/
structure AntwortFrei (D : Deklaration) : Prop where
  regFrei : ∀ r t, Sum.inl t ∈ D.rtraeger r → ∀ f, (D.typ t f).zeigerfrei = true
  regFreiG : ∀ r g, Sum.inr g ∈ D.rtraeger r → (D.gtyp g).zeigerfrei = true
  atomFrei : ∀ g, D.atomar g = true → (D.gtyp g).zeigerfrei = true
  aergFrei : ∀ a τ, D.aerg a = some τ → τ.zeigerfrei = true
  aparamsFrei : ∀ a τ, τ ∈ D.aparams a → τ.zeigerfrei = true
  rtypFrei : ∀ r, (D.rtyp r).zeigerfrei = true

variable (E : Einbettung D D')

/-- **How `D` names a function of `D'`**: an image function by its preimage, a function outside
    the image that conforms to the image of signature `n` by the HEAD `rep n` -- a function of `D`
    that conforms to `n` and whose contract is the pointer's contract (callbacks, stage E4); and
    what `D` reads from outside holds no function pointer (`AntwortFrei`). -/
structure Rueck : Type where
  rep : Nat → Option D.Fn
  rep_passt : ∀ n g, rep n = some g → D.passt g n = true
  voll : ∀ n (f' : D'.Fn), D'.passt f' (E.num n) = true → E.fnZ f' = none → (rep n).isSome = true
  frei : AntwortFrei D

variable {E} in
/-- A function of `D'` conforming to the image of `n`, named in `D`. -/
def Rueck.zeiger (K : E.Rueck) (n : Nat) (f' : D'.Fn) (h' : D'.passt f' (E.num n) = true) :
    {g : D.Fn // D.passt g n = true} :=
  match hz : E.fnZ f' with
  | some g => ⟨g, by rw [← E.passt g n, E.fn_fnZ f' g hz]; exact h'⟩
  | none =>
      match hr : K.rep n with
      | some g => ⟨g, K.rep_passt n g hr⟩
      | none => absurd (K.voll n f' h' hz) (by rw [hr]; simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true])

variable (K : E.Rueck)

/-- **A value of `D'` back in `D`**: a function pointer to its name in `D`, everything else as is. -/
def valZ : (τ : Ty) → Wert D' (E.tyE τ) → Wert D τ :=
  Val.restrict E.num E.tnum (fun n v => K.zeiger n v.1 v.2)

/-- Restricting an embedded value returns its complete source, including payloads. -/
theorem valZ_valE (τ : Ty) (v : Wert D τ) : E.valZ K τ (E.valE τ v) = v :=
  Val.restrict_relocate E.num E.tnum _ _ (fun n value => by
    obtain ⟨f, h⟩ := value
    simp only [Rueck.zeiger, E.fnZ_fn]) τ v
