import Grammatik.Zielsatz.Einbettung.Syntax

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

/-- A type that is not a function pointer: its values name no function. -/
def _root_.Gabbro.Grammatik.Ty.zeigerfrei : Ty → Bool
  | .fnptr _ => false
  | _ => true

/-- A value transported along a type equation. -/
def castW {τ σ : Ty} (h : τ = σ) (v : Wert D τ) : Wert D σ := h ▸ v

theorem castW_castW {τ σ ρ : Ty} (h : τ = σ) (h' : σ = ρ) (v : Wert D τ) :
    castW h' (castW h v) = castW (h.trans h') v := by subst h; subst h'; rfl

theorem castW_self {τ : Ty} (h : τ = τ) (v : Wert D τ) : castW h v = v := rfl

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

variable (E : Einbettung D D')

/-- **How `D` names a function of `D'`**: an image function by its preimage, a function outside
    the image that conforms to the image of signature `n` by the HEAD `rep n` -- a function of `D`
    that conforms to `n` and whose contract is the pointer's contract (callbacks, stage E4). The
    carriers a register or a visibility answer reads hold no function pointer, and no register,
    axiom argument or axiom result is one (two different foreign functions are one head in `D`;
    an answer that depends on which one `D` cannot repeat). -/
structure Rueck : Type where
  rep : Nat → Option D.Fn
  rep_passt : ∀ n g, rep n = some g → D.passt g n = true
  voll : ∀ n (f' : D'.Fn), D'.passt f' (E.num n) = true → E.fnZ f' = none → (rep n).isSome = true
  regFrei : ∀ r t, Sum.inl t ∈ D.rtraeger r → ∀ f, (D.typ t f).zeigerfrei = true
  regFreiG : ∀ r g, Sum.inr g ∈ D.rtraeger r → (D.gtyp g).zeigerfrei = true
  atomFrei : ∀ g, D.atomar g = true → (D.gtyp g).zeigerfrei = true
  aergFrei : ∀ a τ, D.aerg a = some τ → τ.zeigerfrei = true
  aparamsFrei : ∀ a τ, τ ∈ D.aparams a → τ.zeigerfrei = true
  rtypFrei : ∀ r, (D.rtyp r).zeigerfrei = true

variable {E} in
/-- A function of `D'` conforming to the image of `n`, named in `D`. -/
def Rueck.zeiger (K : E.Rueck) (n : Nat) (f' : D'.Fn) (h' : D'.passt f' (E.num n) = true) :
    {g : D.Fn // D.passt g n = true} :=
  match hz : E.fnZ f' with
  | some g => ⟨g, by rw [← E.passt g n, E.fn_fnZ f' g hz]; exact h'⟩
  | none =>
      match hr : K.rep n with
      | some g => ⟨g, K.rep_passt n g hr⟩
      | none => absurd (K.voll n f' h' hz) (by rw [hr]; simp)

variable (K : E.Rueck)

/-- **A value of `D'` back in `D`**: a function pointer to its name in `D`, everything else as is. -/
def valZ : (τ : Ty) → Wert D' (E.tyE τ) → Wert D τ
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum _, v => v
  | .why _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr n, v => K.zeiger n v.1 v.2
  | .ptr _ _, v => v
  | .ref _, v => v

/-- **A value of `D` beside a value of `D'`**: equal through the embedding, except that a head of
    `D` stands beside every function outside the image of its signature. -/
def VRel : (τ : Ty) → Wert D τ → Wert D' (E.tyE τ) → Prop
  | .fnptr n, v, v' => v'.1 = E.fn v.1 ∨ (E.fnZ v'.1 = none ∧ K.rep n = some v.1)
  | τ, v, v' => v' = E.valE τ v

theorem vrel_valE : ∀ (τ : Ty) (v : Wert D τ), E.VRel K τ v (E.valE τ v)
  | .int _ _, _ => rfl
  | .bool, _ => rfl
  | .opt _, _ => rfl
  | .sum _, _ => rfl
  | .why _, _ => rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr _, _ => Or.inl rfl
  | .ptr _ _, _ => rfl
  | .ref _, _ => rfl

theorem vrel_valZ : ∀ (τ : Ty) (v' : Wert D' (E.tyE τ)), E.VRel K τ (E.valZ K τ v') v'
  | .int _ _, _ => rfl
  | .bool, _ => rfl
  | .opt _, _ => rfl
  | .sum _, _ => rfl
  | .why _, _ => rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr n, ⟨f', h'⟩ => by
      show f' = E.fn (K.zeiger n f' h').1 ∨ (E.fnZ f' = none ∧ K.rep n = some (K.zeiger n f' h').1)
      unfold Rueck.zeiger
      split
      · rename_i g hz; exact Or.inl (E.fn_fnZ f' g hz).symm
      · rename_i hz
        split
        · rename_i g hr; exact Or.inr ⟨hz, hr⟩
        · rename_i hr; exact absurd (K.voll n f' h' hz) (by rw [hr]; simp)
  | .ptr _ _, _ => rfl
  | .ref _, _ => rfl

theorem valZ_vrel : ∀ (τ : Ty) {v : Wert D τ} {v' : Wert D' (E.tyE τ)}, E.VRel K τ v v' →
    E.valZ K τ v' = v
  | .int _ _, _, _, h => by subst h; rfl
  | .bool, _, _, h => by subst h; rfl
  | .opt _, _, _, h => by subst h; rfl
  | .sum _, _, _, h => by subst h; rfl
  | .why _, _, _, h => by subst h; rfl
  | .never, _, _, h => by subst h; rfl
  | .fl _ _, _, _, h => by subst h; rfl
  | .fnptr n, ⟨g, hg⟩, ⟨f', h'⟩, h => by
      show K.zeiger n f' h' = ⟨g, hg⟩
      unfold Rueck.zeiger
      rcases h with h | ⟨hz, hr⟩
      · simp only at h
        subst h
        split
        · rename_i g0 hz
          rw [E.fnZ_fn] at hz
          cases hz; rfl
        · rename_i hz; rw [E.fnZ_fn] at hz; cases hz
      · split
        · rename_i g0 hz'; simp only at hz; rw [hz] at hz'; cases hz'
        · split
          · rename_i g0 hr'; simp only at hr; rw [hr] at hr'; cases hr'; rfl
          · rename_i hr'; simp only at hr; rw [hr] at hr'; cases hr'
  | .ptr _ _, _, _, h => by subst h; rfl
  | .ref _, _, _, h => by subst h; rfl

/-- Pointer-free values are related exactly when they are equal through the embedding. -/
theorem vrel_frei : ∀ (τ : Ty), τ.zeigerfrei = true → ∀ (v : Wert D τ) (v' : Wert D' (E.tyE τ)),
    E.VRel K τ v v' ↔ v' = E.valE τ v
  | .int _ _, _, _, _ => Iff.rfl
  | .bool, _, _, _ => Iff.rfl
  | .opt _, _, _, _ => Iff.rfl
  | .sum _, _, _, _ => Iff.rfl
  | .why _, _, _, _ => Iff.rfl
  | .never, _, _, _ => Iff.rfl
  | .fl _ _, _, _, _ => Iff.rfl
  | .fnptr _, h, _, _ => absurd h (by simp [Ty.zeigerfrei])
  | .ptr _ _, _, _, _ => Iff.rfl
  | .ref _, _, _, _ => Iff.rfl

/-! ## Memories -/

/-- The type of a field of an image table, by the field it comes from. -/
theorem typ_feldZ (t : D.Tab) (f' : D'.Feld (E.tab t)) :
    D'.typ (E.tab t) f' = E.tyE (D.typ t (E.feldZ t f')) := by
  conv => lhs; rw [← E.feld_feldZ t f']
  exact E.typ t (E.feldZ t f')

/-- **A memory of `D'` restricted to `D`.** -/
def speicherZ (s : Speicher D') : Speicher D where
  slots := fun t k f => E.valZ K (D.typ t f) (castW (E.typ t f) (s.slots (E.tab t) k (E.feld t f)))
  globs := fun g => E.valZ K (D.gtyp g) (castW (E.gtyp g) (s.globs (E.glob g)))

/-- A slot of an image table, from a memory of `D`. -/
def slotBild (s : Speicher D) (t : D.Tab) (k : Int) (f' : D'.Feld (E.tab t)) :
    Wert D' (D'.typ (E.tab t) f') :=
  castW (E.typ_feldZ t f').symm (E.valE _ (s.slots t k (E.feldZ t f')))

/-- A slot of `D'`: the image's from `s`, every other from the context. -/
def slotE (ctx : Speicher D') (s : Speicher D) (t' : D'.Tab) (k : Int) (f' : D'.Feld t') :
    Wert D' (D'.typ t' f') :=
  match hz : E.tabZ t' with
  | none => ctx.slots t' k f'
  | some t => by
      have e : E.tab t = t' := E.tab_tabZ t' t hz
      subst e
      exact E.slotBild s t k f'

/-- A global of `D'`: the image's from `s`, every other from the context. -/
def globE (ctx : Speicher D') (s : Speicher D) (g' : D'.Glob) : Wert D' (D'.gtyp g') :=
  match hz : E.globZ g' with
  | none => ctx.globs g'
  | some g => by
      have e : E.glob g = g' := E.glob_globZ g' g hz
      subst e
      exact castW (E.gtyp g).symm (E.valE _ (s.globs g))

/-- **A memory of `D` embedded into `D'` around the context `ctx`.** -/
def speicherE (ctx : Speicher D') (s : Speicher D) : Speicher D' where
  slots := E.slotE ctx s
  globs := E.globE ctx s

theorem slotBild_feld (s : Speicher D) (t : D.Tab) (k : Int) (f : D.Feld t) :
    E.slotBild s t k (E.feld t f) = castW (E.typ t f).symm (E.valE _ (s.slots t k f)) := by
  unfold slotBild
  have key : ∀ (f0 : D.Feld t), f0 = f →
      ∀ h1 : D'.typ (E.tab t) (E.feld t f) = E.tyE (D.typ t f0),
        castW h1.symm (E.valE _ (s.slots t k f0)) = castW (E.typ t f).symm (E.valE _ (s.slots t k f)) := by
    intro f0 h h1; subst h; rfl
  exact key _ (E.feldZ_feld t f) (E.typ_feldZ t (E.feld t f))

theorem slotE_fremd (ctx : Speicher D') (s : Speicher D) {t' : D'.Tab} (h : E.tabZ t' = none)
    (k : Int) (f' : D'.Feld t') : E.slotE ctx s t' k f' = ctx.slots t' k f' := by
  unfold slotE
  split
  · rfl
  · rename_i t hz; rw [h] at hz; cases hz

theorem globE_fremd (ctx : Speicher D') (s : Speicher D) {g' : D'.Glob} (h : E.globZ g' = none) :
    E.globE ctx s g' = ctx.globs g' := by
  unfold globE
  split
  · rfl
  · rename_i g hz; rw [h] at hz; cases hz

theorem slotE_bild (ctx : Speicher D') (s : Speicher D) (t : D.Tab) (k : Int) (f' : D'.Feld (E.tab t)) :
    E.slotE ctx s (E.tab t) k f' = E.slotBild s t k f' := by
  unfold slotE
  split
  · rename_i hz; rw [E.tabZ_tab] at hz; cases hz
  · rename_i t0 hz
    have e : t0 = t := Option.some.inj ((E.tabZ_tab t).symm.trans hz).symm
    subst e
    rfl

theorem globE_bild (ctx : Speicher D') (s : Speicher D) (g : D.Glob) :
    E.globE ctx s (E.glob g) = castW (E.gtyp g).symm (E.valE _ (s.globs g)) := by
  unfold globE
  split
  · rename_i hz; rw [E.globZ_glob] at hz; cases hz
  · rename_i g0 hz
    have e : g0 = g := Option.some.inj ((E.globZ_glob g).symm.trans hz).symm
    subst e
    rfl

/-- **Restricting an embedding gives the memory back.** -/
theorem speicherZ_speicherE (ctx : Speicher D') (s : Speicher D) :
    E.speicherZ K (E.speicherE ctx s) = s := by
  cases s with
  | mk slots globs =>
    simp only [speicherZ, speicherE]
    congr 1
    · funext t k f
      rw [E.slotE_bild, E.slotBild_feld, castW_castW, castW_self]
      exact E.valZ_vrel K _ (E.vrel_valE K _ _)
    · funext g
      rw [E.globE_bild, castW_castW, castW_self]
      exact E.valZ_vrel K _ (E.vrel_valE K _ _)

/-! ## Environments -/

/-- An environment of `D` as an environment of `D'`. -/
def envE : {Γ : Ctx} → Env D Γ → Env D' (Γ.map E.tyE)
  | _, .nil => .nil
  | _, .cons v ρ => .cons (E.valE _ v) (envE ρ)

theorem envE_get : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ),
    (E.envE ρ).get (varE E x) = E.valE τ (ρ.get x)
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons _ ρ, .there x => envE_get ρ x

end Einbettung

end Gabbro.Grammatik.Einbettung
