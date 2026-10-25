import Grammatik.Zielsatz.Einbettung.Syntax

/-!
  File:      Grammatik/Zielsatz/Einbettung/Welt.lean
  Subject:   Values, memories and environments under an embedding (stage E1).

  A project's carriers hold values the project can name: until callbacks into foreign functions
  are covered (stage E4), its tables, globals and parameters carry no function-pointer type
  (`ZeigerfreiD`), and a value of such a type goes back from `D'` to `D` (`valZ`). A memory of
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

/-- **No function pointer comes in from outside**: tables and globals of `D` carry none, and no
    function result, axiom result or register answer is one (a foreign answer could name a
    function `D` does not know; callbacks are stage E4). -/
structure ZeigerfreiD (D : Deklaration) : Prop where
  typ : ∀ t f, (D.typ t f).zeigerfrei = true
  gtyp : ∀ g, (D.gtyp g).zeigerfrei = true
  erg : ∀ f τ, D.erg f = some τ → τ.zeigerfrei = true
  aerg : ∀ a τ, D.aerg a = some τ → τ.zeigerfrei = true
  rtyp : ∀ r, (D.rtyp r).zeigerfrei = true

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

/-- A value of a pointer-free type, back in `D`. -/
def valZ : (τ : Ty) → τ.zeigerfrei = true → Wert D' (E.tyE τ) → Wert D τ
  | .int _ _, _, v => v
  | .bool, _, v => v
  | .opt _, _, v => v
  | .sum _, _, v => v
  | .why _, _, v => v
  | .never, _, v => v
  | .fl _ _, _, v => v
  | .fnptr _, h, _ => absurd h (by simp [Ty.zeigerfrei])
  | .ptr _ _, _, v => v
  | .ref _, _, v => v

theorem valZ_valE : ∀ (τ : Ty) (h : τ.zeigerfrei = true) (v : Wert D τ), E.valZ τ h (E.valE τ v) = v
  | .int _ _, _, _ => rfl
  | .bool, _, _ => rfl
  | .opt _, _, _ => rfl
  | .sum _, _, _ => rfl
  | .why _, _, _ => rfl
  | .never, _, _ => rfl
  | .fl _ _, _, _ => rfl
  | .fnptr _, h, _ => absurd h (by simp [Ty.zeigerfrei])
  | .ptr _ _, _, _ => rfl
  | .ref _, _, _ => rfl

theorem valE_valZ : ∀ (τ : Ty) (h : τ.zeigerfrei = true) (v : Wert D' (E.tyE τ)), E.valE τ (E.valZ τ h v) = v
  | .int _ _, _, _ => rfl
  | .bool, _, _ => rfl
  | .opt _, _, _ => rfl
  | .sum _, _, _ => rfl
  | .why _, _, _ => rfl
  | .never, _, _ => rfl
  | .fl _ _, _, _ => rfl
  | .fnptr _, h, _ => absurd h (by simp [Ty.zeigerfrei])
  | .ptr _ _, _, _ => rfl
  | .ref _, _, _ => rfl

theorem valE_inj (τ : Ty) (h : τ.zeigerfrei = true) {v w : Wert D τ} (e : E.valE τ v = E.valE τ w) :
    v = w := by
  rw [← E.valZ_valE τ h v, ← E.valZ_valE τ h w, e]

/-! ## Memories -/

/-- The type of a field of an image table, by the field it comes from. -/
theorem typ_feldZ (t : D.Tab) (f' : D'.Feld (E.tab t)) :
    D'.typ (E.tab t) f' = E.tyE (D.typ t (E.feldZ t f')) := by
  conv => lhs; rw [← E.feld_feldZ t f']
  exact E.typ t (E.feldZ t f')

/-- **A memory of `D'` restricted to `D`.** -/
def speicherZ (hZ : ZeigerfreiD D) (s : Speicher D') : Speicher D where
  slots := fun t k f => E.valZ (D.typ t f) (hZ.typ t f) (castW (E.typ t f) (s.slots (E.tab t) k (E.feld t f)))
  globs := fun g => E.valZ (D.gtyp g) (hZ.gtyp g) (castW (E.gtyp g) (s.globs (E.glob g)))

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
theorem speicherZ_speicherE (hZ : ZeigerfreiD D) (ctx : Speicher D') (s : Speicher D) :
    E.speicherZ hZ (E.speicherE ctx s) = s := by
  cases s with
  | mk slots globs =>
    simp only [speicherZ, speicherE]
    congr 1
    · funext t k f
      rw [E.slotE_bild, E.slotBild_feld, castW_castW, castW_self]
      exact E.valZ_valE _ _ _
    · funext g
      rw [E.globE_bild, castW_castW, castW_self]
      exact E.valZ_valE _ _ _

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
