module
public import Grammatik.Zielsatz.Einbettung.Syntax
public import Grammatik.Zielsatz.Einbettung.Syntaxb
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
  | .prod _ fs => Ty.fieldsZeigerfrei fs
  | _ => true

/-- Sum traversal for the same pointer-free predicate, without a depth bound. -/
def _root_.Gabbro.Grammatik.Ty.casesZeigerfrei : List (Option Ty) → Bool
  | [] => true
  | none :: cs => Ty.casesZeigerfrei cs
  | some τ :: cs => τ.zeigerfrei && Ty.casesZeigerfrei cs

/-- Check every original product field with the same complete-value predicate. -/
def _root_.Gabbro.Grammatik.Ty.fieldsZeigerfrei : List Ty → Bool
  | [] => true
  | τ :: fs => τ.zeigerfrei && Ty.fieldsZeigerfrei fs
end

@[simp] theorem _root_.Gabbro.Grammatik.Ty.casesZeigerfrei_eq_all (cs : List (Option Ty)) :
    Ty.casesZeigerfrei cs = cs.all (fun | none => true | some τ => τ.zeigerfrei) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [Ty.casesZeigerfrei, List.all_cons, ih, Bool.true_and]

@[simp] theorem _root_.Gabbro.Grammatik.Ty.fieldsZeigerfrei_eq_all (fs : List Ty) :
    Ty.fieldsZeigerfrei fs = fs.all Ty.zeigerfrei := by
  induction fs with
  | nil => rfl
  | cons τ fs ih => simp only [Ty.fieldsZeigerfrei, List.all_cons, ih]

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
    apply Subtype.ext
    change (K.zeiger n (E.fn f) ((E.passt f n).trans h)).val = f
    unfold Rueck.zeiger
    split
    · rename_i g hz
      exact Option.some.inj (hz.symm.trans (E.fnZ_fn f))
    · rename_i hz
      rw [E.fnZ_fn] at hz
      cases hz) τ v

/-- **A value of `D` beside a value of `D'`**: equal through the embedding, except that a head of
    `D` stands beside every function outside the image of its signature. -/
def VRel : (τ : Ty) → Wert D τ → Wert D' (E.tyE τ) → Prop
  | .fnptr n, v, v' => v'.1 = E.fn v.1 ∨ (E.fnZ v'.1 = none ∧ K.rep n = some v.1)
  | .arr τ _, v, v' => ∀ j, VRel τ (v j) (v' j)
  | .sum cs, v, v' => E.valZ K (.sum cs) v' = v
  | .prod r fs, v, v' => E.valZ K (.prod r fs) v' = v
  | τ, v, v' => v' = E.valE τ v

/-- Payload relations use the same function representatives as all other values. -/
def NRel : (c : Option Ty) → Nutzlast D.Fn D.passt c →
    Nutzlast D'.Fn D'.passt (c.map E.tyE) → Prop
  | none, _, _ => True
  | some τ, v, v' => E.VRel K τ v v'

theorem vrel_valE : ∀ (τ : Ty) (v : Wert D τ), E.VRel K τ v (E.valE τ v)
  | .int _ _, _ => rfl
  | .bool, _ => rfl
  | .opt _, _ => rfl
  | .sum cs, v => E.valZ_valE K (.sum cs) v
  | .why _, _ => rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr _, _ => Or.inl rfl
  | .ptr _, _ => rfl
  | .ref _, _ => rfl
  | .arr τ _, v => fun j => vrel_valE τ (v j)
  | .str _, _ => rfl
  | .prod r fs, v => E.valZ_valE K (.prod r fs) v

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
        · rename_i hr; exact absurd (K.voll n f' h' hz) (by rw [hr]; simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true])
  | .ptr _, _ => rfl
  | .ref _, _ => rfl
  | .arr τ _, v' => fun j => vrel_valZ τ (v' j)
  | .str _, _ => rfl
  | .prod _ _, _ => rfl

theorem valZ_vrel : ∀ (τ : Ty) {v : Wert D τ} {v' : Wert D' (E.tyE τ)}, E.VRel K τ v v' →
    E.valZ K τ v' = v
  | .int _ _, _, _, h => by subst h; rfl
  | .bool, _, _, h => by subst h; rfl
  | .opt _, _, _, h => by subst h; rfl
  | .sum _, _, _, h => h
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
  | .ptr _, _, _, h => by subst h; rfl
  | .ref _, _, _, h => by subst h; rfl
  | .arr τ _, _, _, h => funext fun j => valZ_vrel τ (h j)
  | .str _, _, _, h => by subst h; rfl
  | .prod _ _, _, _, h => h

/-- Restricting related payloads returns the complete source payload. -/
theorem nrel_valZ : ∀ (c : Option Ty) (v : Nutzlast D.Fn D.passt c)
    (v' : Nutzlast D'.Fn D'.passt (c.map E.tyE)), E.NRel K c v v' →
      Nutzlast.restrict E.num E.tnum (fun n value => K.zeiger n value.1 value.2) c v' = v
  | none, v, v', _ => by cases v; cases v'; rfl
  | some τ, _, _, h => E.valZ_vrel K τ h

/-- The value relation names exactly the unique source produced by restriction.
    For sums this recursively compares the active tag and the complete payload;
    foreign function representatives inside a payload remain visible. -/
theorem vrel_iff_valZ (τ : Ty) (v : Wert D τ) (v' : Wert D' (E.tyE τ)) :
    E.VRel K τ v v' ↔ E.valZ K τ v' = v :=
  ⟨E.valZ_vrel K τ, fun h => h ▸ E.vrel_valZ K τ v'⟩

mutual
/-- Pointer-free values have a two-sided transport even when the larger
    declaration also contains foreign function representatives. -/
theorem valE_valZ_frei : ∀ (τ : Ty), τ.zeigerfrei = true →
    ∀ v : Wert D' (E.tyE τ), E.valE τ (E.valZ K τ v) = v
  | .int _ _, _, _ | .bool, _, _ | .opt _, _, _ | .why _, _, _ | .never, _, _
  | .fl _ _, _, _ | .ptr _, _, _ | .ref _, _, _ | .str _, _, _ => rfl
  | .fnptr _, h, _ => by simp only [Ty.zeigerfrei, Bool.false_eq_true] at h
  | .arr τ _, h, v => funext fun i => valE_valZ_frei τ h (v i)
  | .sum cs, h, v => by
    simp only [Ty.zeigerfrei, Ty.casesZeigerfrei_eq_all] at h
    exact valE_valZSum_frei cs h v
  | .prod _ fs, h, v => valE_valZProd_frei fs h v
termination_by τ _ _ => sizeOf τ
decreasing_by all_goals (simp_wf <;> omega)

theorem valE_valZSum_frei : ∀ (cs : List (Option Ty)),
    (cs.all fun | none => true | some τ => τ.zeigerfrei) = true →
    ∀ v : Wert D' (.sum (Ty.mapCases E.num E.tnum cs)),
      Val.relocateSum E.num E.tnum
        (fun _ value => ⟨E.fn value.1, (E.passt value.1 _).trans value.2⟩) cs
        (Val.restrictSum E.num E.tnum (fun n value => K.zeiger n value.1 value.2) cs v) = v
  | [], _, ⟨i, _⟩ => i.elim0
  | none :: _, _, ⟨⟨0, _⟩, _⟩ => rfl
  | some τ :: cs, h, ⟨⟨0, hi⟩, v⟩ =>
    congrArg (fun w => (⟨⟨0, hi⟩, w⟩ : Wert D' (.sum (Ty.mapCases E.num E.tnum (some τ :: cs)))))
      (valE_valZ_frei τ (Bool.and_eq_true.mp h).1 v)
  | none :: cs, h, ⟨⟨i + 1, hi⟩, v⟩ =>
    congrArg (fun z : Wert D' (.sum (Ty.mapCases E.num E.tnum cs)) =>
      (⟨z.1.succ, z.2⟩ : Wert D' (.sum (none :: Ty.mapCases E.num E.tnum cs))))
      (valE_valZSum_frei cs (Bool.and_eq_true.mp h).2
        ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩)
  | some τ :: cs, h, ⟨⟨i + 1, hi⟩, v⟩ =>
    congrArg (fun z : Wert D' (.sum (Ty.mapCases E.num E.tnum cs)) =>
      (⟨z.1.succ, z.2⟩ : Wert D' (.sum (some (E.tyE τ) :: Ty.mapCases E.num E.tnum cs))))
      (valE_valZSum_frei cs (Bool.and_eq_true.mp h).2
        ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩)
termination_by cs _ _ => sizeOf cs
decreasing_by all_goals (simp_wf <;> omega)

/-- The same two-sided transport for the complete ordered product payload. -/
theorem valE_valZProd_frei : ∀ (fs : List Ty), Ty.fieldsZeigerfrei fs = true →
    ∀ v : ProdVal D'.Fn D'.passt (Ty.mapFields E.num E.tnum fs),
      ProdVal.relocate E.num E.tnum
        (fun _ value => ⟨E.fn value.1, (E.passt value.1 _).trans value.2⟩) fs
        (ProdVal.restrict E.num E.tnum (fun n value => K.zeiger n value.1 value.2) fs v) = v
  | [], _, _ => rfl
  | τ :: fs, h, v =>
    ProdVal.pcons_congr (valE_valZ_frei τ (Bool.and_eq_true.mp h).1 v.1)
      (valE_valZProd_frei fs (Bool.and_eq_true.mp h).2 v.2)
termination_by fs _ _ => sizeOf fs
decreasing_by all_goals (simp_wf <;> omega)
end

/-- Pointer-free values are related exactly when they are equal through the embedding. -/
theorem vrel_frei : ∀ (τ : Ty), τ.zeigerfrei = true → ∀ (v : Wert D τ) (v' : Wert D' (E.tyE τ)),
    E.VRel K τ v v' ↔ v' = E.valE τ v := by
  intro τ h v v'
  rw [E.vrel_iff_valZ K τ v v']
  constructor
  · intro hv
    have ht := E.valE_valZ_frei K τ h v'
    rw [hv] at ht
    exact ht.symm
  · intro hv
    rw [hv]
    exact E.valZ_valE K τ v

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
