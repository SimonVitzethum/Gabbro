/- Part 1d of `Satz/T2/Teil1` (C11 split; pure move): the outcome predicates
   (`GutAusgang`/`GutEnd`), their pull-through, and the held-entry facts. -/
module

public import Grammatik.Kern.Syntax.Satz.T1
public import Grammatik.Kern.Syntax.Satz.T2.Teil1c

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- Rahmen und Spur eines Ausgangs gegen die Eingangswelt: `ok`/`leave`/`next`
    halten die Sperren, `zurueck`/`why` geben genau die gekreuzten Scopes frei
    (Spare + Rank aus dem statischen Scope-Check). -/
def GutAusgang (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : Ausgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' →
    match o with
    | .zurueck _ _ | .why _ _ => GutRetV W G V.haelt V.boden σ σ'
    | _ => Gut W G σ σ'

def GutEnd (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D)
    (o : EndAusgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' →
    match o with
    | .zurueck _ _ | .why _ _ => GutRetV W G V.haelt V.boden σ σ'
    | _ => Gut W G σ σ'

theorem GutAusgang.schrumpf {W G} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : GutAusgang W G σ o) : GutAusgang W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, Ausgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem GutAusgang.schrumpfArm {W G} {σ : World D} (c : Option Ty)
    {o : Ausgang V l (ArmCtx Γ c)} (h : GutAusgang W G σ o) :
    GutAusgang W G σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some _ => exact h.schrumpf

theorem GutEnd.schrumpf {W G} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : GutEnd W G σ o) : GutEnd W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp only [EndAusgang.welt, EndAusgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem GutEnd.zuAusgang {W G} {σ : World D} {o : EndAusgang V l Γ} (h : GutEnd W G σ o) :
    GutAusgang W G σ o.zuAusgang := by
  intro σ' hs; cases o <;> simp only [Ausgang.welt, EndAusgang.zuAusgang, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

/-- Ein Schritt, der schon gut ist, zieht durch einen Unterblock hindurch. -/
theorem GutAusgang.vor {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : Gut W G σ σ1) (h : GutAusgang W G σ1 o) : GutAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.trans (h _ hs)
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.trans (h _ hs)
  | next _ _ _ => exact h1.trans (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem GutEnd.vor {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : Gut W G σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.trans (h _ hs)
  | next _ _ _ => exact h1.trans (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- A releasing step pulls through a sub-block: non-returns keep the release,
    returns concatenate it. -/
theorem GutAusgang.vorRetV {W G} {haelt : List D.Lock} {boden : Option Int}
    {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : GutRetV W G haelt boden σ σ1) (h : GutAusgang W G σ1 o) :
    GutAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.transGut (h _ hs)
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem GutEnd.vorRetV {W G} {haelt : List D.Lock} {boden : Option Int}
    {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : GutRetV W G haelt boden σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRetV (h _ hs)
  | why _ _ => exact h1.transRetV (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- A releasing step pulls through a sub-block (plain release, no spare/rank). -/
theorem GutAusgang.vorRet {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : GutRet W G σ σ1) (h : GutAusgang W G σ1 o) : GutAusgang W G σ o := by
  intro σ' hs
  cases o with
  | ok _ _ => exact h1.transGut (h _ hs)
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

theorem GutEnd.vorRet {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : GutRet W G σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o := by
  intro σ' hs
  cases o with
  | zurueck _ _ => exact h1.transRet (h _ hs)
  | why _ _ => exact h1.transRet (h _ hs)
  | leave _ _ _ => exact h1.transGut (h _ hs)
  | next _ _ _ => exact h1.transGut (h _ hs)
  | logik _ => cases hs
  | hardware _ => cases hs

/-- `locks L { … }`: nehmen, Rumpf, geben. -/
theorem GutAusgang.gibt {W G} {σ : World D} (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt) {o : Ausgang V l Γ}
    (h : GutAusgang W G (σ.nimmt L) o) : GutAusgang W G σ (o.mapWelt (·.gibt L)) := by
  intro σ' hs
  cases o with
  | ok _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl)
  | zurueck _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibtRetV _ _ L hn (h _ rfl)
  | why _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibtRetV _ _ L hn (h _ rfl)
  | leave _ _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl)
  | next _ _ _ =>
      simp only [Ausgang.welt, Ausgang.mapWelt, Option.some.injEq] at hs ⊢
      subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl)
  | logik _ => simp only [Ausgang.welt, Ausgang.mapWelt, reduceCtorEq] at hs
  | hardware _ => simp only [Ausgang.welt, Ausgang.mapWelt, reduceCtorEq] at hs

/-- Von einem `Λ` zu einem, das hoechstens weniger Zeugnisse nennt, ueber einen guten Schritt. -/
theorem heldGenau_weiter {W G} {σ σ1 : World D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (hg : Gut W G σ σ1) (hh : HeldGenau Λ σ.haelt) :
    HeldGenau Λ' σ1.haelt := by
  intro L; rw [hg.haelt, hm L]; exact hh L

theorem held_anfang (S : Signatur D.Tab D.Glob D.Lock D.Marke) (L : D.Lock) :
    Res.held L ∈ Signatur.anfang D S ↔ L ∈ S.haelt := by
  unfold Signatur.anfang
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨M, hM, hML⟩ | ⟨m, _, hm⟩)
    · cases hML; exact hM
    · cases m; simp only [Res.vonMarke, reduceCtorEq] at hm
  · intro h; exact .inl ⟨L, h, rfl⟩

theorem held_ende (V : Vertrag D) (L : D.Lock) : Res.held L ∈ V.ende ↔ L ∈ V.haelt := by
  unfold Vertrag.ende
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨M, hM, hML⟩ | ⟨m, _, hm⟩)
    · cases hML; exact hM
    · cases m; simp only [Res.vonMarke, reduceCtorEq] at hm
  · intro h; exact .inl ⟨L, h, rfl⟩

/-- Der Rufer haelt genau, was der Gerufene am Eintritt nennt. -/
theorem heldGenau_ruf {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)} {h : List D.Lock}
    (hh' : ∀ L, Res.held L ∈ Λ ↔ L ∈ S.haelt) (hh : HeldGenau Λ h) : HeldGenau (Signatur.anfang D S) h := by
  intro L; rw [held_anfang, ← hh' L]; exact hh L

theorem heldGenau_locks {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock) (hh : HeldGenau Λ h) :
    HeldGenau (Res.held L :: Λ) (L :: h) := by
  intro M
  simp only [List.mem_cons, Res.held.injEq]
  constructor
  · rintro (rfl | hM)
    · exact .inl rfl
    · exact .inr ((hh M).mp hM)
  · rintro (rfl | hM)
    · exact .inl rfl
    · exact .inr ((hh M).mpr hM)

/-- Ein `locks L` nimmt eine Sperre, die der Faden NICHT haelt: alles Gehaltene hat kleineren
    Rang, und `rang L < rang L` ist keine Zahl. -/
theorem nicht_gehalten {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L) (hh : HeldGenau Λ h) :
    (∀ M ∈ h, D.rang M < D.rang L) ∧ L ∉ h := by
  refine ⟨fun M hM => hr M ((hh M).mpr hM), ?_⟩
  intro hL
  have := hr L ((hh L).mpr hL)
  omega

end Gabbro.Grammatik

