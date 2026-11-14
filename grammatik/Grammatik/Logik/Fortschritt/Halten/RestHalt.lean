/-
  File:      Grammatik/Logik/Fortschritt/Halten/RestHalt.lean
  Subject:   THE HOLD-BOUND CHECK READ ON A RESIDUE: `GRest.hR` says every block, end block and loop body
             still to run passes the section walker `haltB`/`haltE` (Halten/Pruefung.lean). It is what the
             thread invariant `HaltInvG` (Halten/SchrittHalt.lean) carries along every rule of machine G, so
             that the `locks` statement a thread takes was checked by `haltPasst`. The walker runs at the
             return-predicate price `ep` the frame's body was checked with (C05); it never changes along a
             frame, so every rule carries `hR` at the same `ep`.
-/
module
public import Grammatik.Logik.Fortschritt.Halten.Pruefung
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The residue predicate**: every block, end block and loop body still to run passes the walker. -/
def GRest.hR (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => haltE h ep c Z pa e = true
  | _, _, _, .dann b k => haltB h ep c Z pa b = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .schrumpf k => GRest.hR h ep c Z pa k
  | _, _, _, .frei _ k => GRest.hR h ep c Z pa k
  | _, _, _, .trav _ _ body _ k => haltB h ep c Z pa body = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .travRest _ _ body _ k => haltB h ep c Z pa body = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .verbrauch _ _ _ _ _ _ body _ k => haltB h ep c Z pa body = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .verbrauchRest _ _ _ _ _ _ body _ _ k =>
      haltB h ep c Z pa body = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .wieder _ _ body ueber k =>
      haltB h ep c Z pa body = true ∧ haltB h ep c Z pa ueber = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .wiederRest _ _ body ueber k =>
      haltB h ep c Z pa body = true ∧ haltB h ep c Z pa ueber = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .ewig _ _ _ body k => haltB h ep c Z pa body = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .ewigRest _ _ _ body k => haltB h ep c Z pa body = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .wartet b k => haltB h ep c Z pa b = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .wartetSonst _ err b k =>
      haltE h ep c Z pa err = true ∧ haltB h ep c Z pa b = true ∧ GRest.hR h ep c Z pa k
  | _, _, _, .abbruch k => GRest.hR h ep c Z pa k
  | _, _, _, .leer => True
  | _, _, _, .rueckBereit _ k => GRest.hR h ep c Z pa k
  | _, _, _, .zurueckgekehrt _ => True
  | _, _, _, .aufraeumen _ _ => True

section Hilfen

variable (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat) {V : Vertrag D}
  {l : Bool}

/-- An end block run as a block passes the walker exactly when the end block does. -/
theorem haltB_alsBlock :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
      haltB h ep c Z pa e.alsBlock.2 = haltE h ep c Z pa e
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .retScoped _ _ => rfl
  | _, _, .retWhyScoped _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .bindCallIndElse p args he hp hr err rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock t]
  | _, _, .float op a b lo hi rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .floatLit q lo hi rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .floatOf e lo hi rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]
  | _, _, .floatNarrow e lo hi sonst rest => by
      simp only [Endblock.alsBlock, haltB, haltE, haltB_alsBlock rest]

theorem haltB_armWahlG {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    haltArms h ep c Z pa arms = true → haltB h ep c Z pa (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, hb => by
      simp only [haltArms, Bool.and_eq_true] at hb
      exact hb.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, hb => by
      simp only [haltArms, Bool.and_eq_true] at hb
      exact haltB_armWahlG rest _ hb.2

theorem haltB_grundWahlG {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    haltGArms h ep c Z pa arms = true → haltB h ep c Z pa (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, hb => by
      simp only [haltGArms, Bool.and_eq_true] at hb
      exact hb.1
  | _, .cons b rest, ⟨k + 1, hk⟩, hb => by
      simp only [haltGArms, Bool.and_eq_true] at hb
      exact haltB_grundWahlG rest _ hb.2

/-- The residue behind an optional foreign binder carries the predicate of its continuation. -/
theorem GRest.hR_weiterOpt {Γ : Ctx} {Λ Λ' : List (Res D)} (e : Option Ty)
    (k : GRest D V l Γ Λ') : GRest.hR h ep c Z pa (GRest.weiterOpt (Λ := Λ) e k) ↔ GRest.hR h ep c Z pa k := by
  cases e <;> exact Iff.rfl

end Hilfen

/-- A resumed caller keeps the predicate its suspended residue had. -/
theorem antwortRestG_hR (h : D.Lock → Option Nat) (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool)
    (pa : Nat)
    (g : D.Fn) (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende) {V : Vertrag D}
    (x y : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (ha : antwortRestG g a x = some y) (hm : GRest.hR h ep c Z pa x.2.2.2.2) :
    GRest.hR h ep c Z pa y.2.2.2.2 := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  cases a with
  | inl v =>
      cases r with
      | wartet b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha; subst y; exact hm
          · cases ha
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha; subst y; exact hm.2
          · cases ha
      | _ => simp only [antwortRestG, Option.some.injEq] at ha; subst y; exact hm
  | inr grund =>
      cases r with
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha; subst y
            exact ⟨by rw [haltB_alsBlock]; exact hm.1, hm.2.2⟩
          · cases ha
      | _ => cases ha

/-- Answering is a head-local completion or a pop that resumes the caller with its predicate. -/
theorem rufAntwortG_hRcls (h : D.Lock → Option Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (pa : Nat)
    {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ a = some z') :
    (z'.stapel = z.stapel ∧
      ∀ ep, (GRest.hR h ep c Z pa z.kopf.rest.2.2.2.2 → GRest.hR h ep c Z pa z'.kopf.rest.2.2.2.2)) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      z.stapel = caller :: rst ∧ z'.stapel = rst ∧
      ∀ ep, (GRest.hR h ep c Z pa caller.rest.2.2.2.2 → GRest.hR h ep c Z pa z'.kopf.rest.2.2.2.2)) := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact Or.inl ⟨rfl, fun _ _ => trivial⟩
  | cons cl st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a cl.rest = some r := by
        cases hr : antwortRestG z.kopf.f a cl.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      exact Or.inr ⟨cl, st, rfl, rfl, fun ep hm => antwortRestG_hR h ep c Z pa _ _ _ _ hr hm⟩

end Gabbro.Grammatik
