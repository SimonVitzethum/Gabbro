module

public import Grammatik.Bausteine.Arena.Ownership.Body.Check.Lemmas

@[expose] public section



/-! **Soundness of the executable admission check.** Whatever the check
returns for a statement, block, end block or case arms is backed by a
derivation of the body judgment: a fall-through context by a derivation
into it, "never falls through" by a derivation into every bounded context.
One structural induction over the syntax, for every program. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. What an outcome supports -/

/-- What a check outcome supports, as a predicate on fall-through contexts. -/
def Supports (P : Context → Prop) : Out → Prop
  | some (some x) => P x ∧ x.bounded
  | some none => ∀ x, x.bounded → P x
  | none => True

theorem supports_mono {P Q : Context → Prop} {r : Out} (h : ∀ z, P z → Q z) (hp : Supports P r) :
    Supports Q r := by
  match r, hp with
  | some (some x), ⟨hx, hb⟩ => exact ⟨h x hx, hb⟩
  | some none, hp => exact fun x hx => h x (hp x hx)
  | none, _ => trivial

theorem supports_if {P : Context → Prop} {x : Context} {b : Bool} (h : b = true → P x) (hb : x.bounded) :
    Supports P (if b then some (some x) else none) := by
  cases b
  · trivial
  · exact ⟨h rfl, hb⟩

theorem supports_ifDead {P : Context → Prop} {b : Bool} (h : b = true → ∀ x, P x) :
    Supports P (if b then some none else none) := by
  cases b
  · trivial
  · exact fun x _ => h rfl x

/-- A map with a bounded section. -/
theorem supports_map {P : Context → Prop} {r : Out} (f g : Context → Context)
    (hfg : ∀ x, f (g x) = x) (hg : ∀ x, x.bounded → (g x).bounded) (hf : ∀ x, x.bounded → (f x).bounded)
    (h : Supports P r) : Supports (fun x => ∃ c1, P c1 ∧ x = f c1) (mapR f r) := by
  match r, h with
  | some (some c1), ⟨h1, hb1⟩ => exact ⟨⟨c1, h1, rfl⟩, hf c1 hb1⟩
  | some none, h => exact fun x hx => ⟨g x, h _ (hg x hx), (hfg x).symm⟩
  | none, _ => trivial

theorem supports_drop {P : Context → Prop} {r : Out} (h : Supports P r) :
    Supports (fun x => ∃ c1, P c1 ∧ x = c1.drop) (mapR Context.drop r) :=
  supports_map Context.drop (fun x => x.bind none) (fun x => Context.bind_drop x none)
    (fun _ hx => Context.bindNone_bounded hx) (fun _ hx => Context.drop_bounded hx) h

/-- Two branch outcomes join; the rule needs both branches into one weaker context. -/
theorem supports_join {P1 P2 Q : Context → Prop} {r1 r2 : Out} (h1 : Supports P1 r1) (h2 : Supports P2 r2)
    (hrule : ∀ x y z, P1 x → P2 y → Weaker z x → Weaker z y → Q z) : Supports Q (joinR r1 r2) := by
  cases hj : joinR r1 r2 with
  | none => trivial
  | some o =>
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := joinR_dead hj
      intro z hz
      exact hrule z z z (h1 z hz) (h2 z hz) (Weaker.refl hz) (Weaker.refl hz)
    | some j =>
      rcases joinR_live hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, hab⟩
      · obtain ⟨hy, hjb⟩ := h2
        exact ⟨hrule j j j (h1 j hjb) hy (Weaker.refl hjb) (Weaker.refl hjb), hjb⟩
      · obtain ⟨hx, hjb⟩ := h1
        exact ⟨hrule j j j hx (h2 j hjb) (Weaker.refl hjb) (Weaker.refl hjb), hjb⟩
      · obtain ⟨hx, hab'⟩ := h1
        obtain ⟨hy, hbb⟩ := h2
        obtain ⟨wa, wb⟩ := joinB_weaker hab' hbb hab
        exact ⟨hrule a b j hx hy wa wb, joinB_bounded hab' hbb hab⟩

/-- A loop body's outcome returns to the loop head. -/
theorem back_sound {P : Context → Prop} {kk : Context} {r : Out} (hkk : kk.bounded) (h : Supports P r)
    (hb : backB kk r = true) : ∃ c1, P c1 ∧ Weaker kk c1 := by
  rcases backB_sound hb with rfl | ⟨c1, rfl, hw⟩
  · exact ⟨kk, h kk hkk, Weaker.refl hkk⟩
  · exact ⟨c1, h.1, weakerB_sound hkk h.2 hw⟩

theorem supports_orElse {P : Context → Prop} {a b : Out} (ha : Supports P a) (hb : Supports P b) :
    Supports P (orElseR a b) := by
  match a, ha with
  | none, _ => exact hb
  | some (some x), ha => exact ha
  | some none, ha => exact ha

theorem supports_condDrop {P Q : Context → Prop} {b : Bool} {r : Out} (hr : b = true → Supports Q r)
    (hrule : b = true → ∀ c1, Q c1 → P c1.drop) : Supports P (if b then mapR Context.drop r else none) := by
  cases b
  · trivial
  · exact supports_mono (fun x ⟨c1, h1, hx⟩ => hx ▸ hrule rfl c1 h1) (supports_drop (hr rfl))

theorem supports_cond {P Q : Context → Prop} {b : Bool} {r : Out} (hr : b = true → Supports Q r)
    (hrule : b = true → ∀ c1, Q c1 → P c1) : Supports P (if b then r else none) := by
  cases b
  · trivial
  · exact supports_mono (hrule rfl) (hr rfl)

theorem supports_seq {k c : Context} {l : Bool} {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)}
    {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}
    {s : Stmt D V l Γ Λ Λ1} {rest : Block D V l Γ Λ1 Λ'} {r : Out} {f : Context → Out}
    (hs : Supports (OS A I out k c s) r) (hrest : ∀ c1, c1.bounded → Supports (OB A I out k c1 rest) (f c1)) :
    Supports (OB A I out k c (.cons s rest)) (seqR r f) := by
  match r, hs with
  | some (some c1), ⟨h1, hb1⟩ =>
    exact supports_mono (fun z hz => OB.cons s rest h1 hz) (hrest c1 hb1)
  | some none, hs => exact fun x _ => OB.dead s rest hs
  | none, _ => trivial

section Sound

variable {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn} {V : Vertrag D} {out : Flow.Output A V.erg}

/-! ## 2. Weakening the arms -/

theorem OArms.weaken : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {k c c' z : Context} {arms : Arms D V l Γ Λ Λ' cs}, OArms A I out k c arms c' → Weaker z c' →
      OArms A I out k c arms z
  | _, _, _, _, _, _, _, _, _, _, .nil, _ => OArms.nil
  | _, _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, hz =>
    OArms.cons b rest hb (hz.trans hw) (OArms.weaken hr hz)

theorem OGrund.weaken : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {k c c' z : Context} {arms : GrundArms D V l Γ Λ Λ' n}, OGrund A I out k c arms c' → Weaker z c' →
      OGrund A I out k c arms z
  | _, _, _, _, _, _, _, _, _, _, .nil, _ => OGrund.nil
  | _, _, _, _, _, _, _, _, _, _, .cons b rest hb hw hr, hz =>
    OGrund.cons b rest hb (hz.trans hw) (OGrund.weaken hr hz)

/-! ## 3. The induction -/

variable (hvoll : ∀ f, f ∈ fs)
include hvoll

end Sound
end Gabbro.Grammatik.ArenaOwnership.Body
