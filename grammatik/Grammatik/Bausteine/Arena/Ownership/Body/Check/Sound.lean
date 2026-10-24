import Grammatik.Bausteine.Arena.Ownership.Body.Check.Lemmas

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

mutual

theorem chkS_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (st : Stmt D V l Γ Λ Λ') (k c : Context),
    k.bounded → c.bounded → Supports (OS A I out k c st) (chkS A I fs out st k c)
  | _, _, _, _, .assignSlot t f i e hw hL, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OS.assignSlot t f i e hw hL h.1.1.1 h.1.1.2 h.1.2 h.2) hc
  | _, _, _, _, .assignThru p t ht f i e hw hL, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OS.assignThru p t ht f i e hw hL h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2) hc
  | _, _, _, _, .assignGlob g e hw hL, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OS.assignGlob g e hw hL h.1 h.2) hc
  | _, _, _, _, .putBytes t f hf n i hlo hhi e hw hL, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OS.putBytes t f hf n i hlo hhi e hw hL h.1.1 h.1.2 h.2) hc
  | _, _, _, _, .assignVar x e, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => OS.assignVar x e h) (Context.assign_bounded hc x e)
  | _, _, _, _, .shift t f hτ i von nach hn he hw hL, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OS.shift t f hτ i von nach hn he hw hL h.1.1 h.1.2 h.2) hc
  | _, _, _, _, .ite cond t e, k, c, hk, hc => by
    simp only [chkS]
    split
    · rename_i hcond
      exact supports_join (chkB_sound t k c hk hc) (chkB_sound e k c hk hc)
        (fun x y z hx hy wx wy => OS.ite cond t e hcond (OB.weaken t hx wx) (OB.weaken e hy wy))
    · trivial
  | _, _, _, _, .onOption o p a, k, c, hk, hc => by
    simp only [chkS]
    split
    · rename_i ho
      exact supports_join (supports_drop (chkB_sound p k (c.bind none) hk (Context.bindNone_bounded hc)))
        (chkB_sound a k c hk hc)
        (fun x y z hx hy wx wy => by
          obtain ⟨c1, hp1, rfl⟩ := hx
          exact OS.onOption o p a ho hp1 wx (OB.weaken a hy wy))
    · trivial
  | _, _, _, _, .onTag v arms, k, c, hk, hc => by
    simp only [chkS]
    split
    · rename_i hv
      exact supports_mono (fun z hz => OS.onTag v arms hv hz) (chkArms_sound arms k c hk hc)
    · trivial
  | _, _, _, _, .onWhy r arms, k, c, hk, hc => by
    simp only [chkS]
    split
    · rename_i hr
      exact supports_mono (fun z hz => OS.onWhy r arms hr hz) (chkGrund_sound arms k c hk hc)
    · trivial
  | _, _, _, _, .call f args hp hr, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true] at h
      exact OS.call f args hp hr h.1 h.2) (dropContext_bounded (afterCall_bounded hc) _)
  | _, _, _, _, .callInd p args hp hr, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true] at h
      exact OS.callInd p args hp hr _ _ (sigCompatB_sound hvoll h.1.2) h.1.1.1 h.1.1.2 h.2)
      (dropContextB_bounded (afterCall_bounded hc) _)
  | _, _, _, _, .locks L hr body, k, c, hk, hc => by
    simp only [chkS]
    exact supports_mono (fun z hz => OS.locks L hr body hz) (chkB_sound body k c hk hc)
  | _, _, _, _, .breaking i body, k, c, hk, hc => by
    simp only [chkS]
    exact supports_mono (fun z hz => OS.breaking i body hz) (chkB_sound body k c hk hc)
  | _, _, _, _, .traverse t inv body, k, c, hk, hc => by
    simp only [chkS]
    have hkk := loopCtx_bounded hc (assignsB body)
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      obtain ⟨x, ⟨c1, hb1, rfl⟩, hw⟩ := back_sound hkk
        (supports_drop (chkB_sound body _ _ hkk (Context.bindNone_bounded hkk))) h.2
      exact ⟨OS.traverse t inv body (loopCtx_weaker hc _) h.1 hb1 hw, hkk⟩
    · trivial
  | _, _, _, _, .retry n bis body u, k, c, hk, hc => by
    simp only [chkS]
    have hkk := loopCtx_bounded hc (assignsB body ++ assignsB u)
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      obtain ⟨c1, hb1, hw1⟩ := back_sound hkk (chkB_sound body _ _ hkk hkk) h.1.2
      obtain ⟨cu, hbu, hwu⟩ := back_sound hkk (chkB_sound u k _ hk hkk) h.2
      exact ⟨OS.retry n bis body u (loopCtx_weaker hc _) h.1.1 hb1 hw1 (OB.weaken u hbu hwu), hkk⟩
    · trivial
  | _, _, _, _, .forever a inv body, k, c, hk, hc => by
    simp only [chkS]
    have hkk := loopCtx_bounded hc (assignsB body)
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      obtain ⟨c1, hb1, hw1⟩ := back_sound hkk (chkB_sound body _ _ hkk hkk) h.2
      exact ⟨OS.forever a inv body (loopCtx_weaker hc _) h.1 hb1 hw1, hkk⟩
    · trivial
  | _, _, _, _, .axiomCall a args hres hw hg hd hgd, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OS.axiomCall a args hres hw hg hd hgd h.1 h.2) hc
  | _, _, _, _, .regWrite r hk' e, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => OS.regWrite r hk' e h) hc
  | _, _, _, _, .transition r hk' m hm hl maske bits, k, c, _, hc => by
    simp only [chkS]
    exact ⟨OS.transition r hk' m hm hl maske bits, hc⟩
  | _, _, _, _, .publish g e payload hp hw hL, k, c, _, hc => by
    simp only [chkS]
    exact supports_if (fun h => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact OS.publish g e payload hp hw hL h.1 h.2) hc
  | _, _, _, _, .advances m a h hs, k, c, _, hc => by
    simp only [chkS]
    exact ⟨OS.advances m a h hs, hc⟩
  | _, _, _, _, .retires m st h a, k, c, _, hc => by
    simp only [chkS]
    exact ⟨OS.retires m st h a, hc⟩
  | _, _, _, _, .ret e hΛ, k, c, _, _ => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.ret e hΛ h)
  | _, _, _, _, .retWhy r hΛ, k, c, _, _ => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.retWhy r hΛ h)
  | _, _, _, _, .leave hl, k, c, hk, hc => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.leave hl (exitsB_sound hk hc h))
  | _, _, _, _, .next hl, k, c, hk, hc => by
    simp only [chkS]
    exact supports_ifDead (fun h x => OS.next hl (exitsB_sound hk hc h))

theorem chkB_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k c : Context),
    k.bounded → c.bounded → Supports (OB A I out k c b) (chkB A I fs out b k c)
  | _, _, _, _, .nil, k, c, _, hc => by
    simp only [chkB]
    exact ⟨OB.nil, hc⟩
  | _, _, _, _, .cons s rest, k, c, hk, hc => by
    have hgen := supports_seq (chkS_sound s k c hk hc) (fun c1 hc1 => chkB_sound rest k c1 hk hc1)
    have hrel := fun c2 p hc2 => relB_sound rest k c2 p hk hc2
    cases s with
    | assignSlot t f i e hw hL =>
      simp only [chkB]
      by_cases hcb : ((if ht : t = A.tab then decide (ht ▸ f = A.nxt) else false) &&
          exprGlob e == some A.kopf) = true
      · rw [if_pos hcb]
        simp only [Bool.and_eq_true, beq_iff_eq] at hcb
        obtain ⟨ht, hf⟩ := linkField_sound hcb.1
        split
        · rename_i p c2 o hp hcons
          exact supports_mono (fun x hx => by
            obtain ⟨g, e2, hwK, hLK, rest', rfl, hg, he2, hob⟩ := hx
            exact OB.release t f i e hw hL g e2 hwK hLK rest' ht hf hp hcb.2 hg he2 hcons hob)
            (hrel c2 p (consume_bounded hc hcons))
        · trivial
      · rw [if_neg hcb]
        exact hgen
    | _ => simp only [chkB]; exact hgen
  | _, _, _, _, .bind e rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindOrigin_bounded hc e))
      (fun h c1 h1 => OB.bind e rest h h1)
  | _, _, _, _, .bindCall f args he hp hr rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop
      (fun _ => chkB_sound rest k _ hk (resultContext_bounded (afterCall_bounded hc) _))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.bindCall f args he hp hr rest h.1 h.2 h1)
  | _, _, _, _, .bindCallInd p args he hp hr rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop
      (fun _ => chkB_sound rest k _ hk (resultContextB_bounded (afterCall_bounded hc) _))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.bindCallInd p args he hp hr rest _ _ (sigCompatB_sound hvoll h.1.2) h.1.1.1 h.1.1.2 h.2 h1)
  | _, _, _, _, .bindCallElse f args he hp hr err rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop
      (fun _ => chkB_sound rest k _ hk (resultContext_bounded (afterCall_bounded hc) _))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.bindCallElse f args he hp hr err rest h.1.1 h.1.2
          (chkE_sound err k _ hk (Context.bindNone_bounded (afterCall_bounded hc)) h.2) h1)
  | _, _, _, _, .bindAxiom a args he hw hg hd hgd rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindNone_bounded hc))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact OB.bindAxiom a args he hw hg hd hgd rest h.1 h.2 h1)
  | _, _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindNone_bounded hc))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact OB.bindAxiomElse a args he hr hw hg hd hgd err rest h.1.1 h.1.2
          (chkE_sound err k _ hk (Context.bindNone_bounded hc) h.2) h1)
  | _, _, _, _, .regRead r hk' rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_mono (fun x ⟨c1, h1, hx⟩ => hx ▸ OB.regRead r hk' rest h1)
      (supports_drop (chkB_sound rest k _ hk (Context.bindNone_bounded hc)))
  | _, _, _, _, .regReadElse r hk' zusage sonst rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindNone_bounded hc))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.regReadElse r hk' zusage sonst rest h.1 (chkE_sound sonst k c hk hc h.2) h1)
  | _, _, _, _, .awaits g payload hp hL ha rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_mono (fun x ⟨c1, h1, hx⟩ => hx ▸ OB.awaits g payload hp hL ha rest h1)
      (supports_drop (chkB_sound rest k _ hk (Context.bindNone_bounded hc)))
  | _, _, _, _, .exchange g neu hw hL rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindNone_bounded hc))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact OB.exchange g neu hw hL rest h.1 h.2 h1)
  | _, Γ, _, _, .narrow e lo' hi' voll rest, k, c, hk, hc => by
    simp only [chkB]
    refine supports_orElse ?_ ?_
    · split
      · rename_i hcv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcv
        have hvoll' := chkE_sound voll k c hk hc hcv.1
        split
        · rename_i hz
          simp only [beq_iff_eq] at hz
          exact supports_mono (fun x hx => by
            obtain ⟨c1, ⟨t, f, i, ev, hw, hL, rest1, rfl, hn, hi, hev, hs, g, e2, hwG, hLG, rest2, rfl, hg,
              he2, hob⟩, rfl⟩ := hx
            exact OB.allocCounter e lo' hi' voll t f i ev hw hL g e2 hwG hLG rest2 hz hcv.2 hn hg he2 hi hev hs
              hvoll' hob)
            (supports_drop (ctr1B_sound rest k c.bindFresh Γ.length hk (Context.bindFresh_bounded hc)))
        · split
          · rename_i _ hz
            simp only [beq_iff_eq] at hz
            exact supports_mono (fun x hx => by
              obtain ⟨c1, ⟨g, e2, hwK, hLK, rest1, rfl, hg, he2, t, f, i, ev, hw, hL, rest2, rfl, hn, hi, hev,
                hs, hob⟩, rfl⟩ := hx
              exact OB.allocList e lo' hi' voll g e2 hwK hLK t f i ev hw hL rest2 hz hcv.2 hg he2 hn hi hev hs
                hvoll' hob)
              (supports_drop (lst1B_sound rest k c.bindFresh Γ.length hk (Context.bindFresh_bounded hc)))
          · trivial
      · trivial
    · exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindOrigin_bounded hc e))
        (fun h c1 h1 => by
          simp only [Bool.and_eq_true] at h
          exact OB.narrow e lo' hi' voll rest h.1 (chkE_sound voll k c hk hc h.2) h1)
  | _, _, _, _, .check cond sonst rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_cond (fun _ => chkB_sound rest k c hk hc)
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.check cond sonst rest h.1 (chkE_sound sonst k c hk hc h.2) h1)
  | _, _, _, _, .float op a b lo hi rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindNone_bounded hc))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.float op a b lo hi rest h.1 h.2 h1)
  | _, _, _, _, .floatLit q lo hi rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_mono (fun x ⟨c1, h1, hx⟩ => hx ▸ OB.floatLit q lo hi rest h1)
      (supports_drop (chkB_sound rest k _ hk (Context.bindNone_bounded hc)))
  | _, _, _, _, .floatOf e lo hi rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindNone_bounded hc))
      (fun h c1 h1 => OB.floatOf e lo hi rest h h1)
  | _, _, _, _, .floatNarrow e lo hi sonst rest, k, c, hk, hc => by
    simp only [chkB]
    exact supports_condDrop (fun _ => chkB_sound rest k _ hk (Context.bindNone_bounded hc))
      (fun h c1 h1 => by
        simp only [Bool.and_eq_true] at h
        exact OB.floatNarrow e lo hi sonst rest h.1 (chkE_sound sonst k c hk hc h.2) h1)

theorem relB_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwK : V.gschreibt g = true)
      (hLK : gdarf D g Λ) (rest' : Block D V l Γ Λ Λ'), rest = .cons (.assignGlob g e2 hwK hLK) rest' ∧
      g = A.kopf ∧ exprVarPos e2 = some p ∧ OB A I out k c rest' x) (relB A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := chkB_sound rest1 k c hk hc
      cases s with
      | assignGlob g e2 hwK hLK =>
        simp only [relB]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
          exact ⟨g, e2, hwK, hLK, rest1, rfl, h.1, h.2, hx⟩)
      | _ => simp only [relB]; trivial
    | .nil => by simp only [relB]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [relB]; trivial

theorem ctr2B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwG : V.gschreibt g = true)
      (hLG : gdarf D g Λ) (rest' : Block D V l Γ Λ Λ'), rest = .cons (.assignGlob g e2 hwG hLG) rest' ∧
      g = A.zaehl ∧ exprSucc e2 = some p ∧ OB A I out k c rest' x) (ctr2B A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := chkB_sound rest1 k c hk hc
      cases s with
      | assignGlob g e2 hwG hLG =>
        simp only [ctr2B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
          exact ⟨g, e2, hwG, hLG, rest1, rfl, h.1, h.2, hx⟩)
      | _ => simp only [ctr2B]; trivial
    | .nil => by simp only [ctr2B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [ctr2B]; trivial

theorem ctr1B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (ev : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) (rest1 : Block D V l Γ Λ Λ'),
      rest = .cons (.assignSlot t f i ev hw hL) rest1 ∧ NotLink A t f ∧ checkExpression A c i = true ∧
      checkExpression A c ev = true ∧ storeCheck A c t i = true ∧
      ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwG : V.gschreibt g = true) (hLG : gdarf D g Λ)
        (rest2 : Block D V l Γ Λ Λ'), rest1 = .cons (.assignGlob g e2 hwG hLG) rest2 ∧
        g = A.zaehl ∧ exprSucc e2 = some p ∧ OB A I out k c rest2 x) (ctr1B A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := ctr2B_sound rest1 k c p hk hc
      cases s with
      | assignSlot t f i ev hw hL =>
        simp only [ctr1B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨t, f, i, ev, hw, hL, rest1, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2, hx⟩)
      | _ => simp only [ctr1B]; trivial
    | .nil => by simp only [ctr1B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [ctr1B]; trivial

theorem lst2B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context),
    k.bounded → c.bounded →
    Supports (fun x => ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (ev : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) (rest' : Block D V l Γ Λ Λ'),
      rest = .cons (.assignSlot t f i ev hw hL) rest' ∧ NotLink A t f ∧ checkExpression A c i = true ∧
      checkExpression A c ev = true ∧ storeCheck A c t i = true ∧ OB A I out k c rest' x) (lst2B A I fs out rest k c)
  | _, _, _, _, b, k, c, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := chkB_sound rest1 k c hk hc
      cases s with
      | assignSlot t f i ev hw hL =>
        simp only [lst2B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨t, f, i, ev, hw, hL, rest1, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2, hx⟩)
      | _ => simp only [lst2B]; trivial
    | .nil => by simp only [lst2B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [lst2B]; trivial

theorem lst1B_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (rest : Block D V l Γ Λ Λ') (k c : Context)
    (p : Nat), k.bounded → c.bounded →
    Supports (fun x => ∃ (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwK : V.gschreibt g = true)
      (hLK : gdarf D g Λ) (rest1 : Block D V l Γ Λ Λ'), rest = .cons (.assignGlob g e2 hwK hLK) rest1 ∧
      g = A.kopf ∧ exprSlotRead e2 = some ⟨A.tab, A.nxt, p⟩ ∧
      ∃ (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
        (ev : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) (rest2 : Block D V l Γ Λ Λ'),
        rest1 = .cons (.assignSlot t f i ev hw hL) rest2 ∧ NotLink A t f ∧ checkExpression A c i = true ∧
        checkExpression A c ev = true ∧ storeCheck A c t i = true ∧ OB A I out k c rest2 x)
      (lst1B A I fs out rest k c p)
  | _, _, _, _, b, k, c, p, hk, hc =>
    match b with
    | .cons s rest1 => by
      have ih := lst2B_sound rest1 k c hk hc
      cases s with
      | assignGlob g e2 hwK hLK =>
        simp only [lst1B]
        exact supports_cond (fun _ => ih) (fun h x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨g, e2, hwK, hLK, rest1, rfl, h.1, slotIsLink_sound h.2, hx⟩)
      | _ => simp only [lst1B]; trivial
    | .nil => by simp only [lst1B]; trivial
    | .bind .. | .bindCall .. | .bindCallInd .. | .bindCallElse .. | .bindAxiom .. | .bindAxiomElse ..
    | .regRead .. | .regReadElse .. | .awaits .. | .exchange .. | .narrow .. | .check .. | .float ..
    | .floatLit .. | .floatOf .. | .floatNarrow .. => by simp only [lst1B]; trivial

theorem chkE_sound : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (eb : Endblock D V l Γ Λ) (k c : Context),
    k.bounded → c.bounded → chkE A I fs out eb k c = true → OE A I out k c eb
  | _, _, _, .ret e hΛ, k, c, _, _, h => by
    simp only [chkE] at h; exact OE.ret e hΛ h
  | _, _, _, .retWhy r hΛ, k, c, _, _, h => by
    simp only [chkE] at h; exact OE.retWhy r hΛ h
  | _, _, _, .leave hl, k, c, hk, hc, h => by
    simp only [chkE] at h; exact OE.leave hl (exitsB_sound hk hc h)
  | _, _, _, .next hl, k, c, hk, hc, h => by
    simp only [chkE] at h; exact OE.next hl (exitsB_sound hk hc h)
  | _, _, _, .cons s rest, k, c, hk, hc, h => by
    have hs := chkS_sound s k c hk hc
    have ih := fun c1 hc1 => chkE_sound rest k c1 hk hc1
    simp only [chkE] at h
    generalize chkS A I fs out s k c = r at hs h
    match r, hs, h with
    | some (some c1), hs, h => exact OE.cons s rest hs.1 (ih c1 hs.2 h)
    | some none, hs, _ => exact OE.dead s rest hs
    | none, _, h => cases h
  | _, _, _, .bind e rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true] at h
    exact OE.bind e rest h.1 (chkE_sound rest k _ hk (Context.bindOrigin_bounded hc e) h.2)
  | _, _, _, .bindCall f args he hp hr rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true] at h
    exact OE.bindCall f args he hp hr rest h.1.1 h.1.2
      (chkE_sound rest k _ hk (resultContext_bounded (afterCall_bounded hc) _) h.2)
  | _, _, _, .bindCallElse f args he hp hr err rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true] at h
    exact OE.bindCallElse f args he hp hr err rest h.1.1.1 h.1.1.2
      (chkE_sound err k _ hk (Context.bindNone_bounded (afterCall_bounded hc)) h.1.2)
      (chkE_sound rest k _ hk (resultContext_bounded (afterCall_bounded hc) _) h.2)
  | _, _, _, .bindAxiom a args he hw hg hd hgd rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true, decide_eq_true_eq] at h
    exact OE.bindAxiom a args he hw hg hd hgd rest h.1.1 h.1.2
      (chkE_sound rest k _ hk (Context.bindNone_bounded hc) h.2)
  | _, _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true, decide_eq_true_eq] at h
    exact OE.bindAxiomElse a args he hr hw hg hd hgd err rest h.1.1.1 h.1.1.2
      (chkE_sound err k _ hk (Context.bindNone_bounded hc) h.1.2)
      (chkE_sound rest k _ hk (Context.bindNone_bounded hc) h.2)
  | _, _, _, .regRead r hk' rest, k, c, hk, hc, h => by
    simp only [chkE] at h
    exact OE.regRead r hk' rest (chkE_sound rest k _ hk (Context.bindNone_bounded hc) h)
  | _, _, _, .regReadElse r hk' zusage sonst rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true] at h
    exact OE.regReadElse r hk' zusage sonst rest h.1.1 (chkE_sound sonst k c hk hc h.1.2)
      (chkE_sound rest k _ hk (Context.bindNone_bounded hc) h.2)
  | _, _, _, .awaits g payload hp hL ha rest, k, c, hk, hc, h => by
    simp only [chkE] at h
    exact OE.awaits g payload hp hL ha rest (chkE_sound rest k _ hk (Context.bindNone_bounded hc) h)
  | _, _, _, .bindCallInd p args he hp hr rest, k, c, hk, hc, h => by
    simp only [chkE, Bool.and_eq_true] at h
    exact OE.bindCallInd p args he hp hr rest _ _ (sigCompatB_sound hvoll h.1.1.2) h.1.1.1.1 h.1.1.1.2 h.1.2
      (chkE_sound rest k _ hk (resultContextB_bounded (afterCall_bounded hc) _) h.2)

theorem chkArms_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (k c : Context),
    k.bounded → c.bounded → Supports (OArms A I out k c arms) (chkArms A I fs out arms k c)
  | _, _, _, _, _, .nil, k, c, _, _ => by
    simp only [chkArms]
    exact fun x _ => OArms.nil
  | _, _, _, _, ca :: _, .cons b rest, k, c, hk, hc => by
    simp only [chkArms]
    exact supports_join
      (supports_map (fun c1 => armDrop c1 ca) (fun x => armBind x ca)
        (fun x => by cases ca <;> simp [armDrop, armBind, Context.bind_drop])
        (fun x hx => armBind_bounded hx ca) (fun x hx => armDrop_bounded hx ca)
        (chkB_sound b k (armBind c ca) hk (armBind_bounded hc ca)))
      (chkArms_sound rest k c hk hc)
      (fun x y z hx hy wx wy => by
        obtain ⟨c1, hb1, rfl⟩ := hx
        exact OArms.cons b rest hb1 wx (OArms.weaken hy wy))

theorem chkGrund_sound : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (k c : Context),
    k.bounded → c.bounded → Supports (OGrund A I out k c arms) (chkGrund A I fs out arms k c)
  | _, _, _, _, _, .nil, k, c, _, _ => by
    simp only [chkGrund]
    exact fun x _ => OGrund.nil
  | _, _, _, _, _, .cons b rest, k, c, hk, hc => by
    simp only [chkGrund]
    exact supports_join (chkB_sound b k c hk hc) (chkGrund_sound rest k c hk hc)
      (fun x y z hx hy wx wy => OGrund.cons b rest hx wx (OGrund.weaken hy wy))

end

end Sound

end Gabbro.Grammatik.ArenaOwnership.Body
