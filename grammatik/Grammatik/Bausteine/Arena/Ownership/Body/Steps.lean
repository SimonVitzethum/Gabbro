import Grammatik.Bausteine.Arena.Ownership.Body.Judgment

/-! The steps the soundness proof of the body judgment is assembled from:
outcomes through scope exits and world maps, assignment, returns, the three
loop runners of G and the case arms. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. Environments -/

theorem Env.set_get_same : ∀ {Γ : Ctx} {τ υ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (y : Var Γ υ) (v : Wert D τ),
    y.unten = x.unten → intVon υ ((ρ.set x v).get y) = intVon τ v
  | _, _, _, .cons _ _, .here, .here, _, _ => rfl
  | _, _, _, .cons _ _, .here, .there y, _, h => by
    have := Var.unten_lt y; simp only [Var.unten] at h; omega
  | _, _, _, .cons _ _, .there x, .here, _, h => by
    have := Var.unten_lt x; simp only [Var.unten] at h; omega
  | _, _, _, .cons _ ρ, .there x, .there y, v, h => Env.set_get_same ρ x y v h

theorem Env.set_get_other : ∀ {Γ : Ctx} {τ υ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (y : Var Γ υ) (v : Wert D τ),
    y.unten ≠ x.unten → (ρ.set x v).get y = ρ.get y
  | _, _, _, .cons _ _, .here, .here, _, h => absurd rfl h
  | _, _, _, .cons _ _, .here, .there _, _, _ => rfl
  | _, _, _, .cons _ _, .there _, .here, _, _ => rfl
  | _, _, _, .cons _ ρ, .there x, .there y, v, h => Env.set_get_other ρ x y v h

section Holds

variable {A : FreiForm D} {fr : Frame} {s0 : State}

/-- **Assignment re-binds provenance.** The assigned name takes the origin
of the new value; every other name keeps its own. -/
theorem Holds.assign {c : Context} {σ : World D} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (x : Var Γ τ) (e : Expr D Γ Λ τ) (σa σb : World D) :
    Holds A fr s0 (c.assign x (origin c e)) σ (ρ.set x (eval σa e σb ρ)) := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hr⟩, hc, hl, hp⟩ := h
  have hx : x.unten < c.references.length := by rw [href.1]; exact Var.unten_lt x
  refine ⟨g, s, ⟨ha, hf, ⟨hb.1, ?_⟩, ⟨by simp only [Context.assign, List.length_set, href.1], ?_⟩, hr⟩, hc, hl, hp⟩
  · intro ref hm i he
    rcases List.mem_or_eq_of_mem_set hm with hm | hm
    · exact hb.2 ref hm i he
    · subst hm
      exact hb.2 (some i) (origin_member c e i he) i rfl
  · intro υ y i hi
    unfold Context.reference Context.assign at hi
    by_cases hyx : y.unten = x.unten
    · rw [hyx, List.getElem?_set_self hx] at hi
      simp only [Option.getD_some] at hi
      obtain ⟨h, hg, hv⟩ := origin_sound c g ρ href e i hi σa σb
      exact ⟨h, hg, (Env.set_get_same ρ x y _ hyx).trans hv⟩
    · rw [List.getElem?_set_ne (Ne.symm hyx)] at hi
      rw [Env.set_get_other ρ x y _ hyx]
      exact href.2 y i hi

/-- A narrowed integer keeps the integer, hence its origin. -/
theorem Holds.bindNarrow {c : Context} {σ : World D} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (e : Expr D Γ Λ (.int lo hi)) (σa σb : World D) (lo' hi' : Int)
    (hn : lo' ≤ (eval σa e σb ρ).n ∧ (eval σa e σb ρ).n ≤ hi') :
    Holds A fr s0 (c.bind (origin c e)) σ
      (.cons (τ := .int lo' hi') ⟨(eval σa e σb ρ).n, hn.1, hn.2⟩ ρ) := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hr⟩, hc, hl, hp⟩ := h
  refine ⟨g, s, ⟨ha, hf, ?_, ?_, hr⟩, Complete.bind hc _, hl, hp⟩
  · apply Context.bind_bounded hb
    intro i hi
    exact hb.2 (some i) (origin_member c e i hi) i rfl
  · apply References.bind href _ (origin c e)
    intro i hi
    obtain ⟨h, hg, hv⟩ := origin_sound c g ρ href e i hi σa σb
    exact ⟨h, hg, hv⟩

end Holds

/-! ## 2. Outcomes -/

section Post

variable {A : FreiForm D} {fr : Frame} {s0 : State} {V : Vertrag D} {out : Flow.Output A V.erg}

theorem DoneValue.meta {σ σ' : World D} {v : ErgVal D V.erg} (h : DoneValue A fr s0 out σ v)
    (hm : MetaSame A σ σ') : DoneValue A fr s0 out σ' v := by
  obtain ⟨s, ha, hf, hl, hp, hr⟩ := h
  exact ⟨s, State.agrees_meta ha hm, freiOk_meta hf hm, hl, hp, hr⟩

theorem DoneReason.meta {σ σ' : World D} (h : DoneReason A fr s0 σ) (hm : MetaSame A σ σ') :
    DoneReason A fr s0 σ' := by
  obtain ⟨s, ha, hf, hl, hp, hr⟩ := h
  exact ⟨s, State.agrees_meta ha hm, freiOk_meta hf hm, hl, hp, hr⟩

theorem Holds.length {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ) :
    c.references.length = Γ.length := by
  obtain ⟨_, _, ⟨_, _, _, href, _⟩, _⟩ := h
  exact href.1

theorem BPost.schrumpf {k c' : Context} {l : Bool} {Γ : Ctx} {τ : Ty}
    (hk : k.references.length ≤ Γ.length) (o : Ausgang V l (τ :: Γ))
    (h : BPost A fr s0 out k c' o) : BPost A fr s0 out k c'.drop o.schrumpf := by
  cases o with
  | ok σ ρ => cases ρ; exact Holds.drop h
  | leave hl σ ρ =>
    cases ρ
    obtain ⟨c, hx, hc⟩ := h
    have := hc.length
    exact ⟨c.drop, hx.drop (by simp only [List.length_cons] at this; omega), Holds.drop hc⟩
  | next hl σ ρ =>
    cases ρ
    obtain ⟨c, hx, hc⟩ := h
    have := hc.length
    exact ⟨c.drop, hx.drop (by simp only [List.length_cons] at this; omega), Holds.drop hc⟩
  | _ => exact h

theorem EPost.schrumpf {k : Context} {l : Bool} {Γ : Ctx} {τ : Ty}
    (hk : k.references.length ≤ Γ.length) (o : EndAusgang V l (τ :: Γ))
    (h : EPost A fr s0 out k o) : EPost A fr s0 out k o.schrumpf := by
  cases o with
  | leave hl σ ρ =>
    cases ρ
    obtain ⟨c, hx, hc⟩ := h
    have := hc.length
    exact ⟨c.drop, hx.drop (by simp only [List.length_cons] at this; omega), Holds.drop hc⟩
  | next hl σ ρ =>
    cases ρ
    obtain ⟨c, hx, hc⟩ := h
    have := hc.length
    exact ⟨c.drop, hx.drop (by simp only [List.length_cons] at this; omega), Holds.drop hc⟩
  | _ => exact h

theorem EPost.toB {k c' : Context} {l : Bool} {Γ : Ctx} (o : EndAusgang V l Γ)
    (h : EPost A fr s0 out k o) : BPost A fr s0 out k c' o.zuAusgang := by
  cases o <;> exact h

theorem BPost.weaken {k c1 c2 : Context} {l : Bool} {Γ : Ctx} (o : Ausgang V l Γ)
    (hw : Weaker c2 c1) (h : BPost A fr s0 out k c1 o) : BPost A fr s0 out k c2 o := by
  cases o with
  | ok σ ρ => exact Holds.weaken h hw
  | _ => exact h

theorem BPost.mapMeta {k c' : Context} {l : Bool} {Γ : Ctx} (o : Ausgang V l Γ) (F : World D → World D)
    (hF : ∀ σ, MetaSame A σ (F σ)) (h : BPost A fr s0 out k c' o) : BPost A fr s0 out k c' (o.mapWelt F) := by
  cases o with
  | ok σ ρ => exact Holds.meta h (hF σ)
  | zurueck σ v => exact DoneValue.meta h (hF σ)
  | why σ r => exact DoneReason.meta h (hF σ)
  | leave hl σ ρ => obtain ⟨c, hx, hc⟩ := h; exact ⟨c, hx, Holds.meta hc (hF σ)⟩
  | next hl σ ρ => obtain ⟨c, hx, hc⟩ := h; exact ⟨c, hx, Holds.meta hc (hF σ)⟩
  | logik e => trivial
  | hardware e => trivial

/-- **A checked return meets the interface postcondition.** -/
theorem Holds.doneValue {c : Context} {σ : World D} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (e : ErgExpr D Γ Λ V.erg) (he : out.check A c e = true) (σa σb : World D) :
    DoneValue A fr s0 out σ (evalErg σa e σb ρ) := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hr⟩, hc, hl, hp⟩ := h
  exact ⟨s, ha, hf, hl, hp, Flow.Output.check_sound A c g fr s out e σa σb ρ hb href hr hc he⟩

/-- **A checked reason return leaves nothing owned.** -/
theorem Holds.doneReason {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
    (h : Holds A fr s0 c σ ρ) (hf : finish c none = true) : DoneReason A fr s0 σ := by
  obtain ⟨g, s, ⟨ha, hfr, hb, _, _⟩, hc, hl, hp⟩ := h
  exact ⟨s, ha, hfr, hl, hp, finish_void hb hc hf⟩

/-! ## 3. Loops -/

/-- The body of a loop, judged from the loop context `kk` back into `kk`. -/
def LoopBody (A : FreiForm D) (fr : Frame) (s0 : State) (out : Flow.Output A V.erg) (kk : Context) {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ) : Prop :=
  ∀ σ ρ, Holds A fr s0 kk σ ρ → BPost A fr s0 out kk kk (schritt σ ρ)

theorem BPost.loopHead {kk : Context} {Γ : Ctx} {σ : World D} {ρ : Env D Γ}
    (h : ∃ c, ExitsTo kk c ∧ Holds A fr s0 c σ ρ) (hlen : kk.references.length = Γ.length) :
    Holds A fr s0 kk σ ρ := by
  obtain ⟨c, hx, hc⟩ := h
  exact hc.weaken (hx.weaker (hc.length.trans hlen.symm))

/-- `forever`: every pass starts in the loop context. -/
theorem forever_post {k kk : Context} {l : Bool} {Γ : Ctx} (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ) (inv : World D → Env D Γ → World D × Bool)
    (hinv : ∀ σ ρ, MetaSame A σ (inv σ ρ).1) (hb : LoopBody A fr s0 out kk schritt)
    (hlen : kk.references.length = Γ.length) :
    ∀ n σ ρ, Holds A fr s0 kk σ ρ → BPost A fr s0 out k kk (foreverLauf (l := l) a schritt inv n σ ρ)
  | 0, _, _, _ => trivial
  | n + 1, σ, ρ, h => by
    simp only [foreverLauf]
    split
    · trivial
    · have hs := hb _ ρ (h.meta (hinv σ ρ))
      generalize schritt (inv σ ρ).1 ρ = o at hs
      cases o with
      | ok σ' ρ' => exact forever_post a schritt inv hinv hb hlen n σ' ρ' hs
      | next _ σ' ρ' => exact forever_post a schritt inv hinv hb hlen n σ' ρ' (BPost.loopHead hs hlen)
      | leave _ σ' ρ' => exact BPost.loopHead hs hlen
      | zurueck σ' v => exact hs
      | why σ' r => exact hs
      | logik e => trivial
      | hardware e => trivial

/-- `retry`: every attempt starts in the loop context; the overflow branch
falls off in it too. -/
theorem retry_post {k kk : Context} {l : Bool} {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ) (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hbis : ∀ σ ρ, MetaSame A σ (bis σ ρ).1) (hb : LoopBody A fr s0 out kk schritt)
    (hu : ∀ σ ρ, Holds A fr s0 kk σ ρ → BPost A fr s0 out k kk (ueberlauf σ ρ))
    (hlen : kk.references.length = Γ.length) :
    ∀ n σ ρ, Holds A fr s0 kk σ ρ → BPost A fr s0 out k kk (retryLauf schritt bis ueberlauf n σ ρ)
  | 0, σ, ρ, h => by
    simp only [retryLauf]
    split
    · exact h.meta (hbis σ ρ)
    · exact hu _ ρ (h.meta (hbis σ ρ))
  | n + 1, σ, ρ, h => by
    simp only [retryLauf]
    split
    · exact h.meta (hbis σ ρ)
    · have hs := hb _ ρ (h.meta (hbis σ ρ))
      generalize schritt (bis σ ρ).1 ρ = o at hs
      cases o with
      | ok σ' ρ' => exact retry_post schritt bis ueberlauf hbis hb hu hlen n σ' ρ' hs
      | next _ σ' ρ' => exact retry_post schritt bis ueberlauf hbis hb hu hlen n σ' ρ' (BPost.loopHead hs hlen)
      | leave _ σ' ρ' => exact BPost.loopHead hs hlen
      | zurueck σ' v => exact hs
      | why σ' r => exact hs
      | logik e => trivial
      | hardware e => trivial

/-- `traverse`: every pass binds the next index without provenance. -/
theorem traverse_post {k kk c1 : Context} {l : Bool} {Γ : Ctx} {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ)) (inv : World D → Env D Γ → World D × Bool)
    (hinv : ∀ σ ρ, MetaSame A σ (inv σ ρ).1)
    (hb : ∀ σ ρ, Holds A fr s0 (kk.bind none) σ ρ → BPost A fr s0 out kk c1 (schritt σ ρ))
    (hback : Weaker kk c1.drop) (hlen : kk.references.length = Γ.length) :
    ∀ (ks : List (Wert D τ)) σ ρ, Holds A fr s0 kk σ ρ →
      BPost A fr s0 out k kk (traverseLauf (l := l) schritt inv ks σ ρ)
  | [], σ, ρ, h => by
    simp only [traverseLauf]
    split
    · exact h.meta (hinv σ ρ)
    · trivial
  | x :: ks, σ, ρ, h => by
    simp only [traverseLauf]
    split
    · trivial
    · have hs := hb _ _ ((h.meta (hinv σ ρ)).bindNone x)
      generalize schritt (inv σ ρ).1 (.cons x ρ) = o at hs
      cases o with
      | ok σ' ρ' =>
        cases ρ'
        exact traverse_post schritt inv hinv hb hback hlen ks σ' _ ((Holds.drop hs).weaken hback)
      | next _ σ' ρ' =>
        cases ρ'
        obtain ⟨c, hx, hc⟩ := hs
        have hl := hc.length
        have hd : ∃ c, ExitsTo kk c ∧ Holds A fr s0 c σ' _ :=
          ⟨c.drop, hx.drop (by simp only [List.length_cons] at hl; omega), Holds.drop hc⟩
        exact traverse_post schritt inv hinv hb hback hlen ks σ' _ (BPost.loopHead hd hlen)
      | leave _ σ' ρ' =>
        cases ρ'
        obtain ⟨c, hx, hc⟩ := hs
        have hl := hc.length
        have hd : Holds A fr s0 kk σ' _ :=
          BPost.loopHead ⟨c.drop, hx.drop (by simp only [List.length_cons] at hl; omega), Holds.drop hc⟩ hlen
        simp only [Env.tail]
        split
        · exact hd.meta (hinv _ _)
        · trivial
      | zurueck σ' v => exact hs
      | why σ' r => exact hs
      | logik e => trivial
      | hardware e => trivial

end Post

#print axioms Holds.assign
#print axioms forever_post
#print axioms traverse_post

end Gabbro.Grammatik.ArenaOwnership.Body
