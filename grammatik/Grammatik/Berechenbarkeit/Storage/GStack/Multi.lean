import Grammatik.Berechenbarkeit.Storage.GStack.Push

/-! Several G stacks in ONE arena: one head per stack, one shared link field, pairwise disjoint chains of live
cells. This is the storage a TM2 machine with several stacks needs (`Turing.TM2`, one stack per index). The theorems
say that an actual G push on one stack gives exactly the new value sequence there and leaves every other stack
exactly as it was: the allocated cell was dead, so it lies on no chain, and the link store touches that cell and
the pushed stack's head only. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open ArenaKette

variable {D : Deklaration} {A : FreiForm D}

/-- **Several stacks in one arena**: per stack index `k` a chain of distinct live cells from the head `G k` whose
payloads are `vals k`, and no cell on two chains. -/
def MultiRep {K : Type} (L : LinkFeld A) (G : K → LinkKopf A) (σ : World D)
    (vals : K → List (Wert D (D.typ A.tab A.feld))) : Prop :=
  ∃ ix : K → List Int,
    (∀ k, KetteF (D.count A.tab) (L.wert σ) ((G k).st σ) (ix k) ∧ (ix k).Nodup ∧ (∀ i ∈ ix k, A.Lebt σ i) ∧
      (ix k).map (fun i => σ.slots A.tab i A.feld) = vals k) ∧
    ∀ k k', k ≠ k' → ∀ i ∈ ix k, i ∉ ix k'

/-- Each stack of a multi-stack arena is a represented stack. -/
theorem MultiRep.stapel {K : Type} {L : LinkFeld A} {G : K → LinkKopf A} {σ : World D} {vals}
    (h : MultiRep L G σ vals) (k : K) : Represents L (G k) σ (vals k) := by
  obtain ⟨ix, hk, _⟩ := h
  obtain ⟨hc, hn, hl, hv⟩ := hk k
  exact ⟨ix k, hc, hn, hl, hv⟩

/-- No stacks hold no cells: every arena with empty heads represents empty stacks. -/
theorem multiRep_leer {K : Type} (L : LinkFeld A) (G : K → LinkKopf A) (σ : World D)
    (hh : ∀ k, (G k).st σ = D.count A.tab) : MultiRep L G σ (fun _ => []) :=
  ⟨fun _ => [], fun k => ⟨hh k ▸ KetteF.nil, .nil, by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true], rfl⟩, by simp only [ne_eq, List.not_mem_nil, not_false_eq_true, implies_true]⟩

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- **A G push on one of several stacks.** The executed allocation and link stores put `value` on stack `k`
and leave every other stack's value sequence unchanged; the free list stays safe. Uniform in the continuation. -/
theorem push_multi {K : Type} [DecidableEq K] (allocator : Allocator A V l Γ Λ) (L : LinkFeld A)
    (G : K → LinkKopf A) (hinj : Function.Injective fun k => (G k).g) (k : K)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ) (σ : World D) (ρ : Env D Γ)
    (value : Wert D (D.typ A.tab A.feld)) (vals : K → List (Wert D (D.typ A.tab A.feld))) (slot : Int)
    (hm : MultiRep L G σ vals) (ha : Allocated O passes R A allocator σ ρ value slot) :
    ∃ σ' kk,
      (∀ {Λ'} (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.pushAllocated allocator L (G k) hwT hLT hwH hLH rest) σ ρ =
          (execBlock O passes R rest σ' (.cons kk ρ)).schrumpf) ∧
      kk.n = slot ∧ MultiRep L G σ' (Function.update vals k (value :: vals k)) ∧ A.FreiOk σ' := by
  obtain ⟨σ1, kk, halloc, hkn, hframe, hf, hlive, hold, hbytes⟩ := ha
  obtain ⟨ix, hix, hdis⟩ := hm
  -- the link step, uniform in the continuation, and its frame
  obtain ⟨σ2, hexec2, hbytes2⟩ :=
    linkPush_prefix O passes R (l := l) L (G k) .here hwT hLT hwH hLH σ1 (.cons kk ρ)
  obtain ⟨σ2', he', hrahmen, hhead, hlinkx, hother, hfree, hnext, hcount⟩ :=
    linkPush_ausfuehren O passes R (l := l) L (G k) .here hwT hLT hwH hLH (.nil) σ1 (.cons kk ρ)
  have hw : σ2' = σ2 := by
    have hp := hexec2 (.nil)
    rw [he'] at hp
    change (Ausgang.ok σ2' (.cons kk ρ) : Ausgang V l _) = .ok σ2 (.cons kk ρ) at hp
    cases hp; rfl
  subst σ2'
  simp only [Env.get_cons_here, hkn] at hhead hlinkx hother
  have hsame := A.lebt_gleich hfree hnext hcount
  -- the allocated cell was dead, so it lies on no chain
  have hfresh : ∀ j, slot ∉ ix j := fun j hm => hold ((hix j).2.2.1 slot hm)
  -- the chains after the allocation (the allocator writes no link and no head of a stack)
  have hix1 : ∀ j, KetteF (D.count A.tab) (L.wert σ1) ((G j).st σ1) (ix j) := fun j => by
    rw [L.wert_fremd' hframe, (G j).st_fremd hframe]; exact (hix j).1
  have hslot : slot < D.count A.tab := by
    have hl := (hlive slot).mpr (.inl rfl)
    have := hl.2.1
    have := A.stand_le σ1
    omega
  have hslot0 : 0 ≤ slot := ((hlive slot).mpr (.inl rfl)).1
  refine ⟨σ2, kk, ?_, hkn, ⟨Function.update ix k (slot :: ix k), fun j => ?_, ?_⟩, ?_⟩
  · intro Λ' rest
    unfold Block.pushAllocated
    rw [halloc, hexec2]
  · by_cases hj : j = k
    · subst hj
      simp only [Function.update_self]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hhead]
        refine KetteF.cons slot hslot0 hslot (ix j) ?_
        rw [hlinkx]
        exact (hix1 j).uebertragen (fun i hi => hother i (fun he => hfresh j (he ▸ hi)))
      · exact List.nodup_cons.2 ⟨hfresh j, (hix j).2.1⟩
      · intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact (hsame i).mpr ((hlive i).mpr (.inl rfl))
        · exact (hsame i).mpr ((hlive i).mpr (.inr ((hix j).2.2.1 i hi)))
      · simp only [List.map_cons, hbytes2, hbytes]
        rw [← (hix j).2.2.2]
        apply congrArg
        apply List.map_congr_left
        intro i hi
        have hne : i ≠ slot := fun he => hfresh j (he ▸ hi)
        simp only [hne, ↓reduceIte]
    · simp only [Function.update_of_ne hj]
      have hg : (G j).g ∉ [(G k).g] := by
        simp only [List.mem_singleton]
        exact fun he => hj (hinj he)
      refine ⟨?_, (hix j).2.1, ?_, ?_⟩
      · rw [hrahmen.kopf (G j) hg]
        exact (hix1 j).uebertragen (fun i hi => hother i (fun he => hfresh j (he ▸ hi)))
      · intro i hi
        exact (hsame i).mpr ((hlive i).mpr (.inr ((hix j).2.2.1 i hi)))
      · rw [← (hix j).2.2.2]
        apply List.map_congr_left
        intro i hi
        have hne : i ≠ slot := fun he => hfresh j (he ▸ hi)
        simp only [hbytes2, hbytes, hne, ↓reduceIte]
  · intro a b hab i hi hi'
    by_cases ha : a = k
    · subst ha
      rw [Function.update_of_ne (Ne.symm hab)] at hi'
      simp only [Function.update_self] at hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact hfresh b hi'
      · exact hdis a b hab i hi hi'
    · rw [Function.update_of_ne ha] at hi
      by_cases hb : b = k
      · subst hb
        simp only [Function.update_self] at hi'
        rcases List.mem_cons.1 hi' with rfl | hi'
        · exact hfresh a hi
        · exact hdis a b hab i hi hi'
      · rw [Function.update_of_ne hb] at hi'
        exact hdis a b hab i hi hi'
  · exact A.freiOk_gleich hfree hnext hcount hf

/-- **A G pop on one of several stacks.** The executed unlink, payload read and release take `value` off stack
`k` and hand it to the continuation, leave every other stack's value sequence unchanged, and keep the free list
safe. -/
theorem pop_multi {K : Type} [DecidableEq K] (L : LinkFeld A) (G : K → LinkKopf A)
    (hinj : Function.Injective fun k => (G k).g) (k : K)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (empty : Endblock D V l Γ Λ)
    {Λ'} (rest : Gabbro.Grammatik.Block D V l (D.typ A.tab A.feld :: Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (value : Wert D (D.typ A.tab A.feld))
    (tl : List (Wert D (D.typ A.tab A.feld))) (vals : K → List (Wert D (D.typ A.tab A.feld)))
    (hk : vals k = value :: tl) (hm : MultiRep L G σ vals) (hf : A.FreiOk σ) :
    ∃ σ' kk,
      execBlock O passes R (Block.popAndRelease L (G k) hwH hLH hwT hLT hwF hLF empty rest) σ ρ =
        ((execBlock O passes R rest σ' (.cons value (.cons kk ρ))).schrumpf).schrumpf ∧
      MultiRep L G σ' (Function.update vals k tl) ∧ A.FreiOk σ' := by
  obtain ⟨ix, hix, hdis⟩ := hm
  obtain ⟨hc, hnd, hlv, hvals⟩ := hix k
  rw [hk] at hvals
  generalize hixk : ix k = xs at hc hnd hlv hvals
  generalize hroot : (G k).st σ = root at hc
  cases hc with
  | nil => simp only [List.map_nil, List.nil_eq, reduceCtorEq] at hvals
  | cons _ h0 hi0 tail ht =>
    have hv := List.cons.inj (by simpa only [List.map_cons] using hvals)
    have hne : (G k).st σ < D.count A.tab := hroot ▸ hi0
    -- the unlink
    obtain ⟨σ1, kk, hexec1, hkn, hslots1⟩ := linkPop_prefix O passes R L (G k) hwH hLH hLT empty σ ρ hne
    obtain ⟨σm, km, hm1, hrahmen, _, hhead, hlinks, hkopf, hnext, hcount⟩ :=
      linkPop_ausfuehren O passes R L (G k) hwH hLH hLT empty (.nil) σ ρ hne
    have hw1 : σm = σ1 := by
      have h := hexec1 (.nil)
      rw [hm1] at h
      change (Ausgang.ok σm ρ : Ausgang V l Γ) = .ok σ1 ρ at h
      cases h; rfl
    subst σm
    have hkn0 : kk.n = root := hkn.trans hroot
    have hsame1 := A.lebt_gleich hkopf hnext hcount
    have hfree1 := A.freiOk_gleich hkopf hnext hcount hf
    -- the payload read records an access and changes nothing else
    let σ2 := σ1.lese Λ [Sum.inl A.tab]
    have hsame2 : ∀ i, A.Lebt σ2 i ↔ A.Lebt σ1 i := A.lebt_gleich (σ := σ1) (σ' := σ2) rfl (fun _ => rfl) rfl
    have hfree2 : A.FreiOk σ2 := A.freiOk_gleich (σ := σ1) (σ' := σ2) rfl (fun _ => rfl) rfl hfree1
    have hi0live : A.Lebt σ root := hlv root (List.mem_cons_self ..)
    have hlive2 : A.Lebt σ2 kk.n := (hsame2 _).mpr ((hsame1 _).mpr (hkn0 ▸ hi0live))
    -- the release
    obtain ⟨σ3, hexec3, hbytes3⟩ := free_prefix O passes R (l := l) A (.there .here) hwT hLT hwF hLF σ2
      (.cons value (.cons kk ρ))
    obtain ⟨σn, hn3, hkopf3, hnew3, hother3, hcount3, hframe3⟩ := freiVar_ausfuehren O passes R (l := l) A
      (.there .here) hwT hLT hwF hLF (.nil) σ2 (.cons value (.cons kk ρ))
    have hw3 : σn = σ3 := by
      have h := hexec3 (.nil)
      rw [hn3] at h
      change (Ausgang.ok σn _ : Ausgang V l _) = .ok σ3 _ at h
      cases h; rfl
    subst σn
    simp only [Env.get_cons_there, Env.get_cons_here] at hkopf3 hnew3 hother3
    have hfree3 := (A.lebt_frei kk.n hlive2 hfree2 hkopf3 hnew3 hother3 hcount3).1
    have hlive3 := A.release_live_iff kk.n hlive2 hfree2 hkopf3 hnew3 hother3 hcount3
    -- every view of every stack through the three steps
    have hwert : L.wert σ3 = L.wert σ := by
      rw [L.wert_fremd' hframe3]
      exact funext hlinks
    have hst : ∀ j, (G j).st σ3 = (G j).st σ1 := fun j => (G j).st_fremd hframe3
    have hpay : ∀ i, σ3.slots A.tab i A.feld = σ.slots A.tab i A.feld := fun i => by
      rw [hbytes3]
      exact congrFun (congrFun (congrFun hslots1 A.tab) i) A.feld
    have hn0 := List.nodup_cons.mp hnd
    refine ⟨σ3, kk, ?_, ⟨Function.update ix k tail, fun j => ?_, ?_⟩, hfree3⟩
    · unfold Block.popAndRelease
      rw [hexec1]
      have heval : eval σ2 (Expr.slot A.tab A.feld (Expr.var .here) hLT) σ2 (.cons kk ρ) = value := by
        change σ1.slots A.tab kk.n A.feld = value
        rw [hslots1, hkn0]
        exact hv.1
      change ((execBlock O passes R
        (Gabbro.Grammatik.Block.freiVar A (.there .here) hwT hLT hwF hLF rest)
        σ2 (.cons (eval σ2 (Expr.slot A.tab A.feld (Expr.var .here) hLT) σ2 (.cons kk ρ)) (.cons kk ρ))).schrumpf).schrumpf = _
      rw [heval, hexec3]
    · by_cases hj : j = k
      · subst hj
        simp only [Function.update_self]
        refine ⟨?_, hn0.2, ?_, ?_⟩
        · rw [hwert, hst, hhead, hroot]
          exact ht
        · intro i hi
          exact (hlive3 i).mpr ⟨(hsame2 i).mpr ((hsame1 i).mpr (hlv i (List.mem_cons_of_mem _ hi))),
            fun he => hn0.1 (hkn0 ▸ he ▸ hi)⟩
        · rw [← hv.2]
          exact List.map_congr_left (fun i _ => hpay i)
      · simp only [Function.update_of_ne hj]
        obtain ⟨hcj, hnj, hlj, hvj⟩ := hix j
        have hg : (G j).g ∉ [(G k).g] := by
          simp only [List.mem_singleton]
          exact fun he => hj (hinj he)
        refine ⟨?_, hnj, ?_, ?_⟩
        · rw [hwert, hst, hrahmen.kopf (G j) hg]
          exact hcj
        · intro i hi
          refine (hlive3 i).mpr ⟨(hsame2 i).mpr ((hsame1 i).mpr (hlj i hi)), fun he => ?_⟩
          exact hdis k j (Ne.symm hj) root (hixk ▸ List.mem_cons_self ..) (hkn0 ▸ he ▸ hi)
        · rw [← hvj]
          exact List.map_congr_left (fun i _ => hpay i)
    · intro a b hab i hi hi'
      have sub : ∀ c, ∀ x ∈ Function.update ix k tail c, x ∈ ix c := fun c x hx => by
        by_cases hc : c = k
        · subst hc
          simp only [Function.update_self] at hx
          exact hixk ▸ List.mem_cons_of_mem _ hx
        · rwa [Function.update_of_ne hc] at hx
      exact hdis a b hab i (sub a i hi) (sub b i hi')

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
