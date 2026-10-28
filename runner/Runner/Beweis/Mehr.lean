import Runner.Beweis.Schritt
import Runner.Mach.Maschine

/-! # `runner_mt`: every run of the runner's threads is a run of the IR's threads

Both processes run on the same machine (`Runner/Mach/Maschine.lean`) over the same memory model `M`: the IR
threads with their request trees (`actI`), the x86 threads with the model's step over the runner's code
(`actX`). `Rel` relates two processes: the same memory, the same threads, each IR thread's rest of an instruction
matched by its x86 thread (`Match`).

`runner_mt`: for every memory model that answers a read of the dispatch table with the table's word (`Fixed`, the
runner's table is never written and the kernel keeps it), every observation of the x86 process -- its system
calls, with their answers, from all threads, in order, and how it ends -- is an observation of the IR process,
and the x86 process never reaches a step the model does not describe. No assumption on the program: also a
program with data races, and under every memory model, sequentially consistent or with store buffers. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog Runner.Mach

def actI : Res IR.T → Res (Res IR.T)
  | .next t => .next (IR.step t)
  | .fault => .fault
  | .unk => .unk
  | .ask o k => .ask o fun a => .next (k a)

def actX (L : Lay) (x : X) : Res X := step L.C x

def Fixed (M : MemSys) (L : Lay) : Prop :=
  ∀ ms i op a ms', op < 256 → M.ans ms i (.rd 8 (taddr L (BitVec.ofNat 64 op))) a ms' →
    ms' = ms ∧ ∃ w, a = some (L.H op, w)

def RelT (L : Lay) : Option (Option (Res IR.T)) → Option (Option X) → Prop
  | none, none => True
  | some none, some none => True
  | some (some r), some (some x) => Match L r x
  | _, _ => False

structure Rel (L : Lay) {M : MemSys} (cI : Cfg M (Res IR.T)) (cX : Cfg M X) : Prop where
  ms : cI.ms = cX.ms
  th : ∀ j : Nat, RelT L cI.ths[j]? cX.ths[j]?

/-! ## The thread lists -/

theorem relT_len {L : Lay} {lI : List (Option (Res IR.T))} {lX : List (Option X)}
    (h : ∀ j : Nat, RelT L lI[j]? lX[j]?) : lI.length = lX.length := by
  rcases Nat.lt_trichotomy lI.length lX.length with hl | hl | hl
  · have := h lI.length
    rw [List.getElem?_eq_none (Nat.le_refl _), List.getElem?_eq_getElem hl] at this
    cases lX[lI.length] <;> simp [RelT] at this
  · exact hl
  · have := h lX.length
    rw [List.getElem?_eq_none (Nat.le_refl _), List.getElem?_eq_getElem hl] at this
    cases lI[lX.length] <;> simp [RelT] at this

theorem relT_set {L : Lay} {lI : List (Option (Res IR.T))} {lX : List (Option X)}
    (h : ∀ j : Nat, RelT L lI[j]? lX[j]?) {i : Nat} {vI : Option (Res IR.T)} {vX : Option X}
    (hv : RelT L (some vI) (some vX)) : ∀ j : Nat, RelT L (lI.set i vI)[j]? (lX.set i vX)[j]? := by
  intro j
  have hl := relT_len h
  simp only [List.getElem?_set]
  split
  · next he =>
    subst he
    rw [hl]
    split
    · exact hv
    · trivial
  · exact h j

theorem relT_push {L : Lay} {lI : List (Option (Res IR.T))} {lX : List (Option X)}
    (h : ∀ j : Nat, RelT L lI[j]? lX[j]?) {vI : Option (Res IR.T)} {vX : Option X}
    (hv : RelT L (some vI) (some vX)) : ∀ j : Nat, RelT L (lI ++ [vI])[j]? (lX ++ [vX])[j]? := by
  intro j
  have hl := relT_len h
  rcases Nat.lt_or_ge j lI.length with hj | hj
  · rw [List.getElem?_append_left hj, List.getElem?_append_left (hl ▸ hj)]
    exact h j
  · rw [List.getElem?_append_right hj, List.getElem?_append_right (hl ▸ hj), hl]
    rcases Nat.lt_or_ge (j - lX.length) 1 with h1 | h1
    · have : j - lX.length = 0 := by omega
      rw [this]
      exact hv
    · rw [List.getElem?_eq_none (by simpa using h1), List.getElem?_eq_none (by simpa using h1)]
      trivial

/-- Changing only the IR thread `i`, where an x86 thread exists. -/
theorem relT_setI {L : Lay} {lI : List (Option (Res IR.T))} {lX : List (Option X)}
    (h : ∀ j : Nat, RelT L lI[j]? lX[j]?) {i : Nat} {x : X} (hx : lX[i]? = some (some x)) {r : Res IR.T}
    (hv : Match L r x) : ∀ j : Nat, RelT L (lI.set i (some r))[j]? lX[j]? := by
  intro j
  have hl := relT_len h
  simp only [List.getElem?_set]
  split
  · next he =>
    subst he
    have : i < lX.length := by
      rcases Nat.lt_or_ge i lX.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none h1] at hx; cases hx
    rw [hl]
    simp only [this, ↓reduceIte, hx]
    exact hv
  · exact h j

/-- The x86 thread `j` exists; the IR thread there is matched. -/
theorem rel_at {L : Lay} {M : MemSys} {cI : Cfg M (Res IR.T)} {cX : Cfg M X} (hR : Rel L cI cX) {j : Nat}
    {x : X} (hx : cX.ths[j]? = some (some x)) : ∃ r, cI.ths[j]? = some (some r) ∧ Match L r x := by
  have := hR.th j
  rw [hx] at this
  rcases h : cI.ths[j]? with _ | _ | r
  · rw [h] at this; exact this.elim
  · rw [h] at this; exact this.elim
  · rw [h] at this; exact ⟨r, rfl, this⟩

/-! ## A pending next IR instruction is begun silently -/

theorem match_next {L : Lay} (hI : CInv L) {t : IR.T} {p : Pos} (h : MatchP L (.next t) p) :
    MatchP L (IR.step t) p := by
  generalize hr : (Res.next t : Res IR.T) = r at h
  induction h with
  | priv hs _ ih => exact .priv hs (ih hr)
  | tbl op hop hs _ ih => exact .tbl op hop hs fun w => ih w hr
  | ask => cases hr
  | fault => cases hr
  | disp hD => cases hr; exact step_ok hI hD
  | kfault => cases hr
  | knext _ ih => exact .knext (ih hr)

/-- From any related pair, the IR thread `j` reaches (in at most one silent step) a rest that is not a pending
    next instruction and still matches. -/
theorem norm {L : Lay} (hI : CInv L) {M : MemSys} {cI : Cfg M (Res IR.T)} {cX : Cfg M X} (hR : Rel L cI cX)
    {j : Nat} {x : X} (hx : cX.ths[j]? = some (some x)) :
    ∃ cI' r, Rel L cI' cX ∧ cI'.ths[j]? = some (some r) ∧ Match L r x ∧ (∀ t, r ≠ .next t) ∧
      ∀ l e m, Tr M actI cI' l e m → ∃ m', Tr M actI cI l e m' := by
  obtain ⟨r, hr, hM⟩ := rel_at hR hx
  cases r with
  | next t =>
    refine ⟨⟨cI.ms, cI.ths.set j (some (IR.step t))⟩, IR.step t,
      ⟨hR.ms, relT_setI hR.th hx (match_next hI hM)⟩, ?_, match_next hI hM, ?_, ?_⟩
    · have : j < cI.ths.length := by
        rcases Nat.lt_or_ge j cI.ths.length with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none h1] at hr; cases hr
      simp only [List.getElem?_set_self this]
    · intro t' h
      simp only [IR.step, rd8] at h
      cases h
    · intro l e m h
      exact ⟨m + 1, .priv hr rfl h⟩
  | fault =>
    refine ⟨cI, .fault, hR, hr, hM, ?_, fun l e m h => ⟨m, h⟩⟩
    intro t h; cases h
  | unk =>
    refine ⟨cI, .unk, hR, hr, hM, ?_, fun l e m h => ⟨m, h⟩⟩
    intro t h; cases h
  | ask o k =>
    refine ⟨cI, .ask o k, hR, hr, hM, ?_, fun l e m h => ⟨m, h⟩⟩
    intro t h; cases h

/-- Changing only the x86 thread `i`, where an IR thread exists. -/
theorem relT_setX {L : Lay} {lI : List (Option (Res IR.T))} {lX : List (Option X)}
    (h : ∀ j : Nat, RelT L lI[j]? lX[j]?) {i : Nat} {r : Res IR.T} (hr : lI[i]? = some (some r)) {x : X}
    (hv : Match L r x) : ∀ j : Nat, RelT L lI[j]? (lX.set i (some x))[j]? := by
  intro j
  have hl := relT_len h
  simp only [List.getElem?_set]
  split
  · next he =>
    subst he
    have : i < lI.length := by
      rcases Nat.lt_or_ge i lI.length with h1 | h1
      · exact h1
      · rw [List.getElem?_eq_none h1] at hr; cases hr
    rw [← hl]
    simp only [this, ↓reduceIte, hr]
    exact hv
  · exact h j

/-! ## What a matched x86 thread can do -/

theorem inv_unk {L : Lay} {r : Res IR.T} {x : X} (h : Match L r x) : step L.C x ≠ .unk := by
  cases h with
  | priv hs => rw [hs]; exact fun h => by cases h
  | tbl _ _ hs => rw [hs]; exact fun h => by cases h
  | ask hs => rw [hs]; exact fun h => by cases h
  | fault hs => rw [hs]; exact fun h => by cases h
  | disp hD => rw [step_code hD.code]; simp [exec, rd8]

theorem inv_next {L : Lay} {r : Res IR.T} {x y : X} (h : Match L r x) (hs : step L.C x = .next y)
    (hr : ∀ t, r ≠ .next t) : Match L r y := by
  cases h with
  | priv hs' h' => rw [hs] at hs'; cases hs'; exact h'
  | tbl _ _ hs' => rw [hs] at hs'; cases hs'
  | ask hs' => rw [hs] at hs'; cases hs'
  | fault hs' => rw [hs] at hs'; cases hs'
  | disp => exact absurd rfl (hr _)

theorem inv_fault {L : Lay} {r : Res IR.T} {x : X} (h : Match L r x) (hs : step L.C x = .fault)
    (hr : ∀ t, r ≠ .next t) : r = .fault := by
  cases h with
  | priv hs' => rw [hs] at hs'; cases hs'
  | tbl _ _ hs' => rw [hs] at hs'; cases hs'
  | ask hs' => rw [hs] at hs'; cases hs'
  | fault => rfl
  | disp => exact absurd rfl (hr _)

theorem inv_ask {L : Lay} {r : Res IR.T} {x : X} {o : Op} {k : Ans → Res X} (h : Match L r x)
    (hs : step L.C x = .ask o k) (hr : ∀ t, r ≠ .next t) :
    (∃ op, op < 256 ∧ o = .rd 8 (taddr L (BitVec.ofNat 64 op)) ∧ ∀ w, MatchK L r (k (some (L.H op, w)))) ∨
    (∃ kI, r = .ask o kI ∧ ∀ a, MatchK L (kI a) (k a)) := by
  cases h with
  | priv hs' => rw [hs] at hs'; cases hs'
  | tbl op hop hs' hk => rw [hs] at hs'; cases hs'; exact .inl ⟨op, hop, rfl, hk⟩
  | ask hs' hk => rw [hs] at hs'; cases hs'; exact .inr ⟨_, rfl, hk⟩
  | fault hs' => rw [hs] at hs'; cases hs'
  | disp => exact absurd rfl (hr _)

theorem invK_next {L : Lay} {r : Res IR.T} {y : X} (h : MatchK L r (.next y)) : Match L r y := by
  cases h with
  | knext h => exact h

theorem invK_ende {L : Lay} {r : Res IR.T} {rx : Res X} {e : Ende} (h : MatchK L r rx)
    (he : Res.ende rx = some e) : r = .fault ∧ e = .fault := by
  cases h with
  | kfault => simp [Res.ende] at he; exact ⟨rfl, he.symm⟩
  | knext => simp [Res.ende] at he

/-! ## The theorem -/

theorem lbl_rd (i : Nat) (a : W) (b : Ans) : lbl i (.rd 8 a) b = [] := rfl

theorem runner_mt {L : Lay} {M : MemSys} (hF : Fixed M L) (hI : CInv L) :
    ∀ (n : Nat) {cI : Cfg M (Res IR.T)} {cX : Cfg M X} {l : List Ev} {e : Ende},
    Rel L cI cX → Tr M (actX L) cX l e n → e ≠ .unk ∧ ∃ m, Tr M actI cI l e m := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro cI cX l e hR hT
  cases hT with
  | nil => exact ⟨by decide, 0, .nil cI⟩
  | @tau _ ms' _ _ _ hτ hT' =>
    obtain ⟨he, m, hm⟩ := ih _ (Nat.lt_succ_self _) (cI := ⟨ms', cI.ths⟩) (cX := ⟨ms', cX.ths⟩) ⟨rfl, hR.th⟩ hT'
    exact ⟨he, m + 1, .tau (hR.ms ▸ hτ) hm⟩
  | @priv _ j x x' _ _ _ hx hs hT' =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    have hM' := inv_next hM hs hn
    obtain ⟨he, m, hm⟩ := ih _ (Nat.lt_succ_self _) (cI := cI') (cX := ⟨cX.ms, cX.ths.set j (some x')⟩)
      ⟨hR'.ms, relT_setX hR'.th hr hM'⟩ hT'
    exact ⟨he, lift _ _ _ hm⟩
  | @stop _ j x e' hx hs =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    have hne := inv_unk hM
    simp only [actX] at hs
    cases hst : step L.C x with
    | fault =>
      rw [hst] at hs
      simp only [Res.ende, Option.some.injEq] at hs
      subst hs
      have := inv_fault hM hst hn
      subst this
      exact ⟨by decide, lift _ _ _ (.stop hr rfl)⟩
    | unk => exact absurd hst hne
    | next => rw [hst] at hs; simp [Res.ende] at hs
    | ask => rw [hst] at hs; simp [Res.ende] at hs
  | @ask _ j x x' o k a ms l' _ _ hx hs hsp hans hk hT' =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    rcases inv_ask hM hs hn with ⟨op, hop, rfl, hkt⟩ | ⟨kI, rfl, hkI⟩
    · obtain ⟨rfl, w, rfl⟩ := hF _ _ _ _ _ hop hans
      have hM' := invK_next (hk ▸ hkt w)
      obtain ⟨he, m, hm⟩ := ih _ (Nat.lt_succ_self _) (cI := cI') (cX := ⟨cX.ms, cX.ths.set j (some x')⟩)
        ⟨hR'.ms, relT_setX hR'.th hr hM'⟩ hT'
      exact ⟨he, lift _ _ _ (by simpa [lbl_rd] using hm)⟩
    · have hM' := invK_next (hk ▸ hkI a)
      obtain ⟨he, m, hm⟩ := ih _ (Nat.lt_succ_self _) (cI := ⟨ms, cI'.ths.set j (some (kI a))⟩)
        (cX := ⟨ms, cX.ths.set j (some x')⟩)
        ⟨rfl, relT_set hR'.th (vI := some (kI a)) (vX := some x') hM'⟩ hT'
      exact ⟨he, lift _ _ _ (.ask hr rfl hsp (hR'.ms ▸ hans) rfl hm)⟩
  | @askStop _ j x o k a ms e' hx hs hsp hans hk =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    rcases inv_ask hM hs hn with ⟨op, hop, rfl, hkt⟩ | ⟨kI, rfl, hkI⟩
    · obtain ⟨rfl, w, rfl⟩ := hF _ _ _ _ _ hop hans
      obtain ⟨rfl, rfl⟩ := invK_ende (hkt w) hk
      exact ⟨by decide, lift _ _ _ (by simpa [lbl_rd] using (Tr.stop (act := actI) hr rfl))⟩
    · obtain ⟨hf, rfl⟩ := invK_ende (hkI a) hk
      refine ⟨by decide, lift _ _ 2 ?_⟩
      have h2 : Tr M actI ⟨ms, cI'.ths.set j (some (kI a))⟩ [] .fault 1 := by
        have : (cI'.ths.set j (some (kI a)))[j]? = some (some (kI a)) := by
          have hj : j < cI'.ths.length := by
            rcases Nat.lt_or_ge j cI'.ths.length with h1 | h1
            · exact h1
            · rw [List.getElem?_eq_none h1] at hr; cases hr
          simp only [List.getElem?_set_self hj]
        exact .stop this (by rw [hf]; rfl)
      simpa using Tr.ask hr rfl hsp (hR'.ms ▸ hans) rfl h2
  | @exit _ j x q k l' _ _ hx hs hq hT' =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    rcases inv_ask hM hs hn with ⟨op, _, ho, _⟩ | ⟨kI, rfl, _⟩
    · cases ho
    · obtain ⟨he, m, hm⟩ := ih _ (Nat.lt_succ_self _) (cI := ⟨cI'.ms, cI'.ths.set j none⟩)
        (cX := ⟨cX.ms, cX.ths.set j none⟩)
        ⟨hR'.ms, relT_set hR'.th (vI := none) (vX := none) trivial⟩ hT'
      exact ⟨he, lift _ _ _ (.exit hr rfl hq hm)⟩
  | @exitGroup _ j x q k hx hs hq =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    rcases inv_ask hM hs hn with ⟨op, _, ho, _⟩ | ⟨kI, rfl, _⟩
    · cases ho
    · exact ⟨by simp, lift _ _ _ (.exitGroup hr rfl hq)⟩
  | @cloneNo _ j x x' k a ms l' _ _ hx hs hans hno hk hT' =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    rcases inv_ask hM hs hn with ⟨op, _, ho, _⟩ | ⟨kI, rfl, hkI⟩
    · cases ho
    · have hM' := invK_next (hk ▸ hkI a)
      obtain ⟨he, m, hm⟩ := ih _ (Nat.lt_succ_self _) (cI := ⟨ms, cI'.ths.set j (some (kI a))⟩)
        (cX := ⟨ms, cX.ths.set j (some x')⟩)
        ⟨rfl, relT_set hR'.th (vI := some (kI a)) (vX := some x') hM'⟩ hT'
      exact ⟨he, lift _ _ _ (.cloneNo hr rfl (hR'.ms ▸ hans) hno rfl hm)⟩
  | @cloneNoStop _ j x k a ms e' hx hs hans hno hk =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    rcases inv_ask hM hs hn with ⟨op, _, ho, _⟩ | ⟨kI, rfl, hkI⟩
    · cases ho
    · obtain ⟨hf, rfl⟩ := invK_ende (hkI a) hk
      refine ⟨by decide, lift _ _ 2 ?_⟩
      have h2 : Tr M actI ⟨ms, cI'.ths.set j (some (kI a))⟩ [] .fault 1 := by
        have : (cI'.ths.set j (some (kI a)))[j]? = some (some (kI a)) := by
          have hj : j < cI'.ths.length := by
            rcases Nat.lt_or_ge j cI'.ths.length with h1 | h1
            · exact h1
            · rw [List.getElem?_eq_none h1] at hr; cases hr
          simp only [List.getElem?_set_self hj]
        exact .stop this (by rw [hf]; rfl)
      exact .cloneNo hr rfl (hR'.ms ▸ hans) hno rfl h2
  | @clone _ j x x' xc k rr w ms l' _ _ hx hs hans hpos hk hkc hT' =>
    obtain ⟨cI', r, hR', hr, hM, hn, lift⟩ := norm hI hR hx
    rcases inv_ask hM hs hn with ⟨op, _, ho, _⟩ | ⟨kI, rfl, hkI⟩
    · cases ho
    · have hM' := invK_next (hk ▸ hkI (some (rr, w)))
      have hMc := invK_next (hkc ▸ hkI (some (0, w)))
      obtain ⟨he, m, hm⟩ := ih _ (Nat.lt_succ_self _)
        (cI := ⟨ms, cI'.ths.set j (some (kI (some (rr, w)))) ++ [some (kI (some (0, w)))]⟩)
        (cX := ⟨ms, cX.ths.set j (some x') ++ [some xc]⟩)
        ⟨rfl, relT_push (relT_set hR'.th (vI := some (kI (some (rr, w)))) (vX := some x') hM')
          (vI := some (kI (some (0, w)))) (vX := some xc) hMc⟩ hT'
      exact ⟨he, lift _ _ _ (.clone hr rfl (hR'.ms ▸ hans) hpos rfl rfl hm)⟩

end Runner.Beweis
