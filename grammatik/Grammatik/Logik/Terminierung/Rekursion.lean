/-
  File:      Grammatik/Logik/Terminierung/Rekursion.lean
  Subject:   T4 -- MEASURED RECURSION TERMINATES (2026-10-22): on every infinite run of machine GX, every thread
             takes only finitely many steps, for a program whose calls go down a rank or along a cycle whose
             measure falls.

  A cost table cannot bound measured recursion: Ackermann's `(1, 0)` calls `(0, k)` for every `k`, so no number
  bounds the steps below `(1, 0)`. The bound is a WELL-FOUNDED RANK instead, read off a thread's stack:

  * every frame weighs `((rk f, measure of f at its entry), potRest of its residue)` (`gew`) -- the residue's
    potential with every call priced `0`, so it falls at every own step of the frame (`schrittArt`);
  * the stack, read from the bottom, is ordered lexicographically with a proper prefix below its extensions
    (`slt`); on stacks whose weights fall from bottom to top (`KetteW`) that order is well-founded
    (`acc_slt`);
  * an own step lowers the rank: a head step lowers the head's potential, a call lowers the caller's (the callee
    sits above it), a return drops the head and leaves the caller at most where it was; another thread's step
    leaves the rank alone;
  * the weights fall up the stack because every call goes to a lower rank or along a cycle (`tor`, checked on the
    bodies by `rufeE`), and along a cycle the replay of the goal proof carries the measure's fall to the frame
    (`WarteSA`, fed by `MassPflicht`).

  `endlich_aus_wf`: a sequence that falls in a well-founded order at marked indices and stays put elsewhere is
  marked only finitely often. `rekursion_endlich` is the theorem; `rekursion_endlich_aus` takes the premises of
  the goal's replay (`zielInvSA_erreichbarGX`) in place of the replay itself.

  The budget `passes` makes every `forever` finite in the model; T5 separates the programs whose termination does
  not lean on it.
-/
import Grammatik.Zielsatz.Atomar.AtomarInvarianten
import Grammatik.Logik.Fortschritt.KostenG
import Grammatik.Logik.Terminierung.Mass
import Grammatik.Logik.Terminierung.LaufGX

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Weights and their order -/

/-- A frame's weight: (rank, measure) of its function and entry, and the potential of its residue. -/
abbrev Gewicht : Type := (Nat × List Nat) × Nat

/-- **The order on weights**: by rank; at one rank by the measure (tuples of one length); at one measure by the
    potential. -/
def wlt (a b : Gewicht) : Prop :=
  a.1.1 < b.1.1 ∨ (a.1.1 = b.1.1 ∧ (lexLtN b.1.2.length a.1.2 b.1.2 ∨ (a.1.2 = b.1.2 ∧ a.2 < b.2)))

theorem acc_wlt : ∀ a : Gewicht, Acc wlt a := by
  suffices H : ∀ (r : Nat) (n : Nat) (w : List Nat), Acc (lexLtN n) w → w.length = n →
      ∀ p, Acc wlt ((r, w), p) by
    intro a
    exact H a.1.1 a.1.2.length a.1.2 ((lexLt_wf _).apply _) rfl a.2
  intro r
  induction r using Nat.strongRecOn with
  | _ r ihr =>
  intro n w hw
  induction hw with
  | intro w _ ihw =>
  intro hl p
  induction p using Nat.strongRecOn with
  | _ p ihp =>
  refine ⟨_, fun b hb => ?_⟩
  obtain ⟨⟨rb, wb⟩, pb⟩ := b
  rcases hb with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · exact ihr rb h _ wb ((lexLt_wf _).apply _) rfl pb
  · dsimp only at h1 h
    subst h1
    rw [hl] at h
    exact ihw wb h h.1 pb
  · dsimp only at h1 h2 h3
    subst h1; subst h2
    exact ihp pb h3

/-! ## 2. Stacks and their order -/

/-- The weights of a stack, read from the bottom, fall from each one to the next. -/
def KetteW : List Gewicht → Prop
  | x :: y :: r => wlt y x ∧ KetteW (y :: r)
  | _ => True

/-- **The order on stacks** (read from the bottom): lexicographic, a proper prefix below its extensions. -/
def slt : List Gewicht → List Gewicht → Prop
  | [], _ :: _ => True
  | x :: xs, y :: ys => wlt x y ∨ (x = y ∧ slt xs ys)
  | _, [] => False

/-- The order restricted to falling stacks. -/
def sltK (a b : List Gewicht) : Prop := KetteW a ∧ slt a b

theorem ketteW_tail {x : Gewicht} : ∀ {t : List Gewicht}, KetteW (x :: t) → KetteW t
  | [], _ => trivial
  | _ :: _, h => h.2

/-- **The stack order is well-founded on falling stacks.** -/
theorem acc_sltK : ∀ b : List Gewicht, KetteW b → Acc sltK b := by
  have nil : Acc sltK [] := ⟨_, fun a ⟨_, h⟩ => by cases a <;> simp [slt] at h⟩
  intro b hb
  cases b with
  | nil => exact nil
  | cons x t =>
  revert t
  induction (acc_wlt x) with
  | intro x _ ihx =>
  -- every falling tail below `x` is accessible
  have hacc : ∀ t, KetteW (x :: t) → Acc sltK t := by
    intro t ht
    cases t with
    | nil => exact nil
    | cons y t' => exact ihx y ht.1 t' ht.2
  intro t ht
  induction (hacc t ht) with
  | intro t _ iht =>
  refine ⟨_, fun a ⟨ha, hlt⟩ => ?_⟩
  cases a with
  | nil => exact nil
  | cons y as =>
    rcases hlt with h | ⟨rfl, h⟩
    · exact ihx y h as ha
    · exact iht as ⟨ketteW_tail ha, h⟩ ha

theorem ketteW_snoc : ∀ (xs : List Gewicht) (a b : Gewicht), KetteW (xs ++ [a]) → wlt b a →
    KetteW (xs ++ [a, b])
  | [], _, _, _, h => ⟨h, trivial⟩
  | [x], a, b, h, hb => ⟨h.1, hb, trivial⟩
  | x :: y :: r, a, b, h, hb => ⟨h.1, ketteW_snoc (y :: r) a b h.2 hb⟩

/-- A top-first stack whose weights fall upward. -/
def KetteT : List Gewicht → Prop
  | x :: y :: r => wlt x y ∧ KetteT (y :: r)
  | _ => True

theorem ketteT_reverse : ∀ l : List Gewicht, KetteT l → KetteW l.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: r, h => by
      have ih := ketteT_reverse (y :: r) h.2
      simp only [List.reverse_cons] at ih ⊢
      rw [List.append_assoc]
      exact ketteW_snoc _ y x ih h.1

theorem slt_praefix : ∀ (p : List Gewicht) {a b : List Gewicht}, slt a b → slt (p ++ a) (p ++ b)
  | [], _, _, h => h
  | x :: p, _, _, h => Or.inr ⟨rfl, slt_praefix p h⟩

/-! ## 3. A sequence that falls at marked indices -/

theorem ex_min {p : Nat → Prop} : ∀ d, p d → ∃ d, p d ∧ ∀ e, e < d → ¬ p e := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro hd
  by_cases h : ∃ e, e < d ∧ p e
  · obtain ⟨e, he, hpe⟩ := h
    exact ih e he hpe
  · exact ⟨d, hd, fun e he hpe => h ⟨e, he, hpe⟩⟩

/-- **Marked only finitely often**: a sequence that falls in a well-founded order at every marked index and stays
    put at every other is marked only finitely often. -/
theorem endlich_aus_wf {α : Type} (Rel : α → α → Prop) (x : Nat → α) (own : Nat → Prop)
    (hacc : ∀ j, Acc Rel (x j)) (hdown : ∀ j, own j → Rel (x (j + 1)) (x j))
    (hsame : ∀ j, ¬ own j → x (j + 1) = x j) : ∃ N, ∀ j, N ≤ j → ¬ own j := by
  suffices H : ∀ a, Acc Rel a → ∀ j, x j = a → ∃ N, ∀ j', N ≤ j' → ¬ own j' from
    H _ (hacc 0) 0 rfl
  intro a ha
  induction ha with
  | intro a _ ih =>
  intro j hj
  by_cases h : ∃ d, own (j + d)
  · obtain ⟨d0, hd0⟩ := h
    obtain ⟨d, hd, hmin⟩ := ex_min (p := fun d => own (j + d)) d0 hd0
    have hconst : ∀ e, e ≤ d → x (j + e) = a := by
      intro e
      induction e with
      | zero => intro _; exact hj
      | succ e ihe =>
        intro he
        rw [← Nat.add_assoc, hsame _ (hmin e (by omega))]
        exact ihe (by omega)
    have hr := hdown _ hd
    rw [hconst d (Nat.le_refl d)] at hr
    exact ih _ hr (j + d + 1) rfl
  · refine ⟨j, fun j' hj' hown => h ⟨j' - j, ?_⟩⟩
    rw [Nat.add_sub_cancel' hj']
    exact hown

/-! ## 4. The rank of a thread -/

section Rang

variable (P : Programm D) (pa : Nat) (m : Mass D) (zyk : D.Fn → D.Fn → Bool) (rk : D.Fn → Nat) (fs : List D.Fn)

/-- **The call gate**: from `f`, a call goes to a lower rank, or along `f`'s cycle at the same rank. -/
def tor (f g : D.Fn) : Bool := decide (rk g < rk f) || (rk g == rk f && zyk f g)

/-- **The gate of an indirect call** through signature `n`: every function of signature `n` passes `tor`. -/
def torS (f : D.Fn) (n : Nat) : Bool := fs.all fun g => !(D.passt g n) || tor zyk rk f g

theorem torS_tor (hvoll : ∀ g, g ∈ fs) {f : D.Fn} {n : Nat} {g : D.Fn} (h : torS zyk rk fs f n = true)
    (hp : D.passt g n = true) : tor zyk rk f g = true := by
  have := List.all_eq_true.mp h g (hvoll g)
  simpa [hp] using this

/-- A frame's weight. -/
def gew (r : RufRahmenG D) : Gewicht :=
  ((rk (RufSchluesselG r).1, m.wert (RufSchluesselG r).1 (RufSchluesselG r).2.2 (RufSchluesselG r).2.1),
    potRest (fun _ => 0) pa r.rest.2.2.2.2)

/-- **The rank of a thread**: the weights of its stack, read from the bottom. -/
def rangF (z : RufFadenG D) : List Gewicht := ((z.kopf :: z.stapel).map (gew pa m rk)).reverse

/-- The static facts of a stack, top first: every frame's residue calls through its gate, and every frame was
    called through the gate of the frame below it. -/
def Glieder : RufRahmenG D → List (RufRahmenG D) → Prop
  | r, [] => rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r.rest.2.2.2.2 = true
  | r, b :: rest => rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r.rest.2.2.2.2 = true ∧ tor zyk rk b.f r.f = true ∧ Glieder b rest

theorem glieder_kopf {r : RufRahmenG D} {st : List (RufRahmenG D)} (h : Glieder zyk rk fs r st) :
    rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r.rest.2.2.2.2 = true := by
  cases st with
  | nil => exact h
  | cons _ _ => exact h.1

theorem glieder_ersetze {r r' : RufRahmenG D} {st : List (RufRahmenG D)} (h : Glieder zyk rk fs r st)
    (hf : r'.f = r.f) (hok : rufeR (tor zyk rk r.f) (torS zyk rk fs r.f) true r'.rest.2.2.2.2 = true) : Glieder zyk rk fs r' st := by
  have ht : tor zyk rk r'.f = tor zyk rk r.f := by rw [hf]
  have hts : torS zyk rk fs r'.f = torS zyk rk fs r.f := by rw [hf]
  cases st with
  | nil => show rufeR (tor zyk rk r'.f) (torS zyk rk fs r'.f) true r'.rest.2.2.2.2 = true; rw [ht, hts]; exact hok
  | cons b rest => exact ⟨by rw [ht, hts]; exact hok, hf ▸ h.2.1, h.2.2⟩

/-- Along the stack, every call into the caller's cycle has a smaller measure than the caller's entry (the
    replay's fact, `WarteSA`). -/
def MassFaellt : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest =>
      (∃ κ : World D, zyk F.f G.1 = true → lexLt (m.wert G.1 κ G.2.1) (m.wert F.f F.s0 F.rho) = true) ∧
      MassFaellt (RufSchluesselG F) rest

/-- **The weights fall up the stack**: the gate's links, with the measure's fall along a cycle. -/
theorem kette_aus (hL : ∀ f g, zyk f g = true → (m f).length = (m g).length) :
    ∀ (r : RufRahmenG D) (st : List (RufRahmenG D)), Glieder zyk rk fs r st →
      MassFaellt m zyk (RufSchluesselG r) st → KetteT ((r :: st).map (gew pa m rk))
  | r, [], _, _ => trivial
  | r, b :: rest, h, hm => by
      refine ⟨?_, kette_aus hL b rest h.2.2 hm.2⟩
      have ht := h.2.1
      unfold tor at ht
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at ht
      rcases ht with hlt | ⟨heq, hz⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨heq, Or.inl ?_⟩
        obtain ⟨κ, hκ⟩ := hm.1
        have hlex : lexLt (m.wert r.f κ r.rho) (m.wert b.f b.s0 b.rho) = true := hκ hz
        rw [Mass.wert_welt m _ κ r.s0] at hlex
        refine ⟨?_, rfl, hlex⟩
        show (m.wert r.f r.s0 r.rho).length = (m.wert b.f b.s0 b.rho).length
        simp only [Mass.wert, List.length_map]
        exact (hL _ _ hz).symm

end Rang

/-! ## 5. One step -/

section Schritt

variable {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (m : Mass D)
  (zyk : D.Fn → D.Fn → Bool) (rk : D.Fn → Nat) (fs : List D.Fn)

theorem schluessel_kopf {a b : RufFadenG D}
    (h : RufFadenSchluesselG a = RufFadenSchluesselG b) : RufSchluesselG a.kopf = RufSchluesselG b.kopf := by
  unfold RufFadenSchluesselG at h
  simp only [List.map_cons, List.cons.injEq] at h
  exact h.1

theorem gew_fst {r r' : RufRahmenG D} (hk : RufSchluesselG r' = RufSchluesselG r) :
    (gew pa m rk r').1 = (gew pa m rk r).1 := by
  unfold gew
  rw [hk]

theorem wlt_pot {a b : Gewicht} (h1 : a.1 = b.1) (h2 : a.2 < b.2) : wlt a b :=
  Or.inr ⟨congrArg (·.1) h1, Or.inr ⟨congrArg (·.2) h1, h2⟩⟩

/-- **An own step of a GX run lowers the thread's rank and keeps its static facts.** -/
theorem schritt_rang (hvoll : ∀ g, g ∈ fs)
    (hR : ∀ f, rufeE (tor zyk rk f) (torS zyk rk fs f) true (P.rumpf f) = true)
    {M M' : RufMaschineG D} {t : Faden} (hP0 : RufMaschinePasstG M) (hP1 : RufMaschinePasstG M')
    (hs : RufSchrittGX P O pa Tg M t M')
    (hG : Glieder zyk rk fs (M.faeden t).kopf (M.faeden t).stapel) :
    slt (rangF pa m rk (M'.faeden t)) (rangF pa m rk (M.faeden t)) ∧
      Glieder zyk rk fs (M'.faeden t).kopf (M'.faeden t).stapel := by
  have hk := Zielsatz.schritt_schluesselX hP0 hP1 hs
  obtain ⟨σ, M'', hg, _, _, _, hfa, _, _⟩ := hs
  have hfa' : M'.faeden t = M''.faeden t := by rw [hfa]
  have hfm : (mitSpeicher M σ).faeden t = M.faeden t := rfl
  have hlen : ∀ z : RufFadenG D, (RufFadenSchluesselG z).length = z.stapel.length + 1 := by
    intro z; simp [RufFadenSchluesselG]
  rcases schrittArt hg (fun _ => 0) (tor zyk rk (M.faeden t).kopf.f) (torS zyk rk fs (M.faeden t).kopf.f) true with
    ⟨hst, hpot⟩ | ⟨g, caller', rho, s0, hst, hkopf, hpush⟩ | ⟨caller, rst, hst, hst', hpop⟩
  · -- the head steps: same stack, same key, lower potential
    rw [hfm, ← hfa'] at hst hpot
    obtain ⟨hok', hlt⟩ := hpot (glieder_kopf zyk rk fs hG)
    have hkey : RufSchluesselG (M'.faeden t).kopf = RufSchluesselG (M.faeden t).kopf := by
      rcases hk with he | ⟨_, he⟩ | ⟨_, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩
      · exact schluessel_kopf he
      all_goals
        exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst] at this
        omega
    have hf : (M'.faeden t).kopf.f = (M.faeden t).kopf.f := congrArg Sigma.fst hkey
    refine ⟨?_, ?_⟩
    · unfold rangF
      rw [hst]
      simp only [List.map_cons, List.reverse_cons]
      apply slt_praefix
      exact Or.inl (wlt_pot (gew_fst m rk hkey) (by dsimp only [gew]; omega))
    · rw [hst]
      exact glieder_ersetze zyk rk fs hG hf hok'
  · -- a call: the caller's potential falls, the callee sits above it
    rw [hfm, ← hfa'] at hst
    rw [← hfa'] at hkopf
    rw [hfm] at hpush
    obtain ⟨hokc, hdir⟩ := hpush (glieder_kopf zyk rk fs hG)
    have hzg : tor zyk rk (M.faeden t).kopf.f g = true := by
      rcases hdir with ⟨hz, _⟩ | ⟨n, hn, hp, _⟩
      · exact hz
      · exact torS_tor zyk rk fs hvoll hn hp
    have hlt : potRest (fun _ => 0) pa caller'.rest.2.2.2.2 + 1 ≤
        potRest (fun _ => 0) pa (M.faeden t).kopf.rest.2.2.2.2 := by
      rcases hdir with ⟨_, h⟩ | ⟨_, _, _, h⟩
      · simp only [Nat.add_zero] at h; omega
      · exact h
    have hkey : RufSchluesselG caller' = RufSchluesselG (M.faeden t).kopf := by
      rcases hk with he | ⟨_, he⟩ | ⟨_, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩
      · exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst] at this
        omega
      · unfold RufFadenSchluesselG at he
        rw [hst] at he
        simp only [List.map_cons, List.cons.injEq] at he
        exact he.2.1
      all_goals
        exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst] at this
        omega
    have hcf : caller'.f = (M.faeden t).kopf.f := congrArg Sigma.fst hkey
    refine ⟨?_, ?_⟩
    · unfold rangF
      rw [hst]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      apply slt_praefix
      exact Or.inl (wlt_pot (gew_fst m rk hkey) (by dsimp only [gew]; omega))
    · rw [hst, hkopf]
      refine ⟨hR g, ?_, glieder_ersetze zyk rk fs hG hcf hokc⟩
      show tor zyk rk caller'.f g = true
      rw [hcf]; exact hzg
  · -- a return: the head goes, the caller stays at most where it was
    rw [hfm] at hst
    rw [← hfa'] at hst' hpop
    obtain ⟨hgate, hle⟩ := hpop (fun _ => 0) (tor zyk rk caller.f) (torS zyk rk fs caller.f) true
    have hkey : RufSchluesselG (M'.faeden t).kopf = RufSchluesselG caller := by
      rcases hk with he | ⟨_, he⟩ | ⟨_, _, _, _, _, he, _⟩ | ⟨_, _, _, _, _, he, _⟩
      · exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst, hst'] at this
        omega
      · exfalso
        have := congrArg List.length he
        simp only [List.length_cons, hlen, hst, hst'] at this
        omega
      all_goals
        unfold RufFadenSchluesselG at he
        rw [hst, hst'] at he
        simp only [List.map_cons, List.cons.injEq] at he
        exact he.2.1.symm
    have hf : (M'.faeden t).kopf.f = caller.f := congrArg Sigma.fst hkey
    rw [hst] at hG
    refine ⟨?_, ?_⟩
    · unfold rangF
      rw [hst, hst']
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      apply slt_praefix
      by_cases hp : potRest (fun _ => 0) pa (M'.faeden t).kopf.rest.2.2.2.2 <
          potRest (fun _ => 0) pa caller.rest.2.2.2.2
      · exact Or.inl (wlt_pot (gew_fst m rk hkey) hp)
      · refine Or.inr ⟨Prod.ext (gew_fst m rk hkey) (by dsimp only [gew]; omega), trivial⟩
    · rw [hst']
      exact glieder_ersetze zyk rk fs hG.2.2 hf (hgate (glieder_kopf zyk rk fs hG.2.2))

end Schritt

/-! ## 6. Runs -/

/-- The replay carries the measure's fall along every stack. -/
theorem stapelSA_massFaellt (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
    (lok : D.Tab ⊕ D.Glob → Bool) (Tg : D.Tab ⊕ D.Glob → Prop) (m : Mass D) (zyk : D.Fn → D.Fn → Bool) :
    ∀ (G : Σ f : D.Fn, Env D (D.params f) × World D) (st : List (RufRahmenG D)),
      StapelSA P O passes Q S lok Tg m zyk G st → MassFaellt m zyk G st
  | _, [], _ => trivial
  | _, _ :: rest, ⟨hw, hr⟩ => by
      refine ⟨?_, stapelSA_massFaellt P O passes Q S lok Tg m zyk _ rest hr⟩
      obtain ⟨_, _, _, _, κ, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hz, _⟩ := hw
      exact ⟨κ, hz⟩

section Lauf

variable {P : Programm D} {O : Orakel D} {pa : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (m : Mass D)
  (zyk : D.Fn → D.Fn → Bool) (rk : D.Fn → Nat) (fs : List D.Fn)

/-- **T4 -- MEASURED RECURSION TERMINATES.** For a program whose every body calls only through the gate (a lower
    rank, or the caller's cycle at the same rank; no indirect call) and whose measures have one length along a
    cycle, on every infinite GX run from the start on which the goal's replay holds (with the measure), every
    thread takes only finitely many steps. -/
theorem rekursion_endlich (Q : AxEns D) (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool)
    (hvoll : ∀ g, g ∈ fs) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    (hR : ∀ f, rufeE (tor zyk rk f) (torS zyk rk fs f) true (P.rumpf f) = true)
    (hL : ∀ f g, zyk f g = true → (m f).length = (m g).length)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hInv : ∀ M, RufErreichbarGX P O pa Tg (RufStartG P sp init) M → ZielInvSA P O pa Q S lok Tg m zyk M)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden) :
    ∃ N, ∀ j, N ≤ j → R.akt j ≠ some t := by
  have hre := R.erreichbar h0
  have hP : ∀ j, RufMaschinePasstG (R.M j) := fun j => Zielsatz.gx_passt hTA sp init (hre j)
  have hGl : ∀ j, Glieder zyk rk fs ((R.M j).faeden t).kopf ((R.M j).faeden t).stapel := by
    intro j
    induction j with
    | zero =>
      rw [h0]
      rcases hi : init t with ⟨g, rho⟩
      unfold RufStartG
      dsimp only
      rw [hi]
      exact hR g
    | succ j ih =>
      cases h : R.akt j with
      | none => rw [R.stotter j h]; exact ih
      | some u =>
        by_cases htu : t = u
        · subst htu
          exact (schritt_rang m zyk rk fs hvoll hR (hP j) (hP (j + 1)) (R.schritt j t h) ih).2
        · rw [Zielsatz.gx_fremd (R.schritt j u h) t htu]; exact ih
  have hK : ∀ j, KetteW (rangF pa m rk ((R.M j).faeden t)) := fun j =>
    ketteT_reverse _ (kette_aus pa m zyk rk fs hL _ _ (hGl j)
      (stapelSA_massFaellt P O pa Q S lok Tg m zyk _ _ ((hInv _ (hre j)).1 t).2))
  obtain ⟨N, hN⟩ := endlich_aus_wf sltK (fun j => rangF pa m rk ((R.M j).faeden t))
    (fun j => R.akt j = some t) (fun j => acc_sltK _ (hK j))
    (fun j h => ⟨hK (j + 1), (schritt_rang m zyk rk fs hvoll hR (hP j) (hP (j + 1)) (R.schritt j t h) (hGl j)).1⟩)
    (fun j h => by
      cases ha : R.akt j with
      | none => show rangF pa m rk ((R.M (j + 1)).faeden t) = _; rw [R.stotter j ha]
      | some u =>
        have htu : t ≠ u := fun e => h (e ▸ ha)
        show rangF pa m rk ((R.M (j + 1)).faeden t) = _
        rw [Zielsatz.gx_fremd (R.schritt j u ha) t htu])
  exact ⟨N, hN⟩

/-- **T4 from the goal's premises**: `rekursion_endlich` with the replay supplied by `zielInvSA_erreichbarGX`, the
    user's measure duty `MassPflicht` for every function in place of the empty one the goal uses. -/
theorem rekursion_endlich_aus (Q : AxEns D) (S : SperrInv D) (K : Faden → D.Fn → Bool)
    (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S lok f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f) (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hK : ∀ f : D.Fn, KoerperGutSA P pa Q S Tg f) (hM : ∀ f, MassPflicht P pa Q S Tg m zyk f)
    (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hR : ∀ f, rufeE (tor zyk rk f) (torS zyk rk fs f) true (P.rumpf f) = true)
    (hL : ∀ f g, zyk f g = true → (m f).length = (m g).length)
    (R : LaufGX P O pa Tg) (h0 : R.M 0 = RufStartG P sp init) (t : Faden) :
    ∃ N, ∀ j, N ≤ j → R.akt j ≠ some t :=
  rekursion_endlich m zyk rk fs Q S lok hvoll hTA hR hL sp init
    (fun M hr => (zielInvSA_erreichbarGX P O pa Q S K Tg lok sp init hO hRL hQ hlok hS hvoll hAbg hWurzel
      hTA hTV hTS hTO hFragS hFS hlokK hK hM hStart hsp hex M hr).1) R h0 t

end Lauf

end Gabbro.Grammatik
