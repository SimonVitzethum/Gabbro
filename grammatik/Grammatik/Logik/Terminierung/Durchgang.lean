/-
  File:      Grammatik/Logik/Terminierung/Durchgang.lean
  Subject:   T3 -- EVERY PASS OF A SERVICE LOOP IS BOUNDED (2026-10-22): between two pass boundaries of a `forever`
             loop its thread takes at most the cost of one pass of the body.

  A service runs for ever, and it is PRODUCTIVE: from the boundary `.ewig a (n + 1) …` of a loop to its next
  boundary `.ewig a n …` of the same frame, the thread takes at most `kostenBlock body + kostenExpr inv + 2` own
  steps (`durchgang_schritte`), the body's syntax-computed cost with each call counting its callee (the cost engine
  of KostenG.lean). Other threads' steps and waiting are not counted, as in `frame_schritte_beschraenkt`.

  The engine of KostenG.lean forgets which cost table the entry frame is measured with; this file keeps it
  (`SegU`: the bottom frame keeps index `i0`), so the potential at both boundaries is read with ONE table:
  `potRest (.ewig _ (n + 1) …) = potRest (.ewig _ n …) + one pass`.
-/
import Grammatik.Logik.Fortschritt.KostenG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Segments that remember the index of their bottom frame -/

/-- The frames from the head down to the entry frame, each with its index, the entry frame (the LAST one) at
    index `i0`, and their total potential. -/
inductive SegU {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa : Nat) (i0 : ι) :
    List (RufRahmenG D) → Nat → Prop where
  | eins (r : RufRahmenG D) (hok : rufeR (S i0) (fun _ => false) r.rest.2.2.2.2 = true) :
      SegU T S pa i0 [r] (potRest (T i0) pa r.rest.2.2.2.2)
  | cons (r : RufRahmenG D) (i : ι) (rs : List (RufRahmenG D)) (p : Nat)
      (hok : rufeR (S i) (fun _ => false) r.rest.2.2.2.2 = true) (h : SegU T S pa i0 rs p) :
      SegU T S pa i0 (r :: rs) (potRest (T i) pa r.rest.2.2.2.2 + p)

/-- **The invariant**: as `KInv`, with the entry frame's index kept. -/
def DInv {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa B : Nat) (i0 : ι) (f : Faden)
    (k : Nat) (M : RufMaschineG D) (n : Nat) : Prop :=
  ∃ (oben unten : List (RufRahmenG D)) (Φ : Nat),
    (M.faeden f).stapel = oben ++ unten ∧ unten.length = k ∧
    SegU T S pa i0 ((M.faeden f).kopf :: oben) Φ ∧ n + Φ ≤ B

section Motor

variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
  (P : Programm D) (O : Orakel D) (pa : Nat)

theorem segU_pos {i0 : ι} : ∀ {rs : List (RufRahmenG D)} {Φ : Nat}, SegU T S pa i0 rs Φ → rs ≠ []
  | _, _, .eins .. => List.cons_ne_nil _ _
  | _, _, .cons .. => List.cons_ne_nil _ _

/-- **The engine step**, keeping the entry frame's index. -/
theorem dinv_schritt
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) (P.rumpf g) = true)
    {B : Nat} {i0 : ι} {f : Faden} {k : Nat} {M M' : RufMaschineG D} {n : Nat} {g : Faden}
    (hI : DInv T S pa B i0 f k M n) (hs : RufSchrittG P O pa M g M') :
    n + (if g = f then 1 else 0) ≤ B ∧
    (k ≤ (M'.faeden f).stapel.length →
      DInv T S pa B i0 f k M' (n + (if g = f then 1 else 0))) := by
  by_cases hgf : g = f
  · subst hgf
    simp only [if_true]
    obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI
    cases hseg with
    | eins _ hok =>
      -- the entry frame alone: index `i0`
      rcases schrittArt hs (T i0) (S i0) (fun _ => false) with
        ⟨hst', hA⟩ | ⟨g', caller', rho, s0, hst', hk', hB'⟩ | ⟨caller, rst, hpop, hst', hC⟩
      · obtain ⟨hok', hpot⟩ := hA hok
        exact ⟨by omega, fun _ => ⟨[], unten, _, by rw [hst', hst], hul, SegU.eins _ hok', by omega⟩⟩
      · obtain ⟨hokc, hdir⟩ := hB' hok
        obtain ⟨hZ, hpot⟩ := hdir.resolve_right (fun ⟨_, hn, _⟩ => Bool.false_ne_true hn)
        have h1 := hS1 i0 g' hZ
        have h2 := hS2 i0 g' hZ
        refine ⟨by omega, fun _ => ⟨[caller'], unten,
          kostenEnd (T (nx i0 g')) pa (P.rumpf g') + potRest (T i0) pa caller'.rest.2.2.2.2,
          by rw [hst', hst]; rfl, hul, ?_, by omega⟩⟩
        rw [hk']
        exact SegU.cons _ (nx i0 g') _ _ h2 (SegU.eins caller' hokc)
      · have hpos := potRest_pos (T i0) pa (M.faeden g).kopf.rest.2.2.2.2
        refine ⟨by omega, fun hk => ?_⟩
        rw [hst, List.nil_append] at hpop
        rw [hpop] at hul
        rw [hst'] at hk
        simp only [List.length_cons] at hul
        omega
    | cons _ i _ p hok hrest =>
      rcases schrittArt hs (T i) (S i) (fun _ => false) with
        ⟨hst', hA⟩ | ⟨g', caller', rho, s0, hst', hk', hB'⟩ | ⟨caller, rst, hpop, hst', hC⟩
      · obtain ⟨hok', hpot⟩ := hA hok
        exact ⟨by omega, fun _ => ⟨oben, unten, _, by rw [hst', hst], hul, SegU.cons _ i oben p hok' hrest,
          by omega⟩⟩
      · obtain ⟨hokc, hdir⟩ := hB' hok
        obtain ⟨hZ, hpot⟩ := hdir.resolve_right (fun ⟨_, hn, _⟩ => Bool.false_ne_true hn)
        have h1 := hS1 i g' hZ
        have h2 := hS2 i g' hZ
        refine ⟨by omega, fun _ => ⟨caller' :: oben, unten,
          kostenEnd (T (nx i g')) pa (P.rumpf g') + (potRest (T i) pa caller'.rest.2.2.2.2 + p),
          by rw [hst', hst]; rfl, hul, ?_, by omega⟩⟩
        rw [hk']
        exact SegU.cons _ (nx i g') _ _ h2 (SegU.cons caller' i oben p hokc hrest)
      · have hpos := potRest_pos (T i) pa (M.faeden g).kopf.rest.2.2.2.2
        refine ⟨by omega, fun _ => ?_⟩
        cases oben with
        | nil => exact absurd rfl (segU_pos T S pa hrest)
        | cons o oben' =>
          rw [hst] at hpop
          simp only [List.cons_append, List.cons.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          cases hrest with
          | eins _ hokj =>
            obtain ⟨hokc, hpotc⟩ := hC (T i0) (S i0) (fun _ => false)
            refine ⟨[], unten, _, hst', hul, SegU.eins _ (hokc hokj), ?_⟩
            omega
          | cons _ j _ q hokj hrest' =>
            obtain ⟨hokc, hpotc⟩ := hC (T j) (S j) (fun _ => false)
            refine ⟨oben', unten, _, hst', hul, SegU.cons _ j oben' q (hokc hokj) hrest', ?_⟩
            omega
  · simp only [hgf, ite_false, Nat.add_zero]
    have hEq : M'.faeden f = M.faeden f := rufSchrittG_fremd hs f (Ne.symm hgf)
    obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI
    refine ⟨by omega, fun _ => ⟨oben, unten, Φ, ?_, hul, ?_, hB⟩⟩
    · rw [hEq]; exact hst
    · rw [hEq]; exact hseg

/-- **The engine over a run**, keeping the entry frame's index. -/
theorem dinv_lauf
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) (P.rumpf g) = true)
    {B : Nat} {i0 : ι} {f : Faden} {k : Nat} {M1 : RufMaschineG D}
    (h0 : DInv T S pa B i0 f k M1 0) :
    ∀ {M2 : RufMaschineG D} (run : SegLauf P O pa M1 M2), aktivVor f k run →
      segZaehle run f ≤ B ∧
      (k ≤ (M2.faeden f).stapel.length → DInv T S pa B i0 f k M2 (segZaehle run f)) := by
  intro M2 run
  induction run with
  | start =>
    intro _
    refine ⟨?_, fun _ => h0⟩
    obtain ⟨_, _, _, _, _, _, hB⟩ := h0
    simp only [segZaehle]
    omega
  | schritt M M' g run' hs ih =>
    intro hA
    obtain ⟨hA', hk⟩ := hA
    exact dinv_schritt T S nx P O pa hS1 hS2 ((ih hA').2 hk) hs

end Motor

/-! ## 2. One pass -/

section Durchgang

variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
  (P : Programm D) (O : Orakel D) (pa : Nat)

/-- The cost of one pass of a `forever` loop. -/
def passKosten (c : D.Fn → Nat) {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) : Nat :=
  kostenBlock c pa body + kostenExpr inv + 2

/-- **T3 -- EVERY PASS IS BOUNDED.** Thread `f`'s head frame (function `g`, parameters `rho`, entry world `s0`,
    `kk` frames below it) stands at the boundary `.ewig a (n + 1) inv body k` of a loop whose residue is admitted
    at index `i0`. On every run on which the frame stays active and which ends with the SAME frame at the next
    boundary `.ewig a n inv body k`, the thread takes at most one pass's cost of own steps. -/
theorem durchgang_schritte
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) (P.rumpf g) = true)
    {f : Faden} {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D} {kk : Nat}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {a : D.Annahme} {n : Nat}
    {inv : Expr D Γ Λ .bool} {body : Block D (vertragVon D g) true Γ Λ Λ}
    {k : GRest D (vertragVon D g) l Γ Λ} {ρ1 ρ2 : Env D Γ} {M1 M2 : RufMaschineG D} (i0 : ι)
    (h1 : (M1.faeden f).kopf = ⟨g, rho, s0, ⟨l, Γ, Λ, ρ1, .ewig a (n + 1) inv body k⟩⟩)
    (hl1 : (M1.faeden f).stapel.length = kk)
    (hok : rufeR (S i0) (fun _ => false) (GRest.ewig a (n + 1) inv body k) = true)
    (run : SegLauf P O pa M1 M2) (hA : aktivVor f kk run)
    (h2 : (M2.faeden f).kopf = ⟨g, rho, s0, ⟨l, Γ, Λ, ρ2, .ewig a n inv body k⟩⟩)
    (hl2 : (M2.faeden f).stapel.length = kk) :
    segZaehle run f ≤ passKosten pa (T i0) inv body := by
  -- the invariant at the boundary, budget = the potential there
  have h0 : DInv T S pa (potRest (T i0) pa (GRest.ewig a (n + 1) inv body k)) i0 f kk M1 0 := by
    have hs := SegU.eins (T := T) (S := S) (pa := pa) (i0 := i0) (M1.faeden f).kopf (by rw [h1]; exact hok)
    rw [h1] at hs
    refine ⟨[], (M1.faeden f).stapel, _, rfl, hl1, ?_, Nat.le_of_eq (Nat.zero_add _)⟩
    rw [h1]
    exact hs
  obtain ⟨_, hI⟩ := dinv_lauf T S nx P O pa hS1 hS2 h0 run hA
  obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI (Nat.le_of_eq hl2.symm)
  -- the same stack height: nothing above the frame
  have hoben : oben = [] := by
    have := congrArg List.length hst
    rw [List.length_append, hl2, hul] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hoben
  rw [h2] at hseg
  cases hseg with
  | eins _ _ =>
    simp only [potRest, passKosten] at hB ⊢
    rw [Nat.succ_mul] at hB
    omega
  | cons _ _ _ _ _ hrest => exact absurd rfl (segU_pos T S pa hrest)

end Durchgang

end Gabbro.Grammatik
