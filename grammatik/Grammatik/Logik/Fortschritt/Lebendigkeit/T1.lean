/-
  File:      Grammatik/Lebendigkeit.lean
  Subject:   A WAITING BOUND ON MACHINE G (PLAN-ZIELSATZ §8, liveness; KostenG
             TARGET 4): a thread standing at `locks L` takes `L` within
             `wartezeit L` scheduler steps -- under ONE named runtime assumption
             (a FIFO/ticket lock and a scheduler with fairness window `F`), a
             hold-time premise, and the facts the goal theorem supplies.

  THE RUNTIME ASSUMPTION (one entry of the ONE assumption list,
  `LaufzeitAnnahme R F`):
  * `FifoSperre R` -- a FIFO/ticket lock: the thread that takes `L` has stood
    at `locks L` at least since every other thread now standing there
    arrived. (Ties at the start machine are allowed either way.)
  * `FairF R F` -- bounded fairness: a thread that can step at every one of
    `F` consecutive scheduler steps takes one of them. `F` is a named
    constant of the scheduler (round robin over `T` runnable threads with one
    G step per turn: `F = T`).
  Runs are INFINITE (`PlanLauf`): a scheduler step is a step of machine G, or
  a stutter at a machine where no thread can step (a finished program). A
  stutter changes nothing.

  THE HOLD-TIME PREMISE (`Haltezeit R h k`): on every stretch of the run on
  which thread `u` holds `L`, `u` takes at most `h L` own steps, at most
  `k L` of them at a `locks` head (nested acquisitions). It is a PREMISE on
  the run, NOT derived: the checker decides `held <= N ops` (`K002`,
  kosten.rs `sperrbloecke`) in OPERATIONS with callees at their declared
  `costs`, and two bridges are missing -- (1) operations to G steps (KostenG
  TARGET 3 found that G takes steps the checker prices at `0`, findings
  F1-F9; `spiegel_stmt` goes the other way with a remainder `zusatz`), and
  (2) a bound for the `locks` BODY as a residue segment: `frame_schritte_
  beschraenkt` bounds a FRAME from entry to return (`Eintritt`/`aktivVor`),
  and a `locks` body is not a frame; its potential would have to be carried
  through the residue `.dann body (.frei L k)` across all 72 rules.

  THE BOUND, recursive over ranks (`wF`, fuel = the number of locks):
    S(L) = h(L)·F + k(L)·Wn(L)          one critical section of `L`
    Wn(L) = max { W(L') | rang L < rang L' }   a nested wait
    W(L) = (c(L) - 1)·(S(L) + F) + F     `c(L)` = the contenders for `L`
  Each own step of the holder is preceded by at most `F` scheduler steps
  (fairness) or, if it is a nested acquisition, by at most `Wn(L)` (the
  bound one rank up -- the holder stands at `locks L'` with `rang L < rang L'`
  by the rank invariant); a waiting thread sees at most `c(L) - 1` sections
  before its own (FIFO: every thread ahead of it takes `L` at most once),
  each followed by a free gap of fewer than `F` steps.

  THEOREMS.
  * `wartezeit_kern`: under `LaufzeitAnnahme`, `Haltezeit`, `AbschnittAktiv`
    (a lock holder can step or stands at a `locks` head), `Anwaerter`
    (the contenders), the rank invariant and lock exclusivity along the
    run: a thread at `locks L` at step `n0` takes `L` at a step
    `j < n0 + wartezeit L`, and holds `L` after it.
  * `wartezeit_schranke`: the same from the goal theorem's premises
    (`GutO`, `StufenM`, starts without signature locks, the run starting at a
    reachable machine, `KeinLogikHaltG` along the run -- a conjunct of
    `Ziel` -- and `BereichG` along the run, every float range check passes,
    from the body obligation, `bereichG_erreichbarL`) plus
    `HardwareImAbschnitt` (no named stop of any kind inside a critical
    section).
  * Machine-G facts used: `sperre_schritt` (a step at a `locks L` head takes
    `L`, and only if it is free), `schritt_sperre_art` (a step either stands
    at a `locks` head or does not grow the held set), `nimmt_an_sperre`.

  No `sorry`, no `axiom`, no `native_decide`; machine G and Spec.lean are
  unchanged.
-/
import Grammatik.Logik.Fortschritt.Fortschritt

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Scheduled runs -/

section Lauf

variable (P : Programm D) (O : Orakel D) (passes : Nat)

/-- Thread `t` can step at `M`. -/
def Bereit (M : RufMaschineG D) (t : Faden) : Prop := ∃ M', RufSchrittG P O passes M t M'

/-- **A scheduled run**: an infinite sequence of machines; at every scheduler
    step either thread `u` takes a step of machine G (`akt n = some u`), or the
    machine stutters (`akt n = none`), which is allowed only where no thread
    can step. -/
structure PlanLauf where
  M : Nat → RufMaschineG D
  akt : Nat → Option Faden
  schritt : ∀ n u, akt n = some u → RufSchrittG P O passes (M n) u (M (n + 1))
  stotter : ∀ n, akt n = none → M (n + 1) = M n ∧ ∀ u, ¬ Bereit P O passes (M n) u

end Lauf
/-! ## 2. Counting on a run -/

open Classical in
/-- The number of `j ∈ [a, a + n)` with `p j`. -/
noncomputable def zaehl (p : Nat → Prop) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => zaehl p a n + if p (a + n) then 1 else 0

open Classical in
theorem zaehl_add (p : Nat → Prop) (a n : Nat) :
    ∀ m, zaehl p a (n + m) = zaehl p a n + zaehl p (a + n) m
  | 0 => rfl
  | m + 1 => by
      have h1 : zaehl p a (n + (m + 1)) = zaehl p a (n + m) + (if p (a + (n + m)) then 1 else 0) :=
        rfl
      have h2 : zaehl p (a + n) (m + 1) = zaehl p (a + n) m + (if p (a + n + m) then 1 else 0) :=
        rfl
      rw [h1, h2, zaehl_add p a n m, Nat.add_assoc a n m]
      omega

theorem zaehl_pos (p : Nat → Prop) (a : Nat) :
    ∀ n i, i < n → p (a + i) → 1 ≤ zaehl p a n
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h, hp => by
      show 1 ≤ zaehl p a n + _
      by_cases hi : i = n
      · subst hi; rw [if_pos hp]; omega
      · have := zaehl_pos p a n i (by omega) hp
        omega

theorem zaehl_le (p : Nat → Prop) (a : Nat) : ∀ n, zaehl p a n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
      have := zaehl_le p a n
      show zaehl p a n + _ ≤ n + 1
      split <;> omega

theorem zaehl_null (p : Nat → Prop) (a : Nat) :
    ∀ n, (∀ i, i < n → ¬ p (a + i)) → zaehl p a n = 0
  | 0, _ => rfl
  | n + 1, h => by
      show zaehl p a n + _ = 0
      rw [zaehl_null p a n (fun i hi => h i (by omega)), if_neg (h n (by omega))]

open Classical in
/-- The number of list elements with `p`. -/
noncomputable def anz {α : Type} (p : α → Prop) : List α → Nat
  | [] => 0
  | a :: l => anz p l + if p a then 1 else 0

theorem anz_mono {α : Type} (p q : α → Prop) :
    ∀ l : List α, (∀ x ∈ l, p x → q x) → anz p l ≤ anz q l
  | [], _ => Nat.le_refl _
  | a :: l, h => by
      have ih := anz_mono p q l (fun x hx => h x (List.mem_cons_of_mem _ hx))
      show anz p l + _ ≤ anz q l + _
      by_cases hp : p a
      · rw [if_pos hp, if_pos (h a List.mem_cons_self hp)]; omega
      · rw [if_neg hp]; split <;> omega

theorem anz_lt {α : Type} (p q : α → Prop) :
    ∀ l : List α, (∀ x ∈ l, p x → q x) → (∃ x ∈ l, q x ∧ ¬ p x) → anz p l < anz q l
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, h, ⟨x, hx, hq, hp⟩ => by
      have h' : ∀ y ∈ l, p y → q y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hle := anz_mono p q l h'
      show anz p l + _ < anz q l + _
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [if_neg hp, if_pos hq]; omega
      · have := anz_lt p q l h' ⟨x, hx', hq, hp⟩
        by_cases hpa : p a
        · rw [if_pos hpa, if_pos (h a List.mem_cons_self hpa)]; omega
        · rw [if_neg hpa]; split <;> omega

theorem anz_le_len {α : Type} (p : α → Prop) : ∀ l : List α, anz p l ≤ l.length
  | [] => Nat.le_refl _
  | a :: l => by
      have := anz_le_len p l
      show anz p l + _ ≤ l.length + 1
      split <;> omega

theorem anz_lt_len {α : Type} (p : α → Prop) (l : List α) (h : ∃ x ∈ l, ¬ p x) :
    anz p l < l.length := by
  have e : ∀ l' : List α, anz (fun _ => True) l' = l'.length := by
    intro l'
    induction l' with
    | nil => rfl
    | cons a l' ih => show anz _ l' + _ = l'.length + 1; rw [ih, if_pos trivial]
  rw [← e l]
  obtain ⟨x, hx, hp⟩ := h
  exact anz_lt p (fun _ => True) l (fun _ _ _ => trivial) ⟨x, hx, trivial, hp⟩

theorem anz_pos {α : Type} (p : α → Prop) : ∀ l : List α, (∃ x ∈ l, p x) → 1 ≤ anz p l
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, ⟨x, hx, hp⟩ => by
      show 1 ≤ anz p l + _
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [if_pos hp]; omega
      · have := anz_pos p l ⟨x, hx', hp⟩; omega

/-- The first `j` in a window with `p j`. -/
theorem erster (p : Nat → Prop) (m : Nat) : ∀ B, (∃ j, m ≤ j ∧ j < m + B ∧ p j) →
    ∃ j, m ≤ j ∧ j < m + B ∧ p j ∧ ∀ i, m ≤ i → i < j → ¬ p i
  | 0, ⟨_, h1, h2, _⟩ => absurd h2 (by omega)
  | B + 1, h => by
      by_cases hB : ∃ j, m ≤ j ∧ j < m + B ∧ p j
      · obtain ⟨j, h1, h2, h3, h4⟩ := erster p m B hB
        exact ⟨j, h1, by omega, h3, h4⟩
      · obtain ⟨j, h1, h2, h3⟩ := h
        have hj : j = m + B :=
          Classical.byContradiction fun hne => hB ⟨j, h1, by omega, h3⟩
        subst hj
        exact ⟨m + B, h1, by omega, h3, fun i hi1 hi2 hpi => hB ⟨i, hi1, hi2, hpi⟩⟩

/-! ## 3. The bound, recursive over ranks -/

/-- The largest `f L'` over the locks of `ls` ranking above `L` (`0` if none). -/
def wMaxH (L : D.Lock) (f : D.Lock → Nat) : List D.Lock → Nat
  | [] => 0
  | a :: l => max (if D.rang L < D.rang a then f a else 0) (wMaxH L f l)

theorem le_wMaxH (L : D.Lock) (f : D.Lock → Nat) :
    ∀ (ls : List D.Lock) (L' : D.Lock), L' ∈ ls → D.rang L < D.rang L' → f L' ≤ wMaxH L f ls
  | [], _, h, _ => absurd h List.not_mem_nil
  | a :: l, L', h, hr => by
      show f L' ≤ max _ (wMaxH L f l)
      rcases List.mem_cons.mp h with rfl | h'
      · rw [if_pos hr]; exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_wMaxH L f l L' h' hr) (Nat.le_max_right _ _)

/-- **The waiting bound with fuel `n`** (the fuel counts rank levels):
    `wF (n+1) L = (c L - 1) * (h L * F + k L * Wn + F) + F`, where `Wn` is
    the largest bound one fuel level down over the locks ranking above `L`
    and `c L = (Ts L).length` the number of contenders. -/
def wF (ls : List D.Lock) (Ts : D.Lock → List Faden) (h k : D.Lock → Nat) (F : Nat) :
    Nat → D.Lock → Nat
  | 0, _ => 0
  | n + 1, L =>
      ((Ts L).length - 1) * (h L * F + k L * wMaxH L (wF ls Ts h k F n) ls + F) + F

/-- **The waiting bound**: `wF` at fuel `ls.length` (enough: every chain of
    strictly rising ranks in `ls` is shorter). -/
def wartezeit (ls : List D.Lock) (Ts : D.Lock → List Faden) (h k : D.Lock → Nat) (F : Nat)
    (L : D.Lock) : Nat :=
  wF ls Ts h k F ls.length L

/-- The number of locks of `ls` ranking above `L` -- the recursion measure. -/
noncomputable def hoeher (ls : List D.Lock) (L : D.Lock) : Nat :=
  anz (fun L' => D.rang L < D.rang L') ls

theorem hoeher_lt (ls : List D.Lock) {L L' : D.Lock} (hL' : L' ∈ ls)
    (hr : D.rang L < D.rang L') : hoeher ls L' < hoeher ls L :=
  anz_lt _ _ ls (fun _ _ h => Int.lt_trans hr h) ⟨L', hL', hr, Int.lt_irrefl _⟩

theorem hoeher_lt_len (ls : List D.Lock) {L : D.Lock} (hL : L ∈ ls) : hoeher ls L < ls.length :=
  anz_lt_len _ ls ⟨L, hL, Int.lt_irrefl _⟩

/-! ## 4. Machine G at a `locks` head -/

section MaschineG

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem Stmt.blatt_sperreVon {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : s.istBlatt = true) : s.sperreVon = none := by
  cases s <;> simp_all [Stmt.istBlatt, Stmt.sperreVon]

/-- A thread stands at `locks L` for at most one `L`. -/
theorem anSperre_eindeutig {M : RufMaschineG D} {t : Faden} {L L' : D.Lock}
    (h : AnSperre M t L) (h' : AnSperre M t L') : L = L' := by
  have e := (anSperre_kopf h).symm.trans (anSperre_kopf h')
  exact Option.some.inj e

/-- `AnSperre` reads only the thread's own state. -/
theorem anSperre_gleich {M M' : RufMaschineG D} {t : Faden} {L : D.Lock}
    (h : M'.faeden t = M.faeden t) (hA : AnSperre M t L) : AnSperre M' t L := by
  unfold AnSperre at *
  rw [h]
  exact hA

set_option maxHeartbeats 4000000 in
/-- **A step at a `locks L` head takes `L`, and fires only if `L` is free**:
    every rule but `dannLocks` has a head that is no `locks` statement. -/
theorem sperre_schritt {M M' : RufMaschineG D} {t : Faden} {L : D.Lock}
    (hA : AnSperre M t L) (hs : RufSchrittG P O passes M t M') :
    RufFreiG M t L ∧
      (M'.faeden t).spur = Ereignis.nimmt L (offen (M.faeden t).spur) :: (M.faeden t).spur := by
  have hK := anSperre_kopf hA
  cases hs with
  | dannLocks l Γ Λ Λ'' L' hr body rest k ρ hhead hself hrang hfrei =>
      rw [hhead] at hK
      simp only [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon, Option.some.injEq] at hK
      subst hK
      exact ⟨hfrei, by simp only [rufUpdateG_self]⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead =>
      exfalso
      rw [hhead] at hK
      simp only [GRest.kopfSperre, Block.sperreVon, Stmt.blatt_sperreVon s hleaf] at hK
      cases hK
  | _ =>
      exfalso
      rw [‹(M.faeden t).kopf.rest = _›] at hK
      simp [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon] at hK

set_option maxHeartbeats 4000000 in
/-- **What a step does to the held set, with the `locks` head named**: the
    actor stands at a `locks` head (then `sperre_schritt` says what happens),
    or its held set is unchanged, or one lock is released. The twin of
    `offen_schrittG` (ZielOrt.lean), whose take case does not name the head. -/
theorem schritt_sperre_art (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') :
    (∃ L, AnSperre M f L) ∨ offen (M'.faeden f).spur = offen (M.faeden f).spur ∨
    (∃ L, offen (M'.faeden f).spur = (offen (M.faeden f).spur).erase L) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf _ hΛ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inl (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead _ _ _ =>
      exact Or.inl ⟨L, l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩
  | freiGib l Γ Λ L k ρ hhead =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨L, rfl⟩)
  | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨L, rfl⟩)
  | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
      simp only [rufUpdateG_self]
      exact Or.inr (Or.inr ⟨L, rfl⟩)
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [hs₁, lese_offen, leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [next_welt' _ _ _ _ _ _ _ _ hstep]
      rfl
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [hs₂, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ r hax =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ v hax =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ r hax =>
      simp only [rufUpdateG_self]
      refine Or.inr (Or.inl ?_)
      rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
      exact lese_offen _ _ _
  | _ =>
      subst_vars
      simp only [rufUpdateG_self]
      first
        | exact Or.inr (Or.inl trivial)
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inl (lese_offen _ _ _))

/-- **A lock enters a held set only at a `locks` head of that lock.** -/
theorem nimmt_an_sperre (hO : GutO O) {M M' : RufMaschineG D} {f : Faden} {L : D.Lock}
    (hs : RufSchrittG P O passes M f M') (h0 : L ∉ offen (M.faeden f).spur)
    (h1 : L ∈ offen (M'.faeden f).spur) : AnSperre M f L := by
  rcases schritt_sperre_art hO hs with ⟨L', hA⟩ | e | ⟨L', e⟩
  · have e := (sperre_schritt hA hs).2
    rw [e] at h1
    simp only [offen, List.mem_cons] at h1
    rcases h1 with rfl | h1
    · exact hA
    · exact absurd h1 h0
  · rw [e] at h1; exact absurd h1 h0
  · rw [e] at h1; exact absurd (List.mem_of_mem_erase h1) h0

/-- A `locks L` head read off the residue is a `locks L` head. -/
theorem anSperre_of_kopf {M : RufMaschineG D} {t : Faden} {L : D.Lock}
    (h : (M.faeden t).kopf.rest.2.2.2.2.kopfSperre = some L) : AnSperre M t L := by
  unfold AnSperre
  generalize (M.faeden t).kopf.rest = x at h ⊢
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  cases r with
  | dann b k =>
      cases b with
      | cons s rest =>
          cases s with
          | locks L' hr body =>
              simp only [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon,
                Option.some.injEq] at h
              subst h
              exact ⟨l, Γ, Λ, _, ρ, hr, body, rest, k, rfl⟩
          | _ => simp [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon] at h
      | _ => simp [GRest.kopfSperre, Block.sperreVon] at h
  | _ => simp [GRest.kopfSperre] at h

/-- A thread at `locks L` while another thread holds `L` cannot step. -/
theorem nicht_bereit_an_sperre {M : RufMaschineG D} {t u : Faden} {L : D.Lock}
    (hA : AnSperre M t L) (hu : u ≠ t) (hL : L ∈ offen (M.faeden u).spur) :
    ¬ ∃ M', RufSchrittG P O passes M t M' :=
  fun ⟨_, hs⟩ => (sperre_schritt hA hs).1 u hu hL

/-- The residue is a plain `return` end block. -/
def GRest.istEndeRet {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende (.ret ..) => true
  | _ => false

set_option maxHeartbeats 4000000 in
/-- **A finished thread cannot step**: an empty stack under a `return` head
    -- every pop needs a caller, and no other rule has that head. -/
theorem ende_ret_kein_schritt {M M' : RufMaschineG D} {t : Faden}
    (hst : (M.faeden t).stapel = [])
    (hk : (M.faeden t).kopf.rest.2.2.2.2.istEndeRet = true)
    (hs : RufSchrittG P O passes M t M') : False := by
  cases hs with
  | rueck caller rest hpop => rw [hst] at hpop; cases hpop
  | rueckBind caller rest hpop => rw [hst] at hpop; cases hpop
  | _ =>
      rw [‹(M.faeden t).kopf.rest = _›] at hk
      simp [GRest.istEndeRet] at hk

/-- A named hardware stop, read off the head residue. -/
theorem halt_kopf {M : RufMaschineG D} {t : Faden} {k : Zielsatz.HaltArt}
    (h : Zielsatz.HaltBenannt O passes M k t) :
    Zielsatz.RestHalt O passes (M.weltVon t) (M.faeden t).kopf.rest.2.2.2.1 k
      (M.faeden t).kopf.rest.2.2.2.2 := by
  obtain ⟨l, Γ, Λ, ρ, r, he, hr⟩ := h
  rw [he]
  exact hr

end MaschineG
/-! ## 5. The runtime assumption and the premises, on a run -/

section Annahmen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **A FIFO (ticket) lock.** If thread `t` stands at `locks L` at every
    scheduler step from `a` to `n`, and thread `u` takes `L` at step `n`
    (it acts standing at `locks L`), then `u` has stood there since `a`
    too: nobody overtakes a waiting thread. -/
def FifoSperre (R : PlanLauf P O passes) : Prop :=
  ∀ (t u : Faden) (L : D.Lock) (a n : Nat), t ≠ u →
    (∀ j, a ≤ j → j ≤ n → AnSperre (R.M j) t L) →
    R.akt n = some u → AnSperre (R.M n) u L →
    ∀ j, a ≤ j → j ≤ n → AnSperre (R.M j) u L

/-- **Bounded fairness with window `F`.** A thread that can step at each of
    the `F` scheduler steps from `n` on takes one of them. (`F = 0` is
    unsatisfiable: the window is empty.) -/
def FairF (R : PlanLauf P O passes) (F : Nat) : Prop :=
  ∀ (t : Faden) (n : Nat), (∀ j, n ≤ j → j < n + F → Bereit P O passes (R.M j) t) →
    ∃ j, n ≤ j ∧ j < n + F ∧ R.akt j = some t

/-- **THE RUNTIME ASSUMPTION for the waiting bound** -- the entry "a FIFO or
    ticket lock for the waiting bound" of the ONE assumption list
    (PLAN-ZIELSATZ §8), together with the scheduler's fairness window `F`. -/
def LaufzeitAnnahme (R : PlanLauf P O passes) (F : Nat) : Prop :=
  FifoSperre R ∧ FairF R F

/-- **The hold-time premise.** On every stretch of `n` scheduler steps from
    `a` on which thread `u` holds `L`, `u` takes at most `h L` own steps, at
    most `k L` of them at a `locks` head. -/
def Haltezeit (R : PlanLauf P O passes) (h k : D.Lock → Nat) : Prop :=
  ∀ (u : Faden) (L : D.Lock) (a n : Nat),
    (∀ i, i < n → L ∈ offen ((R.M (a + i)).faeden u).spur) →
    zaehl (fun j => R.akt j = some u) a n ≤ h L ∧
    zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') a n ≤ k L

/-- A lock holder can step or stands at a `locks` head (no other stop inside
    a critical section). Derived from progress in `abschnittAktiv_aus`. -/
def AbschnittAktiv (R : PlanLauf P O passes) : Prop :=
  ∀ n u L, L ∈ offen ((R.M n).faeden u).spur →
    Bereit P O passes (R.M n) u ∨ ∃ L', AnSperre (R.M n) u L'

/-- **The contenders for `L`**: every thread that ever holds `L` or stands
    at `locks L` on the run is in `Ts L`. -/
def Anwaerter (R : PlanLauf P O passes) (Ts : D.Lock → List Faden) : Prop :=
  ∀ n u L, (L ∈ offen ((R.M n).faeden u).spur ∨ AnSperre (R.M n) u L) → u ∈ Ts L

/-- **No named stop inside a critical section**, of any kind (`Zielsatz.HaltArt`): devices
    and axioms answer, `awaits` payloads become visible, the `forever` budget is not spent
    while a lock is held. -/
def HardwareImAbschnitt (R : PlanLauf P O passes) : Prop :=
  ∀ n u L, L ∈ offen ((R.M n).faeden u).spur → ∀ k, ¬ Zielsatz.HaltBenannt O passes (R.M n) k u

end Annahmen
/-! ## 6. Runs: frozen threads -/


