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
import Grammatik.Fortschritt

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

section Kern

variable {P : Programm D} {O : Orakel D} {passes : Nat} (R : PlanLauf P O passes)

theorem PlanLauf.fremd (n : Nat) (u : Faden) (h : R.akt n ≠ some u) :
    (R.M (n + 1)).faeden u = (R.M n).faeden u := by
  cases ha : R.akt n with
  | none => rw [(R.stotter n ha).1]
  | some v =>
      have hvu : u ≠ v := fun e => h (by rw [ha, e])
      exact rufSchrittG_fremd (R.schritt n v ha) u hvu

theorem PlanLauf.stet {u : Faden} {m : Nat} :
    ∀ d, (∀ i, m ≤ i → i < m + d → R.akt i ≠ some u) →
      (R.M (m + d)).faeden u = (R.M m).faeden u
  | 0, _ => rfl
  | d + 1, h => by
      show (R.M (m + d + 1)).faeden u = _
      rw [R.fremd (m + d) u (h (m + d) (by omega) (by omega))]
      exact PlanLauf.stet d (fun i h1 h2 => h i h1 (by omega))

theorem PlanLauf.stet' {u : Faden} {m j : Nat} (hmj : m ≤ j)
    (h : ∀ i, m ≤ i → i < j → R.akt i ≠ some u) :
    (R.M j).faeden u = (R.M m).faeden u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmj
  exact R.stet d h

theorem PlanLauf.erreichbar {M0 : RufMaschineG D} (h0 : RufErreichbarG P O passes M0 (R.M 0)) :
    ∀ n, RufErreichbarG P O passes M0 (R.M n)
  | 0 => h0
  | n + 1 => by
      cases ha : R.akt n with
      | none => rw [(R.stotter n ha).1]; exact PlanLauf.erreichbar h0 n
      | some u => exact .schritt _ _ u (PlanLauf.erreichbar h0 n) (R.schritt n u ha)

variable {ls : List D.Lock} {Ts : D.Lock → List Faden} {h k : D.Lock → Nat} {F : Nat}

/-! ## 7. The core -/

section Beweis

variable (hO : GutO O) (hls : ∀ L : D.Lock, L ∈ ls)
  (hRang : ∀ n t, ∃ w, RangInvG w ((R.M n).faeden t))
  (hEx : ∀ n (f g : Faden), f ≠ g → ∀ L : D.Lock,
    L ∈ offen ((R.M n).faeden f).spur → L ∉ offen ((R.M n).faeden g).spur)
  (hFifo : FifoSperre R) (hFair : FairF R F) (hH : Haltezeit R h k)
  (hAkt : AbschnittAktiv R) (hAnw : Anwaerter R Ts)

include hRang in
theorem an_sperre_frei {n : Nat} {t : Faden} {L : D.Lock} (hA : AnSperre (R.M n) t L) :
    L ∉ offen ((R.M n).faeden t).spur := by
  obtain ⟨w, hw⟩ := hRang n t
  exact (sperre_rang hw hA).1

include hRang in
theorem innen_hoeher {n : Nat} {t : Faden} {L L' : D.Lock}
    (hL : L ∈ offen ((R.M n).faeden t).spur) (hA : AnSperre (R.M n) t L') :
    D.rang L < D.rang L' := by
  obtain ⟨w, hw⟩ := hRang n t
  exact (sperre_rang hw hA).2 L hL

/-- The first own step of `u` in a window, with `u`'s state frozen up to it. -/
theorem erster_schritt {u : Faden} {m B : Nat}
    (h : ∃ j, m ≤ j ∧ j < m + B ∧ R.akt j = some u) :
    ∃ j, m ≤ j ∧ j < m + B ∧ R.akt j = some u ∧
      ∀ i, m ≤ i → i ≤ j → (R.M i).faeden u = (R.M m).faeden u := by
  obtain ⟨j, h1, h2, h3, h4⟩ := erster (fun j => R.akt j = some u) m B h
  exact ⟨j, h1, h2, h3, fun i hi1 hi2 =>
    R.stet' hi1 (fun i' h1' h2' => h4 i' h1' (by omega))⟩

include hRang hFair hAkt in
/-- **The gap before the holder's next own step.** A thread holding a lock
    takes its next step within `F` scheduler steps -- or, if it stands at a
    `locks L'` head (then `L'` ranks above every lock it holds), within the
    waiting bound `G` of the locks ranking above `L`. -/
theorem luecke {G : Nat} {L : D.Lock}
    (hV : ∀ L', D.rang L < D.rang L' → ∀ t n, AnSperre (R.M n) t L' →
      ∃ j, n ≤ j ∧ j < n + G ∧ R.akt j = some t)
    {u : Faden} {m : Nat} (hm : L ∈ offen ((R.M m).faeden u).spur) :
    ∃ j, m ≤ j ∧ R.akt j = some u ∧
      (∀ i, m ≤ i → i ≤ j → (R.M i).faeden u = (R.M m).faeden u) ∧
      ((∃ L', AnSperre (R.M m) u L') → j < m + G) ∧
      ((¬ ∃ L', AnSperre (R.M m) u L') → j < m + F) := by
  by_cases hA : ∃ L', AnSperre (R.M m) u L'
  · obtain ⟨L', hA'⟩ := hA
    have hr := innen_hoeher R hRang hm hA'
    obtain ⟨j, h1, h2, h3, h4⟩ := erster_schritt R (hV L' hr u m hA')
    exact ⟨j, h1, h3, h4, fun _ => h2, fun hn => absurd ⟨L', hA'⟩ hn⟩
  · have hex : ∃ j, m ≤ j ∧ j < m + F ∧ R.akt j = some u := by
      refine Classical.byContradiction fun hne => ?_
      have hst : ∀ j, m ≤ j → j < m + F → (R.M j).faeden u = (R.M m).faeden u :=
        fun j h1 h2 => R.stet' h1 (fun i hi1 hi2 he => hne ⟨i, hi1, by omega, he⟩)
      obtain ⟨j, h1, h2, h3⟩ := hFair u m fun j h1 h2 => by
        have e := hst j h1 h2
        have hmj : L ∈ offen ((R.M j).faeden u).spur := by rw [e]; exact hm
        rcases hAkt j u L hmj with hb | ⟨L', hA'⟩
        · exact hb
        · exact absurd ⟨L', anSperre_gleich e.symm hA'⟩ hA
      exact hne ⟨j, h1, h2, h3⟩
    obtain ⟨j, h1, h2, h3, h4⟩ := erster_schritt R hex
    exact ⟨j, h1, h3, h4, fun hn => absurd hn hA, fun _ => h2⟩

include hRang hFair hAkt in
/-- **The release.** A thread holding `L` at `m` with a remaining budget of
    `h'` own steps, `k'` of them nested acquisitions, releases `L` at a step
    `e < m + h' * F + k' * G`, holding it until then. -/
theorem freigabe {G : Nat} {L : D.Lock}
    (hV : ∀ L', D.rang L < D.rang L' → ∀ t n, AnSperre (R.M n) t L' →
      ∃ j, n ≤ j ∧ j < n + G ∧ R.akt j = some t)
    (u : Faden) :
    ∀ (h' k' m : Nat), L ∈ offen ((R.M m).faeden u).spur →
      (∀ n, (∀ i, i < n → L ∈ offen ((R.M (m + i)).faeden u).spur) →
        zaehl (fun j => R.akt j = some u) m n ≤ h' ∧
        zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') m n ≤ k') →
      ∃ e, m ≤ e ∧ e < m + (h' * F + k' * G) ∧ R.akt e = some u ∧
        (∀ i, m ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
        L ∉ offen ((R.M (e + 1)).faeden u).spur := by
  intro h'
  induction h' with
  | zero =>
      intro k' m hm hB
      obtain ⟨j, h1, h2, h3, _, _⟩ := luecke R hRang hFair hAkt hV hm
      have hhold : ∀ i, i < j + 1 - m → L ∈ offen ((R.M (m + i)).faeden u).spur := by
        intro i hi
        rw [h3 (m + i) (by omega) (by omega)]; exact hm
      have hc := (hB (j + 1 - m) hhold).1
      have hp := zaehl_pos (fun j => R.akt j = some u) m (j + 1 - m) (j - m) (by omega)
        (by show R.akt (m + (j - m)) = some u; rw [show m + (j - m) = j by omega]; exact h2)
      omega
  | succ h' ih =>
      intro k' m hm hB
      obtain ⟨j, h1, h2, h3, hG, hFF⟩ := luecke R hRang hFair hAkt hV hm
      have hhold : ∀ i, i < j + 1 - m → L ∈ offen ((R.M (m + i)).faeden u).spur := by
        intro i hi
        rw [h3 (m + i) (by omega) (by omega)]; exact hm
      have hpj : ∀ i, m ≤ i → i ≤ j → L ∈ offen ((R.M i).faeden u).spur := by
        intro i hi1 hi2; rw [h3 i hi1 hi2]; exact hm
      have e1 : m + (j + 1 - m) = j + 1 := by omega
      -- the step `j` counts once, and once more as an acquisition if `u` stands at `locks`
      have hp1 : 1 ≤ zaehl (fun j => R.akt j = some u) m (j + 1 - m) :=
        zaehl_pos _ m (j + 1 - m) (j - m) (by omega)
          (by show R.akt (m + (j - m)) = some u; rw [show m + (j - m) = j by omega]; exact h2)
      have hmul : (h' + 1) * F = h' * F + F := Nat.succ_mul h' F
      by_cases hA : ∃ L', AnSperre (R.M m) u L'
      · have hjG := hG hA
        have hp2 : 1 ≤ zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') m
            (j + 1 - m) := by
          obtain ⟨L', hA'⟩ := hA
          refine zaehl_pos _ m (j + 1 - m) (j - m) (by omega) ?_
          show R.akt (m + (j - m)) = some u ∧ ∃ L', AnSperre (R.M (m + (j - m))) u L'
          rw [show m + (j - m) = j by omega]
          exact ⟨h2, L', anSperre_gleich (h3 j h1 (Nat.le_refl j)) hA'⟩
        have hk1 : 1 ≤ k' := Nat.le_trans hp2 (hB _ hhold).2
        obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
        have hmulk : (k'' + 1) * G = k'' * G + G := Nat.succ_mul k'' G
        by_cases hrel : L ∈ offen ((R.M (j + 1)).faeden u).spur
        · have hB' : ∀ n, (∀ i, i < n → L ∈ offen ((R.M (j + 1 + i)).faeden u).spur) →
              zaehl (fun j => R.akt j = some u) (j + 1) n ≤ h' ∧
              zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') (j + 1) n ≤ k'' := by
            intro n hn
            have hall : ∀ i, i < (j + 1 - m) + n → L ∈ offen ((R.M (m + i)).faeden u).spur := by
              intro i hi
              by_cases hi' : i < j + 1 - m
              · exact hhold i hi'
              · have := hn (i - (j + 1 - m)) (by omega)
                rwa [show j + 1 + (i - (j + 1 - m)) = m + i by omega] at this
            have hb := hB _ hall
            rw [zaehl_add, zaehl_add, e1] at hb
            obtain ⟨hb1, hb2⟩ := hb
            exact ⟨by omega, by omega⟩
          obtain ⟨e, e1', e2, e3, e4, e5⟩ := ih k'' (j + 1) hrel hB'
          refine ⟨e, by omega, by omega, e3, fun i hi1 hi2 => ?_, e5⟩
          by_cases hij : i ≤ j
          · exact hpj i hi1 hij
          · exact e4 i (by omega) hi2
        · exact ⟨j, h1, by omega, h2, hpj, hrel⟩
      · have hjF := hFF hA
        by_cases hrel : L ∈ offen ((R.M (j + 1)).faeden u).spur
        · have hB' : ∀ n, (∀ i, i < n → L ∈ offen ((R.M (j + 1 + i)).faeden u).spur) →
              zaehl (fun j => R.akt j = some u) (j + 1) n ≤ h' ∧
              zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') (j + 1) n ≤ k' := by
            intro n hn
            have hall : ∀ i, i < (j + 1 - m) + n → L ∈ offen ((R.M (m + i)).faeden u).spur := by
              intro i hi
              by_cases hi' : i < j + 1 - m
              · exact hhold i hi'
              · have := hn (i - (j + 1 - m)) (by omega)
                rwa [show j + 1 + (i - (j + 1 - m)) = m + i by omega] at this
            have hb := hB _ hall
            rw [zaehl_add, zaehl_add, e1] at hb
            obtain ⟨hb1, hb2⟩ := hb
            exact ⟨by omega, by omega⟩
          obtain ⟨e, e1', e2, e3, e4, e5⟩ := ih k' (j + 1) hrel hB'
          refine ⟨e, by omega, by omega, e3, fun i hi1 hi2 => ?_, e5⟩
          by_cases hij : i ≤ j
          · exact hpj i hi1 hij
          · exact e4 i (by omega) hi2
        · exact ⟨j, h1, by omega, h2, hpj, hrel⟩

include hO hRang hFifo hFair in
/-- **The free gap.** If `L` is free at `m` and thread `t` has stood at
    `locks L` since `n0`, then within `F` scheduler steps `t` takes a step
    (and stands there until it), or another thread `v` takes `L` -- a thread
    that, by FIFO, has stood at `locks L` since `n0` as well. -/
theorem frei_luecke {L : D.Lock} {t : Faden} {n0 m : Nat} (hnm : n0 ≤ m)
    (hW : ∀ j, n0 ≤ j → j ≤ m → AnSperre (R.M j) t L)
    (hfrei : ∀ v, L ∉ offen ((R.M m).faeden v).spur) :
    ∃ j, m ≤ j ∧ j < m + F ∧ (∀ i, n0 ≤ i → i ≤ j → AnSperre (R.M i) t L) ∧
      (R.akt j = some t ∨
        ∃ v, v ≠ t ∧ R.akt j = some v ∧ L ∈ offen ((R.M (j + 1)).faeden v).spur ∧
          (∀ i, n0 ≤ i → i ≤ j → AnSperre (R.M i) v L)) := by
  let Q : Nat → Prop := fun j => R.akt j = some t ∨ ∃ v, L ∈ offen ((R.M (j + 1)).faeden v).spur
  -- before the first `Q`: `L` stays free and `t` stays frozen
  have hvor : ∀ j, m ≤ j → (∀ i, m ≤ i → i < j → ¬ Q i) →
      (R.M j).faeden t = (R.M m).faeden t ∧ ∀ v, L ∉ offen ((R.M j).faeden v).spur := by
    intro j hj hQ
    refine ⟨R.stet' hj (fun i h1 h2 he => hQ i h1 h2 (Or.inl he)), fun v hv => ?_⟩
    rcases Nat.eq_zero_or_pos (j - m) with h0 | hpos
    · have : j = m := by omega
      subst this; exact hfrei v hv
    · exact hQ (j - 1) (by omega) (by omega) (Or.inr ⟨v, by rwa [show j - 1 + 1 = j by omega]⟩)
  have hex : ∃ j, m ≤ j ∧ j < m + F ∧ Q j := by
    refine Classical.byContradiction fun hne => ?_
    have hno : ∀ i, m ≤ i → i < m + F → ¬ Q i := fun i h1 h2 hq => hne ⟨i, h1, h2, hq⟩
    obtain ⟨j, h1, h2, h3⟩ := hFair t m fun j h1 h2 => by
      obtain ⟨e, hf⟩ := hvor j h1 (fun i hi1 hi2 => hno i hi1 (by omega))
      have hA : AnSperre (R.M j) t L := anSperre_gleich e (hW m hnm (Nat.le_refl m))
      obtain ⟨w, hw⟩ := hRang j t
      exact schritt_an_sperre hw hA (fun g _ => hf g)
    exact hno j h1 h2 (Or.inl h3)
  obtain ⟨j, h1, h2, hQ0, hfirst⟩ := erster Q m F hex
  have hQ : R.akt j = some t ∨ ∃ v, L ∈ offen ((R.M (j + 1)).faeden v).spur := hQ0
  obtain ⟨e, hf⟩ := hvor j h1 hfirst
  have hWj : ∀ i, n0 ≤ i → i ≤ j → AnSperre (R.M i) t L := by
    intro i hi1 hi2
    by_cases him : i ≤ m
    · exact hW i hi1 him
    · have e' := R.stet' (u := t) (show m ≤ i by omega)
        (fun i' h1' h2' he => hfirst i' h1' (by omega) (Or.inl he))
      exact anSperre_gleich e' (hW m hnm (Nat.le_refl m))
  refine ⟨j, h1, h2, hWj, ?_⟩
  rcases hQ with ht | ⟨v, hv⟩
  · exact Or.inl ht
  · by_cases ht : R.akt j = some t
    · exact Or.inl ht
    · right
      have hvt : v ≠ t := by
        rintro rfl
        rw [R.fremd j v ht] at hv
        exact an_sperre_frei R hRang (hWj j (by omega) (Nat.le_refl j)) hv
      have hv0 : L ∉ offen ((R.M j).faeden v).spur := hf v
      have hakt : R.akt j = some v := by
        cases ha : R.akt j with
        | none => rw [(R.stotter j ha).1] at hv; exact absurd hv hv0
        | some w =>
            by_cases hwv : w = v
            · rw [hwv]
            · rw [rufSchrittG_fremd (R.schritt j w ha) v (Ne.symm hwv)] at hv
              exact absurd hv hv0
      have hAv := nimmt_an_sperre hO (R.schritt j v hakt) hv0 hv
      exact ⟨v, hvt, hakt, hv, hFifo t v L n0 j (Ne.symm hvt) hWj hakt hAv⟩

/-- The threads AHEAD of `t` at step `m` (`t` stands at `locks L` since `n0`):
    the holder of `L`, and every thread standing at `locks L` since `n0`. -/
abbrev Vor (t : Faden) (L : D.Lock) (n0 m : Nat) (u : Faden) : Prop :=
  u ≠ t ∧ (L ∈ offen ((R.M m).faeden u).spur ∨ ∀ j, n0 ≤ j → j ≤ m → AnSperre (R.M j) u L)

include hO hRang hEx hFifo hFair hAnw in
/-- **Waiting while `L` is held**: with at most `q` threads ahead, `t` takes
    its step within `q * (S + F)` scheduler steps, where `S` bounds one
    critical section (`hRel`). Each round: the holder releases (`< S`), a
    free gap (`< F`) ends with `t`'s step or the next holder -- a thread
    ahead of `t` that leaves the set ahead for good. -/
theorem warte_gehalten {L : D.Lock} {t : Faden} {n0 S : Nat}
    (hRel : ∀ u m, L ∈ offen ((R.M m).faeden u).spur → ∃ e, m ≤ e ∧ e < m + S ∧
      R.akt e = some u ∧ (∀ i, m ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
      L ∉ offen ((R.M (e + 1)).faeden u).spur) :
    ∀ q m, n0 ≤ m → (∀ j, n0 ≤ j → j ≤ m → AnSperre (R.M j) t L) →
      (∃ u, L ∈ offen ((R.M m).faeden u).spur) →
      anz (Vor R t L n0 m) (Ts L) ≤ q →
      ∃ j, m ≤ j ∧ j < m + q * (S + F) ∧ R.akt j = some t
  | 0, m, hnm, hW, ⟨u, hu⟩, hc => by
      have hut : u ≠ t := fun e => an_sperre_frei R hRang (hW m hnm (Nat.le_refl m)) (e ▸ hu)
      have := anz_pos (Vor R t L n0 m) (Ts L) ⟨u, hAnw m u L (Or.inl hu), hut, Or.inl hu⟩
      omega
  | q + 1, m, hnm, hW, ⟨u, hu⟩, hc => by
      have hut : u ≠ t := fun e => an_sperre_frei R hRang (hW m hnm (Nat.le_refl m)) (e ▸ hu)
      have hmul : (q + 1) * (S + F) = q * (S + F) + (S + F) := Nat.succ_mul q (S + F)
      obtain ⟨e, he1, he2, he3, he4, he5⟩ := hRel u m hu
      by_cases hact : ∃ j, m ≤ j ∧ j < e + 1 ∧ R.akt j = some t
      · obtain ⟨j, j1, j2, j3⟩ := hact
        exact ⟨j, j1, by omega, j3⟩
      · have hno : ∀ i, m ≤ i → i < e + 1 → R.akt i ≠ some t :=
          fun i h1 h2 he => hact ⟨i, h1, h2, he⟩
        have hWe : ∀ j, n0 ≤ j → j ≤ e + 1 → AnSperre (R.M j) t L := by
          intro j hj1 hj2
          by_cases hjm : j ≤ m
          · exact hW j hj1 hjm
          · exact anSperre_gleich (R.stet' (show m ≤ j by omega)
              (fun i h1 h2 => hno i h1 (by omega))) (hW m hnm (Nat.le_refl m))
        have hfrei : ∀ v, L ∉ offen ((R.M (e + 1)).faeden v).spur := by
          intro v hv
          by_cases hvu : v = u
          · subst hvu; exact he5 hv
          · have hne : R.akt e ≠ some v := by
              rw [he3]; intro h; exact hvu (Option.some.inj h).symm
            rw [R.fremd e v hne] at hv
            exact hEx e u v (Ne.symm hvu) L (he4 e he1 (Nat.le_refl e)) hv
        obtain ⟨j, j1, j2, j3, j4⟩ := frei_luecke R hO hRang hFifo hFair (show n0 ≤ e + 1 by omega)
          hWe hfrei
        rcases j4 with ht | ⟨v, hvt, hv1, hv2, hv3⟩
        · exact ⟨j, by omega, by omega, ht⟩
        · have hW' : ∀ i, n0 ≤ i → i ≤ j + 1 → AnSperre (R.M i) t L := by
            intro i hi1 hi2
            by_cases hij : i ≤ j
            · exact j3 i hi1 hij
            · have e' : i = j + 1 := by omega
              subst e'
              have hne : R.akt j ≠ some t := by
                rw [hv1]; intro h; exact hvt (Option.some.inj h)
              exact anSperre_gleich (R.fremd j t hne) (j3 j (by omega) (Nat.le_refl j))
          -- the new holder `v` is the only holder, and it was ahead since `n0`
          have hnur : ∀ x, L ∈ offen ((R.M (j + 1)).faeden x).spur → x = v := by
            intro x hx
            refine Classical.byContradiction fun hxv => ?_
            exact hEx (j + 1) v x (Ne.symm hxv) L hv2 hx
          have hvu : v ≠ u := by
            rintro rfl
            exact an_sperre_frei R hRang (hv3 m hnm (by omega)) hu
          have himp : ∀ x ∈ Ts L, Vor R t L n0 (j + 1) x → Vor R t L n0 m x := by
            intro x _ ⟨hxt, hx⟩
            refine ⟨hxt, Or.inr ?_⟩
            rcases hx with hx | hx
            · have := hnur x hx
              subst this
              exact fun i hi1 hi2 => hv3 i hi1 (by omega)
            · exact fun i hi1 hi2 => hx i hi1 (by omega)
          have hunot : ¬ Vor R t L n0 (j + 1) u := by
            rintro ⟨_, hx | hx⟩
            · exact hvu (hnur u hx).symm
            · exact an_sperre_frei R hRang (hx m hnm (by omega)) hu
          have hlt := anz_lt (Vor R t L n0 (j + 1)) (Vor R t L n0 m) (Ts L) himp
            ⟨u, hAnw m u L (Or.inl hu), ⟨hut, Or.inl hu⟩, hunot⟩
          obtain ⟨j', j1', j2', j3'⟩ := warte_gehalten hRel q (j + 1) (by omega) hW' ⟨v, hv2⟩
            (by omega)
          exact ⟨j', by omega, by omega, j3'⟩

include hO hRang hEx hFifo hFair hAnw in
/-- **The waiting bound for one lock**, given the bound `S` of one critical
    section: `t` at `locks L` at `n0` takes its step before
    `n0 + (c L - 1) * (S + F) + F`. -/
theorem warte {L : D.Lock} {t : Faden} {n0 S : Nat}
    (hRel : ∀ u m, L ∈ offen ((R.M m).faeden u).spur → ∃ e, m ≤ e ∧ e < m + S ∧
      R.akt e = some u ∧ (∀ i, m ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
      L ∉ offen ((R.M (e + 1)).faeden u).spur)
    (hA : AnSperre (R.M n0) t L) :
    ∃ j, n0 ≤ j ∧ j < n0 + (((Ts L).length - 1) * (S + F) + F) ∧ R.akt j = some t := by
  have htT : t ∈ Ts L := hAnw n0 t L (Or.inr hA)
  have hc0 : anz (Vor R t L n0 n0) (Ts L) ≤ (Ts L).length - 1 := by
    have := anz_lt_len (Vor R t L n0 n0) (Ts L) ⟨t, htT, fun h => h.1 rfl⟩
    omega
  have hW0 : ∀ j, n0 ≤ j → j ≤ n0 → AnSperre (R.M j) t L := by
    intro j h1 h2
    rw [show j = n0 by omega]; exact hA
  by_cases hg : ∃ u, L ∈ offen ((R.M n0).faeden u).spur
  · obtain ⟨j, j1, j2, j3⟩ := warte_gehalten R hO hRang hEx hFifo hFair hAnw hRel _ n0
      (Nat.le_refl n0) hW0 hg hc0
    exact ⟨j, j1, by omega, j3⟩
  · have hfrei : ∀ v, L ∉ offen ((R.M n0).faeden v).spur := fun v hv => hg ⟨v, hv⟩
    obtain ⟨j, j1, j2, j3, j4⟩ := frei_luecke R hO hRang hFifo hFair (Nat.le_refl n0) hW0 hfrei
    rcases j4 with ht | ⟨v, hvt, hv1, hv2, hv3⟩
    · exact ⟨j, j1, by omega, ht⟩
    · have hW' : ∀ i, n0 ≤ i → i ≤ j + 1 → AnSperre (R.M i) t L := by
        intro i hi1 hi2
        by_cases hij : i ≤ j
        · exact j3 i hi1 hij
        · have e' : i = j + 1 := by omega
          subst e'
          have hne : R.akt j ≠ some t := by
            rw [hv1]; intro h; exact hvt (Option.some.inj h)
          exact anSperre_gleich (R.fremd j t hne) (j3 j (by omega) (Nat.le_refl j))
      have hnur : ∀ x, L ∈ offen ((R.M (j + 1)).faeden x).spur → x = v := by
        intro x hx
        refine Classical.byContradiction fun hxv => ?_
        exact hEx (j + 1) v x (Ne.symm hxv) L hv2 hx
      have himp : ∀ x ∈ Ts L, Vor R t L n0 (j + 1) x → Vor R t L n0 n0 x := by
        intro x _ ⟨hxt, hx⟩
        refine ⟨hxt, Or.inr ?_⟩
        rcases hx with hx | hx
        · have := hnur x hx
          subst this
          exact fun i hi1 hi2 => hv3 i hi1 (by omega)
        · exact fun i hi1 hi2 => hx i hi1 (by omega)
      have hle := anz_mono (Vor R t L n0 (j + 1)) (Vor R t L n0 n0) (Ts L) himp
      obtain ⟨j', j1', j2', j3'⟩ := warte_gehalten R hO hRang hEx hFifo hFair hAnw hRel _ (j + 1)
        (by omega) hW' ⟨v, hv2⟩ (Nat.le_trans hle hc0)
      exact ⟨j', by omega, by omega, j3'⟩

include hO hls hRang hEx hFifo hFair hH hAkt hAnw in
/-- **The bound is valid at every fuel level that covers the locks above `L`**
    -- induction over the rank levels. -/
theorem gueltig : ∀ (n : Nat) (L : D.Lock), hoeher ls L < n → ∀ (t : Faden) (m : Nat),
    AnSperre (R.M m) t L → ∃ j, m ≤ j ∧ j < m + wF ls Ts h k F n L ∧ R.akt j = some t
  | 0, _, hL, _, _, _ => absurd hL (Nat.not_lt_zero _)
  | n + 1, L, hL, t, m, hA => by
      have hV : ∀ L', D.rang L < D.rang L' → ∀ t' n', AnSperre (R.M n') t' L' →
          ∃ j, n' ≤ j ∧ j < n' + wMaxH L (wF ls Ts h k F n) ls ∧ R.akt j = some t' := by
        intro L' hr t' n' hA'
        have hlt := hoeher_lt ls (hls L') hr
        obtain ⟨j, j1, j2, j3⟩ := gueltig n L' (by omega) t' n' hA'
        exact ⟨j, j1, Nat.lt_of_lt_of_le j2
          (Nat.add_le_add_left (le_wMaxH L _ ls L' (hls L') hr) _), j3⟩
      have hRel : ∀ u m', L ∈ offen ((R.M m').faeden u).spur → ∃ e, m' ≤ e ∧
          e < m' + (h L * F + k L * wMaxH L (wF ls Ts h k F n) ls) ∧ R.akt e = some u ∧
          (∀ i, m' ≤ i → i ≤ e → L ∈ offen ((R.M i).faeden u).spur) ∧
          L ∉ offen ((R.M (e + 1)).faeden u).spur :=
        fun u m' hm' => freigabe R hRang hFair hAkt hV u (h L) (k L) m' hm'
          (fun n hn => hH u L m' n hn)
      obtain ⟨j, j1, j2, j3⟩ := warte R hO hRang hEx hFifo hFair hAnw hRel hA
      exact ⟨j, j1, j2, j3⟩

include hO hls hRang hEx hFifo hFair hH hAkt hAnw in
/-- **THE WAITING BOUND, core form.** A thread standing at `locks L` at
    scheduler step `n0` takes `L` at a step `j < n0 + wartezeit L` and holds
    it after that step. -/
theorem wartezeit_kern (L : D.Lock) (t : Faden) (n0 : Nat) (hA : AnSperre (R.M n0) t L) :
    ∃ j, n0 ≤ j ∧ j < n0 + wartezeit ls Ts h k F L ∧ R.akt j = some t ∧
      L ∈ offen ((R.M (j + 1)).faeden t).spur := by
  obtain ⟨j, j1, j2, j3⟩ := gueltig R hO hls hRang hEx hFifo hFair hH hAkt hAnw ls.length L
    (hoeher_lt_len ls (hls L)) t n0 hA
  obtain ⟨j', j1', j2', j3', j4'⟩ := erster_schritt R ⟨j, j1, j2, j3⟩
  have hA' : AnSperre (R.M j') t L := anSperre_gleich (j4' j' j1' (Nat.le_refl j')) hA
  have e := (sperre_schritt hA' (R.schritt j' t j3')).2
  refine ⟨j', j1', j2', j3', ?_⟩
  rw [e]
  exact List.mem_cons_self

end Beweis

/-! ## 8. From the goal theorem's premises -/

/-- **A lock holder can step or stands at a `locks` head**, from progress
    (`fortschrittG_aus`, with `KeinLogikHaltG` -- a conjunct of `Ziel`) and
    `HardwareImAbschnitt`: a finished thread holds no lock (`fertig_leer`),
    a waiting one stands at `locks`, a hardware stop is excluded. -/
theorem abschnittAktiv_aus (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    (hr0 : RufErreichbarG P O passes (RufStartG P sp init) (R.M 0))
    (hL : ∀ n, KeinLogikHaltG O passes (R.M n)) (hB : ∀ n t, BereichG (R.M n) t)
    (hHw : HardwareImAbschnitt R) :
    AbschnittAktiv R := by
  intro n u L hu
  have hr := R.erreichbar hr0 n
  have hND := startSpur_nodup_leer init hLeer
  rcases fortschrittG_aus hO hSt sp init hND hr (hL n) (hB n) u with
    hF | hW | hHalt | hHalt | hHalt | hs
  · have e := fertig_leer (rangInvG_erreichbar hO hSt sp init hND hr u) (hLeer u) hF
    rw [e] at hu
    exact absurd hu List.not_mem_nil
  · exact Or.inr hW.1
  · exact absurd hHalt (hHw n u L hu _)
  · exact absurd hHalt (hHw n u L hu _)
  · exact absurd hHalt (hHw n u L hu _)
  · exact Or.inl hs

/-- **THE WAITING BOUND (`wartezeit_schranke`).** On a scheduled run of
    machine G that starts at a reachable machine, under
    * the goal theorem's premises used here -- `GutO` (hardware), `StufenM`
      (checker), starts without signature locks (`AkzeptiertSpec.wurzeln`,
      idle roots), a complete lock list, and `KeinLogikHaltG` at every machine
      of the run (the conjunct `Ziel.keinLogikHalt`, which `gabbro_ziel`
      supplies at every reachable machine);
    * THE RUNTIME ASSUMPTION `LaufzeitAnnahme R F` (FIFO lock, fairness `F`);
    * the hold-time premise `Haltezeit R h k`;
    * `HardwareImAbschnitt R` (no hardware stop inside a critical section);
    * the contenders `Anwaerter R Ts`;
    a thread standing at `locks L` at scheduler step `n0` takes `L` at a step
    `j < n0 + wartezeit ls Ts h k F L` and holds it after that step. -/
theorem wartezeit_schranke (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    (hls : ∀ L : D.Lock, L ∈ ls)
    (hr0 : RufErreichbarG P O passes (RufStartG P sp init) (R.M 0))
    (hL : ∀ n, KeinLogikHaltG O passes (R.M n)) (hB : ∀ n t, BereichG (R.M n) t)
    (hLZ : LaufzeitAnnahme R F) (hH : Haltezeit R h k) (hHw : HardwareImAbschnitt R)
    (hAnw : Anwaerter R Ts)
    (L : D.Lock) (t : Faden) (n0 : Nat) (hA : AnSperre (R.M n0) t L) :
    ∃ j, n0 ≤ j ∧ j < n0 + wartezeit ls Ts h k F L ∧ R.akt j = some t ∧
      L ∈ offen ((R.M (j + 1)).faeden t).spur := by
  have hND := startSpur_nodup_leer init hLeer
  have hRang : ∀ n t, ∃ w, RangInvG w ((R.M n).faeden t) :=
    fun n t => ⟨_, rangInvG_erreichbar hO hSt sp init hND (R.erreichbar hr0 n) t⟩
  have hEx : ∀ n (f g : Faden), f ≠ g → ∀ L : D.Lock,
      L ∈ offen ((R.M n).faeden f).spur → L ∉ offen ((R.M n).faeden g).spur :=
    fun n => exklusivG hO sp init (startExklusiv_ohne_haelt init hLeer) (R.erreichbar hr0 n)
  exact wartezeit_kern R hO hls hRang hEx hLZ.1 hLZ.2 hH
    (abschnittAktiv_aus R hO hSt sp init hLeer hr0 hL hB hHw) hAnw L t n0 hA

end Kern

end Gabbro.Grammatik

/-! ## CUTS

  Proved (no premise beyond those named in the theorems):
  * `wartezeit_kern`, `wartezeit_schranke` -- the waiting bound on every
    scheduled run of G, with the bound `wartezeit` recursive over ranks.
  * `sperre_schritt`, `schritt_sperre_art`, `nimmt_an_sperre` -- G takes a lock
    only at a `locks` head of that lock, and only while it is free.
  * `abschnittAktiv_aus` -- a lock holder is never stuck except at a `locks`
    head, from progress and `HardwareImAbschnitt`.

  NOT proved, named:
  * `Haltezeit` is a premise, not a consequence of the checker's `held <= N
    ops` (`K002`): the ops-to-steps bridge (KostenG TARGET 3, F1-F9) and a
    potential bound for a `locks` body as a residue segment are missing.
  * `Anwaerter` is a premise on the run; its static source (the threads whose
    call graph reaches `locks L`) is computed in the measurement, not
    proved to cover the run.
  * `LaufzeitAnnahme` and `HardwareImAbschnitt` are assumptions by design.
  * The bound counts SCHEDULER steps (G steps plus stutters), not cycles.
-/

#print axioms Gabbro.Grammatik.sperre_schritt
#print axioms Gabbro.Grammatik.schritt_sperre_art
#print axioms Gabbro.Grammatik.wartezeit_kern
#print axioms Gabbro.Grammatik.wartezeit_schranke
