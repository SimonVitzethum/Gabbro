/-
  File:      Grammatik/X86/TSOTrace.lean
  Subject:   Append-only TSO trace history with increasing fresh timestamps.

  Lane 596: `TSOHistory.histVon` is a two-message snapshot (timestamps 0/1)
  and its `fresh2` lemma builds no preserved growing history. This module
  links canonical `TSOZustand`/`TSOSchritt` traces to an append-only
  history projection: issues keep the history, flushes append one release
  message (`Speichermodell.nachricht .freigabe`) at a strictly fresh
  timestamp, and the writer view joins it. No new TSO executor, no new
  source semantics. Byte granularity only: typed-carrier W/GX stays CUTS.
-/
import Grammatik.X86.TSOHistory

namespace Gabbro.Grammatik.X86

/-- A trace node: the canonical TSO state plus its grown history, the
    per-core views, and the next fresh timestamp. -/
structure SpurKnoten where
  tso : TSOZustand
  hist : Adresse → List (Speichermodell.Nachricht Adresse Byte)
  blick : Nat → Speichermodell.Sicht Adresse
  frisch : Nat

/-- Start node over a TSO state: only the initial message, empty views,
    timestamp 1 is the next fresh one. -/
def spurStart (s : TSOZustand) : SpurKnoten :=
  { tso := s
    hist := fun _ => [⟨0, 0, Speichermodell.Sicht.null⟩]
    blick := fun _ => Speichermodell.Sicht.null
    frisch := 1 }

/-- One trace step, projecting the canonical step: an issue keeps history,
    views and clock; a flush of the actual oldest entry `e` appends one
    release message at the old clock and advances it. The appended value
    comes from the flushed entry, never from a desired conclusion. -/
inductive SpurSchritt : SpurKnoten → SpurKnoten → Prop where
  | issue (n n' : SpurKnoten) (c : Nat) (a : Adresse) (v : Byte)
      (h : issueByte n.tso c a v = some n'.tso)
      (hh : n'.hist = n.hist)
      (hb : n'.blick = n.blick)
      (hf : n'.frisch = n.frisch) : SpurSchritt n n'
  | flush (n n' : SpurKnoten) (c : Nat) (e : TSOEintrag)
      (rest : List TSOEintrag)
      (h : flushKern n.tso c = some n'.tso)
      (he : n.tso.puffer c = e :: rest)
      (hh : n'.hist = fun x =>
        if x = e.addr then n.hist x ++
          [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
            (n.blick c) e.addr n.frisch e.wert]
        else n.hist x)
      (hb : n'.blick = fun d =>
        if d = c then (n.blick c).setze e.addr n.frisch else n.blick d)
      (hf : n'.frisch = n.frisch + 1) : SpurSchritt n n'

/-- Reached trace nodes from `n0`. -/
inductive SpurErreichbar (n0 : SpurKnoten) : SpurKnoten → Prop where
  | start : SpurErreichbar n0 n0
  | schritt {n n' : SpurKnoten} :
      SpurErreichbar n0 n → SpurSchritt n n' → SpurErreichbar n0 n'

/-! ## Clock invariant: every used timestamp is below the clock -/

/-- Every history timestamp and every view entry is strictly below the
    next fresh timestamp. Issues keep it; flushes append exactly at the
    old clock and advance by one, so nothing is ever reset. -/
def SpurInv (n : SpurKnoten) : Prop :=
  (∀ a m, m ∈ n.hist a → m.ts < n.frisch) ∧
  (∀ c a, n.blick c a < n.frisch)

/-- The start node satisfies the invariant: only timestamp 0 is used,
    every view is 0, the clock is 1. -/
theorem spurStart_inv (s : TSOZustand) : SpurInv (spurStart s) := by
  refine ⟨?_, ?_⟩
  · intro a m hm
    simp only [spurStart] at hm
    simp at hm
    subst hm
    show (0 : Nat) < 1
    exact Nat.zero_lt_one
  · intro c a
    show (0 : Nat) < 1
    exact Nat.zero_lt_one

/-- One trace step preserves the invariant. The flush case splits the
    grown history into old messages (below the old clock) and the one
    new release message (exactly at the old clock); the writer view
    joins the new timestamp while every other entry stays below. -/
theorem spurSchritt_inv (n n' : SpurKnoten) (hs : SpurSchritt n n')
    (hinv : SpurInv n) : SpurInv n' := by
  obtain ⟨hhist, hblick⟩ := hinv
  cases hs with
  | issue c a v h hh hb hf =>
    refine ⟨?_, ?_⟩
    · intro x m hm
      rw [hh] at hm
      have hlt := hhist x m hm
      omega
    · intro d y
      rw [hb]
      have hlt := hblick d y
      omega
  | flush c e rest h he hh hb hf =>
    refine ⟨?_, ?_⟩
    · intro x m hm
      have hx := congrFun hh x
      rw [hx] at hm
      by_cases ha : x = e.addr
      · rw [if_pos ha] at hm
        rcases List.mem_append.mp hm with hmold | hneu
        · have hlt := hhist x m hmold
          omega
        · simp at hneu
          subst hneu
          have heq : (Speichermodell.nachricht
            Speichermodell.Ordnung.freigabe (n.blick c) e.addr n.frisch
              e.wert).ts = n.frisch := rfl
          rw [heq]
          omega
      · rw [if_neg ha] at hm
        have hlt := hhist x m hm
        omega
    · intro d y
      have hd := congrFun hb d
      rw [hd]
      by_cases hc : d = c
      · rw [if_pos hc]
        by_cases hy : y = e.addr
        · subst hy
          rw [Speichermodell.Sicht.setze_selbst]
          omega
        · rw [Speichermodell.Sicht.setze_anders _ _ hy]
          have hlt := hblick c y
          omega
      · rw [if_neg hc]
        have hlt := hblick d y
        omega

/-! ## Append-only shape: issues keep, flushes append one message -/

/-- One step either keeps the history at `x` pointwise or appends exactly
    one message there: the release message of the flushed entry at the
    old clock, carrying the flushed value. -/
theorem spur_schritt_hist (n n' : SpurKnoten) (hs : SpurSchritt n n')
    (x : Adresse) :
    n'.hist x = n.hist x ∨
      (∃ e : TSOEintrag, x = e.addr ∧ ∃ msg,
        n'.hist x = n.hist x ++ [msg] ∧ msg.ts = n.frisch ∧
          msg.wert = e.wert) := by
  cases hs with
  | issue c a v h hh hb hf =>
    exact Or.inl (congrFun hh x)
  | flush c e rest h he hh hb hf =>
    by_cases hx : x = e.addr
    · refine Or.inr ⟨e, hx,
        Speichermodell.nachricht Speichermodell.Ordnung.freigabe
          (n.blick c) e.addr n.frisch e.wert, ?_, rfl, rfl⟩
      have hfun := congrFun hh x
      rw [if_pos hx] at hfun
      exact hfun
    · exact Or.inl (by
        have hfun := congrFun hh x
        rw [if_neg hx] at hfun
        exact hfun)

/-- One step never drops a message: previous histories are preserved. -/
theorem spur_schritt_erhaelt (n n' : SpurKnoten) (hs : SpurSchritt n n')
    (x : Adresse) (m : Speichermodell.Nachricht Adresse Byte)
    (hm : m ∈ n.hist x) : m ∈ n'.hist x := by
  rcases spur_schritt_hist n n' hs x with heq | ⟨e, rfl, msg, heq, _, _⟩
  · rw [heq]
    exact hm
  · rw [heq]
    exact List.mem_append.mpr (Or.inl hm)

/-- **Legacy link.** The accepted snapshot helper `histVon` stays the
    bounded evidence it was: every message of a start node is in it.
    Growth only appends (`spur_schritt_erhaelt`); nothing is reset. -/
theorem spurStart_legt_snapshot_vor (s : TSOZustand) (a : Adresse)
    (m : Speichermodell.Nachricht Adresse Byte)
    (hm : m ∈ (spurStart s).hist a) : m ∈ histVon s a := by
  simp only [spurStart] at hm
  simp at hm
  subst hm
  simp [histVon]

/- CUTS:
    - So far only the node/step vocabulary; preservation, freshness,
      forwarding and the joint witness follow as increments.
    - Byte granularity only: no typed-carrier W/GX mapping, no aligned
      multi-byte atomicity, no LOCK RMW, no run induction to W runs.
-/

end Gabbro.Grammatik.X86
