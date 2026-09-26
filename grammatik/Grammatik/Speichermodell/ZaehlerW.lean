/-
  File:      Grammatik/Speichermodell/ZaehlerW.lean
  Subject:   THE COUNTER ON MACHINE W ITSELF (Opus lane O25c, 2026-09-26): with RMW atomicity in
             `SchrittW` (`SchrittW.rmw`), increments by `exchange` are never lost.

  Lane O25 proved the counter on a mini-machine (`zaehler_zwei`, Zaehler.lean) and showed that
  W without the adjacency loses an update (`zaehler_verloren`). Since lane O25c the adjacency is
  a field of `SchrittW`, and the counter is a theorem of W:

  * `ZaehltHoch P O passes ord M0 g f` -- the PROGRAM side, as a hypothesis over the run: every
    W step that writes the atomic `g` is an `exchange` of `g` whose written value is the value
    it read plus one (measured by `f`, e.g. `Wert.n` of an integer global);
  * `w_kette` -- the INVARIANT on every machine W reaches: the history of `g` is exactly the
    timestamps `k, k-1, …, 0` (no gap, no duplicate) and the message at timestamp `i` holds
    `v0 + i`, where `v0` is the start value;
  * **`w_zaehler`** -- so the newest message holds `v0 + (number of writes)`: after `n`
    increments by any threads, in any interleaving and whatever stale message each RMW's view
    admitted, the counter is `v0 + n`. Two threads incrementing once each end at `v0 + 2`
    (`w_zaehler_zwei`). Without `SchrittW.rmw` this is false (`zaehler_verloren`).

  NOT here: a concrete program term whose steps are shown, rule by rule, to meet `ZaehltHoch`
  (that every step writing `g` is its `exchange`); for a given program that is a finite
  inversion over the rules of G, as `g_schritt_0` does for one step (report §6).
-/
import Grammatik.Speichermodell.RMW

namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

/-- **Every write of `g` is an `exchange` of `g` that adds one** (measured by `f`). -/
def ZaehltHoch (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (M0 : RufMaschineG D) (g : D.Glob) (f : Wert D (D.gtyp g) → Int) : Prop :=
  ∀ (W W' : RufMaschineW D) (u : Faden) (σ : Speicher D) (M'' : RufMaschineG D)
    (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
    RufErreichbarW P O passes ord (RufStartW M0) W →
    SchrittW P O passes ord W u W' σ M'' wahl neu →
    SchreibG (mitSpeicher W.g σ) M'' u (.inr g) →
    ExchangeKopf W.g u g ∧ f (M''.speicher.globs g) = f (σ.globs g) + 1

/-- The chain invariant of the history of `g`. -/
def KetteInv (g : D.Glob) (f : Wert D (D.gtyp g) → Int) (v0 : Int) (W : RufMaschineW D) : Prop :=
  (W.hist (.inr g)).map (·.ts) = (List.range (W.hist (.inr g)).length).reverse ∧
  ∀ m ∈ W.hist (.inr g), f (m.wert.globs g) = v0 + m.ts

section Kette

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

theorem mem_ts_lt {l : List (NachrichtW D)} {m : NachrichtW D}
    (h : l.map (·.ts) = (List.range l.length).reverse) (hm : m ∈ l) : m.ts < l.length := by
  have : m.ts ∈ l.map (·.ts) := List.mem_map_of_mem hm
  rw [h, List.mem_reverse, List.mem_range] at this
  exact this

theorem ts_mem {l : List (NachrichtW D)} (h : l.map (·.ts) = (List.range l.length).reverse)
    {i : Nat} (hi : i < l.length) : ∃ m ∈ l, m.ts = i := by
  have : i ∈ l.map (·.ts) := by rw [h, List.mem_reverse, List.mem_range]; exact hi
  obtain ⟨m, hm, e⟩ := List.mem_map.mp this
  exact ⟨m, hm, e⟩

/-- **THE CHAIN on every machine W reaches.** -/
theorem w_kette {M0 : RufMaschineG D} {g : D.Glob} {f : Wert D (D.gtyp g) → Int}
    (hZ : ZaehltHoch P O passes ord M0 g f) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW M0) W) :
    KetteInv g f (f (M0.speicher.globs g)) W := by
  induction hr with
  | start =>
      refine ⟨rfl, fun m hm => ?_⟩
      have e : m = ⟨0, M0.speicher, Sicht.null⟩ := List.mem_singleton.mp hm
      subst e
      show f (M0.speicher.globs g) = f (M0.speicher.globs g) + ((0 : Nat) : Int)
      simp
  | schritt W W' u hr' hs ih =>
      obtain ⟨σ, M'', wahl, neu, h⟩ := hs
      obtain ⟨hmap, hval⟩ := ih
      by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u (.inr g)
      · obtain ⟨hk, hv⟩ := hZ W W' u σ M'' wahl neu hr' h hw
        have hk' : ExchangeKopf (mitSpeicher W.g σ) u g := hk
        have hrd := (exchange_liest_schreibt hk' h.schritt).1
        obtain ⟨⟨hmem, _⟩, hσ⟩ := h.lies _ hrd
        have hadj := h.rmw g hk
        have hfr := (h.frisch _ hw).2
        have hlt := mem_ts_lt hmap hmem
        -- the RMW read the NEWEST message: anything below would leave its successor taken
        have hneu : neu (.inr g) = (W.hist (.inr g)).length := by
          refine Classical.byContradiction fun hne => ?_
          have hl : (wahl (.inr g)).ts + 1 < (W.hist (.inr g)).length := by omega
          obtain ⟨m, hm, e⟩ := ts_mem hmap hl
          exact hfr m hm (by rw [e, hadj])
        unfold KetteInv
        rw [h.histS _ hw]
        refine ⟨?_, fun m hm => ?_⟩
        · show neu (.inr g) :: (W.hist (.inr g)).map (·.ts) =
            (List.range ((W.hist (.inr g)).length + 1)).reverse
          rw [hmap, hneu, List.range_succ, List.reverse_append]
          rfl
        · rcases List.mem_cons.mp hm with rfl | hm
          · show f (W'.g.speicher.globs g) = f (M0.speicher.globs g) + (neu (.inr g) : Int)
            have e1 : W'.g.speicher.globs g = M''.speicher.globs g := h.speicherS _ hw
            have e2 : σ.globs g = (wahl (.inr g)).wert.globs g := hσ
            rw [e1, hv, e2, hval _ hmem, hadj]
            omega
          · exact hval m hm
      · unfold KetteInv
        rw [h.histU _ hw]
        exact ⟨hmap, hval⟩

/-- **THE COUNTER ON W**: at every machine W reaches, the newest message of `g` (the head of its
    history, the one at the highest timestamp) holds the start value plus the number of writes,
    and every message sits at or below it. -/
theorem w_zaehler {M0 : RufMaschineG D} {g : D.Glob} {f : Wert D (D.gtyp g) → Int}
    (hZ : ZaehltHoch P O passes ord M0 g f) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW M0) W) :
    ∃ m k, W.hist (.inr g) = m :: k ∧ m.ts = k.length ∧
      f (m.wert.globs g) = f (M0.speicher.globs g) + k.length ∧ ∀ m' ∈ k, m'.ts < m.ts := by
  obtain ⟨hmap, hval⟩ := w_kette hZ hr
  have h0 : (⟨0, M0.speicher, Sicht.null⟩ : NachrichtW D) ∈ W.hist (.inr g) :=
    (laufW_waechst hr).1 _ _ (List.mem_singleton_self _)
  cases hh : W.hist (.inr g) with
  | nil => rw [hh] at h0; exact absurd h0 List.not_mem_nil
  | cons m k =>
      rw [hh] at hmap hval
      have hts : m.ts = k.length := by
        have := congrArg List.head? hmap
        simp [List.range_succ] at this
        exact this
      refine ⟨m, k, rfl, hts, by rw [hval m List.mem_cons_self, hts], fun m' hm' => ?_⟩
      have := mem_ts_lt hmap (List.mem_cons_of_mem _ hm')
      rw [hts]
      have hne : m'.ts ≠ k.length := by
        intro e
        have hm2 : m'.ts ∈ k.map (·.ts) := List.mem_map_of_mem hm'
        have hk : k.map (·.ts) = (List.range k.length).reverse := by
          simp [List.range_succ] at hmap
          exact hmap.2
        rw [hk, List.mem_reverse, List.mem_range, e] at hm2
        omega
      simp at this
      omega

/-- **Two increments, the counter ends at two above its start**: once the history of `g` holds
    three messages (the start and two writes), the newest holds `v0 + 2` -- whichever threads
    wrote, in whichever order, whatever their views admitted. -/
theorem w_zaehler_zwei {M0 : RufMaschineG D} {g : D.Glob} {f : Wert D (D.gtyp g) → Int}
    (hZ : ZaehltHoch P O passes ord M0 g f) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW M0) W) (h3 : (W.hist (.inr g)).length = 3) :
    ∃ m k, W.hist (.inr g) = m :: k ∧ f (m.wert.globs g) = f (M0.speicher.globs g) + 2 := by
  obtain ⟨m, k, hh, _, hv, _⟩ := w_zaehler hZ hr
  refine ⟨m, k, hh, ?_⟩
  rw [hh] at h3
  simp at h3
  rw [hv, h3]
  rfl

end Kette

#print axioms Gabbro.Grammatik.w_kette
#print axioms Gabbro.Grammatik.w_zaehler
#print axioms Gabbro.Grammatik.w_zaehler_zwei

end Gabbro.Grammatik
