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

/-! ## Freshness, release views, forwarding, memory latest value -/

/-- The clock is fresh for every flush: the writer's view is below it
    and no history message uses it. Both invariant halves are needed. -/
theorem spur_flush_frisch_vor (n : SpurKnoten) (c : Nat) (e : TSOEintrag)
    (hinv : SpurInv n) :
    Speichermodell.Frisch n.hist (n.blick c) e.addr n.frisch := by
  obtain ⟨hhist, hblick⟩ := hinv
  refine ⟨hblick c e.addr, ?_⟩
  intro m hm hcon
  have hlt := hhist _ _ hm
  omega

/-- **Release views.** A flushed release message carries the writer's
    view set at the flushed address, stamped with the flush clock.
    Readers joining it observe everything the writer observed. -/
theorem spur_freigabe_sicht (n : SpurKnoten) (c : Nat) (e : TSOEintrag) :
    (Speichermodell.nachricht Speichermodell.Ordnung.freigabe
      (n.blick c) e.addr n.frisch e.wert).sicht
        = (n.blick c).setze e.addr n.frisch ∧
    (Speichermodell.nachricht Speichermodell.Ordnung.freigabe
      (n.blick c) e.addr n.frisch e.wert).ts = n.frisch :=
  ⟨rfl, rfl⟩

/-- **Own-buffer forwarded loads.** A load that hits the own buffer
    returns the youngest pending value, and that entry splits the buffer
    into an older prefix and a younger match-free suffix. Reused from
    the canonical projection; no premise is dropped. -/
theorem spur_weiterleitung_ist_jüngste (n : SpurKnoten) (c : Nat)
    (a : Adresse) (v w : Byte)
    (hload : loadByte n.tso c a = some v)
    (hpend : neuestens (n.tso.puffer c) a = some w) :
    v = w ∧ ∃ pre post : List TSOEintrag,
      n.tso.puffer c = pre ++ [⟨a, w⟩] ++ post ∧
        ∀ e' ∈ post, e'.addr ≠ a :=
  weiterleitung_ist_jüngste n.tso c a v w hload hpend

/-- **Memory latest value.** A flush writes the oldest entry's byte into
    canonical memory, the release message carrying it is in the grown
    history, and every previous message is preserved. -/
theorem spur_flush_schreibt (n n' : SpurKnoten) (c : Nat) (e : TSOEintrag)
    (rest : List TSOEintrag)
    (h : flushKern n.tso c = some n'.tso)
    (he : n.tso.puffer c = e :: rest)
    (hh : n'.hist e.addr = n.hist e.addr ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (n.blick c) e.addr n.frisch e.wert]) :
    n'.tso.mem.bytes e.addr = e.wert ∧
      (Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (n.blick c) e.addr n.frisch e.wert) ∈ n'.hist e.addr ∧
      ∀ m ∈ n.hist e.addr, m ∈ n'.hist e.addr := by
  refine ⟨flush_schreibt_kopf n.tso n'.tso c h e rest he, ?_, ?_⟩
  · rw [hh]
    refine List.mem_append.mpr (Or.inr ?_)
    simp
  · intro m hm
    rw [hh]
    exact List.mem_append.mpr (Or.inl hm)

/-! ## One-flush and finite-trace extension -/

/-- **Generic one-flush extension.** One trace step is either an issue
    (history and clock unchanged) or a flush of the actual oldest entry:
    its timestamp was fresh, its release message is readable in the grown
    history at the writer's joined view, canonical memory holds the
    flushed byte, the invariant is preserved, and no previous message is
    lost. The flushed value comes from the buffer entry, never from a
    desired conclusion. -/
theorem spur_ein_flush (n n' : SpurKnoten) (hs : SpurSchritt n n')
    (hinv : SpurInv n) :
    (∃ c a v, issueByte n.tso c a v = some n'.tso ∧
      n'.hist = n.hist ∧ n'.frisch = n.frisch) ∨
    (∃ c e rest, flushKern n.tso c = some n'.tso ∧
      n.tso.puffer c = e :: rest ∧
      Speichermodell.Frisch n.hist (n.blick c) e.addr n.frisch ∧
      Speichermodell.Lesbar n'.hist (n'.blick c) e.addr
        (Speichermodell.nachricht Speichermodell.Ordnung.freigabe
          (n.blick c) e.addr n.frisch e.wert) ∧
      n'.tso.mem.bytes e.addr = e.wert ∧
      SpurInv n' ∧
      ∀ x m, m ∈ n.hist x → m ∈ n'.hist x) := by
  cases hs with
  | issue c a v h hh hb hf =>
    exact Or.inl ⟨c, a, v, h, hh, hf⟩
  | flush c e rest h he hh hb hf =>
    have hs' : SpurSchritt n n' :=
      SpurSchritt.flush n n' c e rest h he hh hb hf
    refine Or.inr ⟨c, e, rest, h, he, spur_flush_frisch_vor n c e hinv,
      ?_, flush_schreibt_kopf _ _ _ h e rest he,
      spurSchritt_inv n n' hs' hinv, ?_⟩
    · have hfun := congrFun hh e.addr
      have hcond : e.addr = e.addr := rfl
      rw [if_pos hcond] at hfun
      have hbv := congrFun hb c
      have hcondc : c = c := rfl
      rw [if_pos hcondc] at hbv
      refine ⟨?_, ?_⟩
      · rw [hfun]
        refine List.mem_append.mpr (Or.inr ?_)
        simp
      · rw [hbv, Speichermodell.Sicht.setze_selbst]
        exact Nat.le_refl _
    · intro x m hm
      exact spur_schritt_erhaelt n n' hs' x m hm

/-- **Finite-trace extension.** Over every reached trace node the
    invariant holds, the clock never moves backwards, and every message
    of the start history is still present: timestamps are never reset
    and histories only grow. -/
theorem spur_verlauf_waechst (n0 n : SpurKnoten)
    (hr : SpurErreichbar n0 n) (hinv0 : SpurInv n0) :
    SpurInv n ∧ n0.frisch ≤ n.frisch ∧
      ∀ a m, m ∈ n0.hist a → m ∈ n.hist a := by
  induction hr with
  | start =>
    exact ⟨hinv0, Nat.le_refl _, fun a m hm => hm⟩
  | schritt prev step ih =>
    obtain ⟨hinv_mid, hle_mid, hkeep_mid⟩ := ih
    refine ⟨spurSchritt_inv _ _ step hinv_mid, ?_, ?_⟩
    · cases step with
      | issue c a v h hh hb hf =>
        rw [hf]
        exact hle_mid
      | flush c e rest h he hh hb hf =>
        rw [hf]
        omega
    · intro a m hm
      exact spur_schritt_erhaelt _ _ step a m (hkeep_mid a m hm)

/-- **FIFO issuance reaches the grown history.** After two issues from an
    empty buffer and a flush, the OLDER value is both the canonical byte
    and a history message at its actual value, while every previous
    message is preserved. The buffer shape pins the flushed entry to
    `⟨a, v⟩`, so the history equation `hh` is the flush constructor's
    equation at the actual oldest entry. -/
theorem spur_fifo_aelteste (s s1 s2 : TSOZustand) (n2 n3 : SpurKnoten)
    (c : Nat) (a b : Adresse) (v w : Byte)
    (h1 : issueByte s c a v = some s1)
    (h2 : issueByte s1 c b w = some s2)
    (hempty : s.puffer c = [])
    (heq : n2.tso = s2)
    (h : flushKern n2.tso c = some n3.tso)
    (hh : n3.hist a = n2.hist a ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (n2.blick c) a n2.frisch v]) :
    n3.tso.mem.bytes a = v ∧
      (Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (n2.blick c) a n2.frisch v) ∈ n3.hist a ∧
      ∀ m ∈ n2.hist a, m ∈ n3.hist a := by
  have e1 := issue_haengt_an s s1 c a v h1
  have e2 := issue_haengt_an s1 s2 c b w h2
  rw [hempty] at e1
  simp only [List.nil_append] at e1
  have hbuf : n2.tso.puffer c = ⟨a, v⟩ :: [⟨b, w⟩] := by
    rw [e1] at e2
    rw [heq]
    simpa using e2
  refine ⟨flush_schreibt_kopf n2.tso n3.tso c h ⟨a, v⟩ [⟨b, w⟩] hbuf,
    ?_, ?_⟩
  · rw [hh]
    refine List.mem_append.mpr (Or.inr ?_)
    simp
  · intro m hm
    rw [hh]
    exact List.mem_append.mpr (Or.inl hm)

/-! ## Joint two-core witness with non-degenerate timestamps -/

/-- Witness nodes: two issues on different cores, then both flushes.
    Histories/views/clocks follow the step equations definitionally. -/
def spurW0 : SpurKnoten := spurStart sbStart

def spurW1 : SpurKnoten :=
  { tso := sbNach1, hist := spurW0.hist, blick := spurW0.blick,
    frisch := spurW0.frisch }

def spurW2 : SpurKnoten :=
  { tso := sbNach2, hist := spurW1.hist, blick := spurW1.blick,
    frisch := spurW1.frisch }

def spurW3 : SpurKnoten :=
  { tso := sbGespült
    hist := fun x => if x = sbX then spurW2.hist x ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (spurW2.blick 0) sbX spurW2.frisch sbEins]
      else spurW2.hist x
    blick := fun d => if d = 0 then
      (spurW2.blick 0).setze sbX spurW2.frisch else spurW2.blick d
    frisch := spurW2.frisch + 1 }

/-- Core 0's buffer at `spurW2` holds its own issued byte. -/
theorem spurW2_puffer0 : spurW2.tso.puffer 0 = [⟨sbX, sbEins⟩] := by
  show pufferSetze sbNach1.puffer 1 [⟨sbY, sbEins⟩] 0 = _
  rw [pufferSetze_anders _ _ (by decide)]
  show pufferSetze sbStart.puffer 0 [⟨sbX, sbEins⟩] 0 = _
  exact pufferSetze_gleich _ _ _

/-- First issue step: core 0 issues `sbX := 1`. -/
theorem spurW_stufe1 : SpurSchritt spurW0 spurW1 :=
  SpurSchritt.issue _ _ 0 sbX sbEins sb_schritt1 rfl rfl rfl

/-- Second issue step: core 1 issues `sbY := 1`. -/
theorem spurW_stufe2 : SpurSchritt spurW1 spurW2 :=
  SpurSchritt.issue _ _ 1 sbY sbEins sb_schritt2 rfl rfl rfl

/-- First flush step: core 0 publishes `sbX := 1` at clock 1. -/
theorem spurW_stufe3 : SpurSchritt spurW2 spurW3 :=
  SpurSchritt.flush _ _ 0 ⟨sbX, sbEins⟩ [] sb_flush_schritt
    spurW2_puffer0 rfl rfl rfl

/-- Core 1's buffer at `spurW3` still holds its issued byte. -/
theorem spurW3_puffer1 : spurW3.tso.puffer 1 = [⟨sbY, sbEins⟩] := by
  show pufferSetze sbNach2.puffer 0 [] 1 = _
  rw [pufferSetze_anders _ _ (by decide)]
  show pufferSetze sbNach1.puffer 1 [⟨sbY, sbEins⟩] 1 = _
  exact pufferSetze_gleich _ _ _

/-- The TSO state after core 1 flushes: exactly what the canonical
    flush computes. -/
def spurW4tso : TSOZustand :=
  ⟨{ spurW3.tso.mem with
      bytes := fun x =>
        if x = sbY then sbEins else spurW3.tso.mem.bytes x },
    pufferSetze spurW3.tso.puffer 1 []⟩

/-- The flush of core 1 computes as claimed. -/
theorem spurW_stufe4_tso : flushKern spurW3.tso 1 = some spurW4tso := by
  unfold flushKern
  rw [spurW3_puffer1]
  rfl

def spurW4 : SpurKnoten :=
  { tso := spurW4tso
    hist := fun x => if x = sbY then spurW3.hist x ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (spurW3.blick 1) sbY spurW3.frisch sbEins]
      else spurW3.hist x
    blick := fun d => if d = 1 then
      (spurW3.blick 1).setze sbY spurW3.frisch else spurW3.blick d
    frisch := spurW3.frisch + 1 }

/-- Second flush step: core 1 publishes `sbY := 1` at clock 2. -/
theorem spurW_stufe4 : SpurSchritt spurW3 spurW4 :=
  SpurSchritt.flush _ _ 1 ⟨sbY, sbEins⟩ [] spurW_stufe4_tso
    spurW3_puffer1 rfl rfl rfl

/-- The four-step trace is reached from the start node. -/
theorem spurW_erreichbar : SpurErreichbar spurW0 spurW4 :=
  SpurErreichbar.schritt
    (SpurErreichbar.schritt
      (SpurErreichbar.schritt
        (SpurErreichbar.schritt SpurErreichbar.start spurW_stufe1)
        spurW_stufe2)
      spurW_stufe3)
    spurW_stufe4

/-- The grown history at `sbX`: initial message plus the clock-1 flush. -/
theorem spurW_histX : spurW4.hist sbX =
    [⟨0, 0, Speichermodell.Sicht.null⟩,
     Speichermodell.nachricht Speichermodell.Ordnung.freigabe
       (spurW2.blick 0) sbX spurW2.frisch sbEins] := by
  have h4 : spurW4.hist sbX = spurW3.hist sbX := by
    simp only [spurW4]
    rw [if_neg sbX_ne_sbY]
  have h3 : spurW3.hist sbX = spurW2.hist sbX ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (spurW2.blick 0) sbX spurW2.frisch sbEins] := by
    show (if sbX = sbX then spurW2.hist sbX ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (spurW2.blick 0) sbX spurW2.frisch sbEins]
      else spurW2.hist sbX) = _
    rw [if_pos (rfl : sbX = sbX)]
  rw [h4, h3]
  rfl

/-- The grown history at `sbY`: initial message plus the clock-2 flush. -/
theorem spurW_histY : spurW4.hist sbY =
    [⟨0, 0, Speichermodell.Sicht.null⟩,
     Speichermodell.nachricht Speichermodell.Ordnung.freigabe
       (spurW3.blick 1) sbY spurW3.frisch sbEins] := by
  have h4 : spurW4.hist sbY = spurW3.hist sbY ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (spurW3.blick 1) sbY spurW3.frisch sbEins] := by
    show (if sbY = sbY then spurW3.hist sbY ++
      [Speichermodell.nachricht Speichermodell.Ordnung.freigabe
        (spurW3.blick 1) sbY spurW3.frisch sbEins]
      else spurW3.hist sbY) = _
    rw [if_pos (rfl : sbY = sbY)]
  rw [h4]
  rfl

/-- The clocks are non-degenerate: flushes stamped 1 and 2. -/
theorem spurW_uhren : spurW2.frisch = 1 ∧ spurW3.frisch = 2 :=
  ⟨rfl, rfl⟩

/-- Both flushes observably change canonical memory. -/
theorem spurW_speicher :
    spurW0.tso.mem.bytes sbX ≠ spurW4.tso.mem.bytes sbX ∧
      spurW0.tso.mem.bytes sbY ≠ spurW4.tso.mem.bytes sbY := by
  constructor <;> decide

/-- After both flushes each core reads back the flushed byte. -/
theorem spurW_laden :
    loadByte spurW4.tso 0 sbX = some sbEins ∧
      loadByte spurW4.tso 1 sbY = some sbEins := by
  constructor <;> decide

/- CUTS:
    - So far only the node/step vocabulary; preservation, freshness,
      forwarding and the joint witness follow as increments.
    - Byte granularity only: no typed-carrier W/GX mapping, no aligned
      multi-byte atomicity, no LOCK RMW, no run induction to W runs.
-/

end Gabbro.Grammatik.X86
