/-
  File:      Grammatik/X86/TSO.lean
  Subject:   Executable byte-granularity x86-TSO over the canonical pilot memory.

  Lane 284 (wave A, Lean-first): per-core FIFO store buffers, store issue,
  youngest own-buffer forwarding on loads, globally scheduled oldest-entry
  flush onto the SAME canonical `Speicher` of `Grammatik.X86.Typen`, a local
  fence ready only when the own buffer is empty, and explicit
  permissions/failure. Flushes really write canonical bytes; nothing here is
  a stateless event toy. Aligned multi-byte single-copy atomicity and LOCK
  RMW are NOT claimed (refused/OPEN, see §7). Source W/GX stay the source
  concurrency model; §8 holds one proved target-side link to `Sicht`
  (`Lesbar`/`Frisch` instantiated at bytes) plus the precise OPEN
  cross-granularity obligation. No fairness, no OS, no whole-G-block claim.
-/
import Grammatik.X86.Speicher
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

/-- One pending byte store: its address and its byte value. -/
structure TSOEintrag where
  addr : Adresse
  wert : Byte
  deriving DecidableEq, Repr

/-- TSO target state: canonical memory plus one FIFO buffer per core.
    Each core buffer is oldest-first: the head is the next to flush. -/
structure TSOZustand where
  mem : Speicher
  puffer : Nat → List TSOEintrag

/-! ## 1. Core operations: issue, load with forwarding, flush, fence -/

/-- Point update of a core buffer. -/
def pufferSetze (p : Nat → List TSOEintrag) (c : Nat)
    (l : List TSOEintrag) : Nat → List TSOEintrag :=
  fun d => if d = c then l else p d

theorem pufferSetze_gleich (p : Nat → List TSOEintrag) (c : Nat)
    (l : List TSOEintrag) : pufferSetze p c l c = l := by
  simp [pufferSetze]

theorem pufferSetze_anders (p : Nat → List TSOEintrag) {c d : Nat}
    (l : List TSOEintrag) (h : d ≠ c) : pufferSetze p c l d = p d := by
  simp [pufferSetze, h]

/-- Store issue: needs write permission at `a`; appends youngest-last,
    leaves canonical memory unchanged. `none` = refused (failure). -/
def issueByte (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) : Option TSOZustand :=
  if s.mem.schreibbar a then
    some ⟨s.mem, pufferSetze s.puffer c (s.puffer c ++ [⟨a, v⟩])⟩
  else none

/-- Youngest pending value for `a` in a buffer (`none` = no pending entry).
    The fold keeps the LAST match, i.e. the youngest entry. -/
def neuestens : List TSOEintrag → Adresse → Option Byte
  | [], _ => none
  | e :: rest, a =>
    match neuestens rest a with
    | some v => some v
    | none => if e.addr = a then some e.wert else none

/-- Byte load on core `c`: youngest own-buffer entry wins (forwarding),
    otherwise canonical memory. `none` = unreadable (failure). -/
def loadByte (s : TSOZustand) (c : Nat) (a : Adresse) : Option Byte :=
  if s.mem.lesbar a then
    some (match neuestens (s.puffer c) a with
      | some v => v
      | none => s.mem.bytes a)
  else none

/-- Flush of the oldest entry of core `c`: writes its byte into canonical
    memory, drops the head. `none` = empty buffer, nothing to flush. -/
def flushKern (s : TSOZustand) (c : Nat) : Option TSOZustand :=
  match s.puffer c with
  | [] => none
  | e :: rest =>
    some ⟨{ s.mem with bytes := fun x => if x = e.addr then e.wert else s.mem.bytes x },
      pufferSetze s.puffer c rest⟩

/-- Local fence readiness: ready exactly when the OWN buffer is empty.
    A fence changes no state; it only gates. -/
def zaunBereit (s : TSOZustand) (c : Nat) : Bool :=
  (s.puffer c).isEmpty

/-! ## 2. Steps and reachability -/

/-- One TSO step: store issue or oldest-entry flush of any core.
    Loads and fences gate but change no state, so they are no steps. -/
inductive TSOSchritt : TSOZustand → TSOZustand → Prop where
  | issue (s s' : TSOZustand) (c : Nat) (a : Adresse) (v : Byte)
      (h : issueByte s c a v = some s') : TSOSchritt s s'
  | flush (s s' : TSOZustand) (c : Nat)
      (h : flushKern s c = some s') : TSOSchritt s s'

/-- Reached TSO states from `s0`. -/
inductive TSOErreichbar (s0 : TSOZustand) : TSOZustand → Prop where
  | start : TSOErreichbar s0 s0
  | schritt {s s' : TSOZustand} :
      TSOErreichbar s0 s → TSOSchritt s s' → TSOErreichbar s0 s'

/-! ## 3. Permissions are preserved; other cores are untouched -/

/-- Issue preserves all global permissions: only a buffer grows. -/
theorem issue_erhaelt_berechtigungen (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte) (h : issueByte s c a v = some s') :
    s'.mem.lesbar = s.mem.lesbar ∧ s'.mem.schreibbar = s.mem.schreibbar ∧
      s'.mem.ausfuehrbar = s.mem.ausfuehrbar := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hc] at h
    cases h

/-- Flush preserves all global permissions: only `bytes` changes. -/
theorem flush_erhaelt_berechtigungen (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s') :
    s'.mem.lesbar = s.mem.lesbar ∧ s'.mem.schreibbar = s.mem.schreibbar ∧
      s'.mem.ausfuehrbar = s.mem.ausfuehrbar := by
  unfold flushKern at h
  cases hb : s.puffer c with
  | nil =>
    rw [hb] at h
    cases h
  | cons e rest =>
    rw [hb] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩

/-- Issue touches no other core's buffer. -/
theorem issue_anderer_kern (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte) (h : issueByte s c a v = some s')
    {d : Nat} (hd : d ≠ c) : s'.puffer d = s.puffer d := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    exact pufferSetze_anders _ _ hd
  · rw [if_neg hc] at h
    cases h

/-- Flush touches no other core's buffer. -/
theorem flush_anderer_kern (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s')
    {d : Nat} (hd : d ≠ c) : s'.puffer d = s.puffer d := by
  unfold flushKern at h
  cases hb : s.puffer c with
  | nil =>
    rw [hb] at h
    cases h
  | cons e rest =>
    rw [hb] at h
    cases h
    exact pufferSetze_anders _ _ hd

/-- Issue changes no canonical byte: the store sits in the buffer. -/
theorem issue_kein_speicher (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte) (h : issueByte s c a v = some s')
    (x : Adresse) : s'.mem.bytes x = s.mem.bytes x := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    rfl
  · rw [if_neg hc] at h
    cases h

/-- Flush writes exactly the oldest entry's byte at its address. -/
theorem flush_schreibt_kopf (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s') (e : TSOEintrag)
    (rest : List TSOEintrag)
    (he : s.puffer c = e :: rest) :
    s'.mem.bytes e.addr = e.wert := by
  unfold flushKern at h
  rw [he] at h
  cases h
  simp

/-- Flush changes no byte outside the flushed address (frame). -/
theorem flush_rahmen (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s') (e : TSOEintrag)
    (rest : List TSOEintrag)
    (he : s.puffer c = e :: rest)
    (x : Adresse) (hx : x ≠ e.addr) :
    s'.mem.bytes x = s.mem.bytes x := by
  unfold flushKern at h
  rw [he] at h
  cases h
  simp [hx]

end Gabbro.Grammatik.X86
