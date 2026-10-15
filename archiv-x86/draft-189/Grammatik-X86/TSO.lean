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

/-! ## 4. Explicit failure: refusals -/

/-- A store without write permission is refused: memory cannot change. -/
theorem issue_verweigert (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) (h : s.mem.schreibbar a = false) :
    issueByte s c a v = none := by
  unfold issueByte
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- A load without read permission is refused. -/
theorem load_verweigert (s : TSOZustand) (c : Nat) (a : Adresse)
    (h : s.mem.lesbar a = false) :
    loadByte s c a = none := by
  unfold loadByte
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- Flushing an empty buffer is refused. -/
theorem flush_leer (s : TSOZustand) (c : Nat)
    (h : s.puffer c = []) :
    flushKern s c = none := by
  unfold flushKern
  rw [h]

/-! ## 5. Forwarding: the youngest own entry wins -/

/-- Appending an entry for `a` makes it the youngest match. -/
theorem neuestens_angehaengt (l : List TSOEintrag) (a : Adresse)
    (v : Byte) :
    neuestens (l ++ [⟨a, v⟩]) a = some v := by
  induction l with
  | nil =>
    simp [neuestens]
  | cons e rest ih =>
    simp only [List.cons_append] at ⊢
    unfold neuestens
    rw [ih]

/-- Appending an entry for another address changes nothing at `a`. -/
theorem neuestens_angehaengt_anders (l : List TSOEintrag) (a : Adresse)
    (e : TSOEintrag) (h : e.addr ≠ a) :
    neuestens (l ++ [e]) a = neuestens l a := by
  induction l with
  | nil =>
    simp [neuestens, h]
  | cons f rest ih =>
    simp only [List.cons_append] at ⊢
    unfold neuestens
    rw [ih]

/-- A load after issuing the same address forwards the issued byte. -/
theorem load_nach_issue (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) (h : issueByte s c a v = some s')
    (hrd : s.mem.lesbar a = true) :
    loadByte s' c a = some v := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    have hbuf : pufferSetze s.puffer c (s.puffer c ++ [⟨a, v⟩]) c
        = s.puffer c ++ [⟨a, v⟩] := pufferSetze_gleich _ _ _
    simp only [loadByte, hbuf, hrd, if_true, neuestens_angehaengt]
  · rw [if_neg hc] at h
    cases h

/-- Without a pending entry the load reads canonical memory. -/
theorem load_ohne_eintrag (s : TSOZustand) (c : Nat) (a : Adresse)
    (hmiss : neuestens (s.puffer c) a = none)
    (hrd : s.mem.lesbar a = true) :
    loadByte s c a = some (s.mem.bytes a) := by
  unfold loadByte
  rw [if_pos hrd, hmiss]

/-! ## 6. FIFO order: issue appends youngest-last, flush drops oldest-first -/

/-- Issue appends exactly one entry at the young end. -/
theorem issue_haengt_an (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) (h : issueByte s c a v = some s') :
    s'.puffer c = s.puffer c ++ [⟨a, v⟩] := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    exact pufferSetze_gleich _ _ _
  · rw [if_neg hc] at h
    cases h

/-- Flush drops exactly the oldest entry. -/
theorem flush_entfernt_kopf (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s') (e : TSOEintrag)
    (rest : List TSOEintrag)
    (he : s.puffer c = e :: rest) :
    s'.puffer c = rest := by
  unfold flushKern at h
  rw [he] at h
  cases h
  exact pufferSetze_gleich _ _ _

/-- An older entry flushes before a younger one: after issuing two stores,
    the first flush writes the first address. -/
theorem fifo_reihenfolge (s s1 s2 s3 : TSOZustand) (c : Nat)
    (a b : Adresse) (v w : Byte)
    (h1 : issueByte s c a v = some s1)
    (h2 : issueByte s1 c b w = some s2)
    (hempty : s.puffer c = [])
    (h3 : flushKern s2 c = some s3) :
    s3.mem.bytes a = v := by
  have e1 := issue_haengt_an s s1 c a v h1
  have e2 := issue_haengt_an s1 s2 c b w h2
  rw [hempty] at e1
  simp only [List.nil_append] at e1
  rw [e1] at e2
  have he : s2.puffer c = ⟨a, v⟩ :: [⟨b, w⟩] := e2
  exact flush_schreibt_kopf s2 s3 c h3 ⟨a, v⟩ [⟨b, w⟩] he

/-! ## 7. Drain: fence readiness is local to the own buffer -/

/-- The fence is ready exactly when the own buffer is empty. -/
theorem zaunBereit_iff_leer (s : TSOZustand) (c : Nat) :
    zaunBereit s c = true ↔ s.puffer c = [] := by
  unfold zaunBereit
  cases h : s.puffer c with
  | nil =>
    simp
  | cons e rest =>
    simp

/-- Flushing the last entry makes the fence ready. -/
theorem zaun_nach_flush (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s') (e : TSOEintrag)
    (he : s.puffer c = [e]) :
    zaunBereit s' c = true := by
  have hbuf := flush_entfernt_kopf s s' c h e [] he
  rw [zaunBereit_iff_leer]
  simpa using hbuf

/-- Another core's issue never changes this core's fence readiness. -/
theorem zaun_fremd_issue (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte) (h : issueByte s c a v = some s')
    (d : Nat) (hd : d ≠ c) :
    zaunBereit s' d = zaunBereit s d := by
  have hbuf := issue_anderer_kern s s' c a v h hd
  unfold zaunBereit
  rw [hbuf]

/-- Another core's flush never changes this core's fence readiness. -/
theorem zaun_fremd_flush (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s')
    (d : Nat) (hd : d ≠ c) :
    zaunBereit s' d = zaunBereit s d := by
  have hbuf := flush_anderer_kern s s' c h hd
  unfold zaunBereit
  rw [hbuf]

/-- A local fence drains NO foreign buffer: core 0 can be fence-ready
    while core 1 still holds a pending store. -/
theorem zaun_kein_fremd_drain :
    ∃ s : TSOZustand, zaunBereit s 0 = true ∧ s.puffer 1 ≠ [] := by
  refine ⟨⟨zeugenSpeicher,
    fun d => if d = 1 then [⟨(0 : Adresse), BitVec.ofNat 8 1⟩] else []⟩, ?_, ?_⟩
  · decide
  · decide

/-! ## 8. Store-buffering witness over real canonical bytes -/

/-- The two witness addresses: bytes zero and one. -/
def sbX : Adresse := 0
def sbY : Adresse := 1

/-- The witness byte: one. -/
def sbEins : Byte := 1

/-- Start: zeroed fully-permissive memory, all buffers empty. -/
def sbStart : TSOZustand := ⟨zeugenSpeicher, fun _ => []⟩

/-- After core 0 issues `sbX := 1`. -/
def sbNach1 : TSOZustand :=
  ⟨zeugenSpeicher, pufferSetze sbStart.puffer 0 [⟨sbX, sbEins⟩]⟩

/-- After core 1 additionally issues `sbY := 1`. -/
def sbNach2 : TSOZustand :=
  ⟨sbNach1.mem, pufferSetze sbNach1.puffer 1 [⟨sbY, sbEins⟩]⟩

/-- After core 0 flushes its oldest entry. -/
def sbGespült : TSOZustand :=
  ⟨{ sbNach2.mem with
      bytes := fun x => if x = sbX then sbEins else sbNach2.mem.bytes x },
    pufferSetze sbNach2.puffer 0 []⟩

/-- The two addresses differ. -/
theorem sbX_ne_sbY : sbX ≠ sbY := by
  decide

/-- First issue step computes as claimed. -/
theorem sb_schritt1 : issueByte sbStart 0 sbX sbEins = some sbNach1 := by
  rfl

/-- Second issue step computes as claimed. -/
theorem sb_schritt2 : issueByte sbNach1 1 sbY sbEins = some sbNach2 := by
  rfl

/-- Both cores load the stale zero: each read misses its own buffer and
    sees canonical memory, which no flush has touched yet. -/
theorem sb_beide_laden_null :
    loadByte sbNach2 0 sbY = some 0 ∧ loadByte sbNach2 1 sbX = some 0 := by
  refine ⟨by decide, by decide⟩

/-- The flush step computes as claimed. -/
theorem sb_flush_schritt : flushKern sbNach2 0 = some sbGespült := by
  rfl

/-- The flush observably changes canonical memory at `sbX`. -/
theorem sb_flush_aendert_speicher :
    sbNach2.mem.bytes sbX ≠ sbGespült.mem.bytes sbX := by
  decide

/-- **Store buffering, reached, memory-changing.** From the empty start,
    two issue steps reach a state where both cores load `0` for the
    other's address, and flushing core 0 observably changes the
    canonical byte at `sbX`. -/
theorem tso_store_buffering :
    ∃ s0 s2 s3 : TSOZustand,
      TSOErreichbar s0 s2 ∧
      loadByte s2 0 sbY = some 0 ∧ loadByte s2 1 sbX = some 0 ∧
      flushKern s2 0 = some s3 ∧ s2.mem.bytes sbX ≠ s3.mem.bytes sbX := by
  exact ⟨sbStart, sbNach2, sbGespült,
    .schritt (.schritt .start (.issue _ _ _ _ _ sb_schritt1))
      (.issue _ _ _ _ _ sb_schritt2),
    sb_beide_laden_null.1, sb_beide_laden_null.2,
    sb_flush_schritt, sb_flush_aendert_speicher⟩

/-! ## 9. Packets: byte granularity tears; LOCK is refused -/

/-- Natural alignment: the byte address is divisible by `n`. -/
def Ausgerichtet (a : Adresse) (n : Nat) : Prop := a.toNat % n = 0

/-- When a multi-byte access WOULD be single-copy atomic on silicon:
    width 1, 2, 4 or 8, naturally aligned. Width 1 holds here (one
    entry, one flush); wider widths do NOT (see `paket_reisst`). -/
def paketAtomarMoeglich (a : Adresse) (n : Nat) : Prop :=
  (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) ∧ Ausgerichtet a n ∧ 0 < n

/-- Width 1 is always a candidate packet. -/
theorem paket_ein_byte (a : Adresse) :
    paketAtomarMoeglich a 1 := by
  refine ⟨Or.inl rfl, ?_, by decide⟩
  unfold Ausgerichtet
  exact Nat.mod_one _

/-- A single-entry flush changes exactly one address: the byte access
    is single-copy atomic by construction. -/
theorem einzelbyte_atomar (s s' : TSOZustand) (c : Nat)
    (h : flushKern s c = some s') (e : TSOEintrag)
    (he : s.puffer c = [e]) (x : Adresse) :
    s'.mem.bytes x = (if x = e.addr then e.wert else s.mem.bytes x) := by
  by_cases hx : x = e.addr
  · rw [if_pos hx, hx]
    exact flush_schreibt_kopf s s' c h e [] he
  · rw [if_neg hx]
    exact flush_rahmen s s' c h e [] he x hx

/-- **Tearing.** Two issued bytes flush one at a time: after the first
    flush the first address is new while the second still reads the
    pre-flush byte. No multi-byte atomicity is claimed at this layer,
    even for aligned packets: that bridge is OPEN. -/
theorem paket_reisst (s s1 s2 s3 : TSOZustand) (c : Nat)
    (a b : Adresse) (v w : Byte)
    (h1 : issueByte s c a v = some s1)
    (h2 : issueByte s1 c b w = some s2)
    (hempty : s.puffer c = [])
    (h3 : flushKern s2 c = some s3) (hne : a ≠ b) :
    s3.mem.bytes a = v ∧ s3.mem.bytes b = s2.mem.bytes b := by
  have e1 := issue_haengt_an s s1 c a v h1
  have e2 := issue_haengt_an s1 s2 c b w h2
  rw [hempty] at e1
  simp only [List.nil_append] at e1
  rw [e1] at e2
  have he : s2.puffer c = ⟨a, v⟩ :: [⟨b, w⟩] := e2
  exact ⟨flush_schreibt_kopf s2 s3 c h3 ⟨a, v⟩ [⟨b, w⟩] he,
    flush_rahmen s2 s3 c h3 ⟨a, v⟩ [⟨b, w⟩] he b (Ne.symm hne)⟩

/-- LOCK-prefixed read-modify-write has NO transition in this model:
    the inductive has no constructors, so no step is a LOCK step. -/
inductive LockSchritt : TSOZustand → TSOZustand → Prop

/-- Every LOCK claim is void inside this model. -/
theorem kein_lock_schritt (s s' : TSOZustand) :
    ¬ LockSchritt s s' := by
  intro h
  cases h

/-! ## 10. Link to the existing view model (`Sicht`) at byte granularity -/

/-- Singleton byte history: `a` holds one message with value `v`. -/
def tsoEineHist (a : Adresse) (v : Byte) :
    Adresse → List (Speichermodell.Nachricht Adresse Byte) :=
  fun x => if x = a then
    [⟨1, v, Speichermodell.Sicht.null⟩]
  else
    [⟨0, 0, Speichermodell.Sicht.null⟩]

/-- The singleton message is in the history at `a`. -/
theorem tsoEineHist_mem (a : Adresse) (v : Byte) :
    (⟨1, v, Speichermodell.Sicht.null⟩ :
      Speichermodell.Nachricht Adresse Byte) ∈ tsoEineHist a v a := by
  simp [tsoEineHist]

/-- The singleton message is readable in the view model: it is present
    and above the empty view. -/
theorem tsoEineHist_lesbar (a : Adresse) (v : Byte) :
    Speichermodell.Lesbar (tsoEineHist a v)
      Speichermodell.Sicht.null a
      ⟨1, v, Speichermodell.Sicht.null⟩ := by
  refine ⟨tsoEineHist_mem a v, ?_⟩
  exact Nat.zero_le 1

/-- **Target-side view link.** Every byte a TSO load returns is a
    `Lesbar` option of the existing `Sicht` model instantiated at
    bytes: the TSO load options (own-buffer forward or canonical
    memory) sit inside the view model's read options. This reuses
    `Lesbar` as stated; it maps NO source carrier and proves NO
    source-to-target simulation (see CUTS). -/
theorem tso_last_lesbar (s : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) (h : loadByte s c a = some v) :
    ∃ hist : Adresse → List (Speichermodell.Nachricht Adresse Byte),
      ∃ m, m ∈ hist a ∧ m.wert = v ∧
        Speichermodell.Lesbar hist Speichermodell.Sicht.null a m := by
  unfold loadByte at h
  by_cases hrd : s.mem.lesbar a = true
  · rw [if_pos hrd] at h
    cases hne : neuestens (s.puffer c) a with
    | none =>
      simp only [hne, Option.some.injEq] at h
      subst h
      exact ⟨tsoEineHist a (s.mem.bytes a), _,
        tsoEineHist_mem _ _, rfl, tsoEineHist_lesbar _ _⟩
    | some w =>
      simp only [hne, Option.some.injEq] at h
      subst h
      exact ⟨tsoEineHist a w, _,
        tsoEineHist_mem _ _, rfl, tsoEineHist_lesbar _ _⟩
  · rw [if_neg hrd] at h
    cases h

/-- Fresh timestamps exist at bytes: the `Frisch` shape an issue step
    needs (strictly above the view, unused) is inhabited. -/
theorem tso_frisch_beispiel (a : Adresse) :
    ∃ hist : Adresse → List (Speichermodell.Nachricht Adresse Byte),
      ∃ v, Speichermodell.Frisch hist v a 1 := by
  refine ⟨fun _ => [⟨0, 0, Speichermodell.Sicht.null⟩],
    Speichermodell.Sicht.null, ?_, ?_⟩
  · exact Nat.zero_lt_one
  · intro m hm
    simp at hm
    subst hm
    decide

/- CUTS:
   - No aligned multi-byte single-copy atomicity: `paket_reisst` shows a
     byte-wise flush tears a two-byte packet, so the silicon rule for
     widths 2/4/8 (`paketAtomarMoeglich` is a predicate only, with its
     alignment condition) has NO proved correspondence here; width 1 is
     atomic by construction (`einzelbyte_atomar`).
   - No LOCK RMW: `LockSchritt` is empty by construction
     (`kein_lock_schritt`); the exchange/CAS lowering and any `rmw`-field
     (`neu = wahl.ts + 1`) correspondence are OPEN wave-B bridge work.
   - No source-to-target simulation: `tso_last_lesbar` and
     `tso_frisch_beispiel` instantiate the EXISTING `Lesbar`/`Frisch` at
     target bytes only; the cross-granularity refinement from byte TSO
     accesses to carrier-granular W steps (`SchrittW` witnesses `wahl`/`neu`
     per G-step access list, O-access of TSO-GX-BRUECKE.md section 5) is
     NOT proved and NOT assumed.
   - No per-access linearisation of G steps, no lowering map, no run
     induction from x86 traces to W runs; `TSOErreichbar` is target-only.
   - No fairness, progress or timing claim: spins, CAS retries, flush
     liveness and cycle costs are out of scope; any `FortschrittG` or
     `ZeitAbX` transfer is OPEN.
   - No interrupt, device, MMIO or DMA model: handler-entry drains,
     foreign-footprint sorting and the OBS-5 publication obligations of
     TSO-GX-BRUECKE.md section 4.9 are OPEN.
   - Fences only gate (`zaunBereit`): no fence instruction semantics
     beyond the empty-own-buffer condition, and a local fence never drains
     foreign buffers (`zaun_kein_fremd_drain`, `zaun_fremd_issue`,
     `zaun_fremd_flush`).
   - No source SC claim: `tso_store_buffering` exhibits the non-SC
     outcome (both stale reads reachable); W/GX stay the source model.
-/

#print axioms pufferSetze_gleich
#print axioms pufferSetze_anders
#print axioms issue_erhaelt_berechtigungen
#print axioms flush_erhaelt_berechtigungen
#print axioms issue_anderer_kern
#print axioms flush_anderer_kern
#print axioms issue_kein_speicher
#print axioms flush_schreibt_kopf
#print axioms flush_rahmen
#print axioms issue_verweigert
#print axioms load_verweigert
#print axioms flush_leer
#print axioms neuestens_angehaengt
#print axioms neuestens_angehaengt_anders
#print axioms load_nach_issue
#print axioms load_ohne_eintrag
#print axioms issue_haengt_an
#print axioms flush_entfernt_kopf
#print axioms fifo_reihenfolge
#print axioms zaunBereit_iff_leer
#print axioms zaun_nach_flush
#print axioms zaun_fremd_issue
#print axioms zaun_fremd_flush
#print axioms zaun_kein_fremd_drain
#print axioms sbX_ne_sbY
#print axioms sb_schritt1
#print axioms sb_schritt2
#print axioms sb_beide_laden_null
#print axioms sb_flush_schritt
#print axioms sb_flush_aendert_speicher
#print axioms tso_store_buffering
#print axioms paket_ein_byte
#print axioms einzelbyte_atomar
#print axioms paket_reisst
#print axioms kein_lock_schritt
#print axioms tsoEineHist_mem
#print axioms tsoEineHist_lesbar
#print axioms tso_last_lesbar
#print axioms tso_frisch_beispiel

end Gabbro.Grammatik.X86
