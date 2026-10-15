/-
  File:      Grammatik/X86/FenceDrain.lean
  Subject:   Local drain over the canonical TSO pilot model (plan B4).

  Lane 344 (wave B, Lean-first): bounded local-drain iteration over the
  ONE canonical `TSOZustand` of `Grammatik.X86.TSO`, per-core FIFO facts,
  and the explicit NON-theorem that a local fence/drain never discharges
  a foreign buffer. No second IR, no second evaluator, no source change.
-/
import Grammatik.X86.TSO

namespace Gabbro.Grammatik.X86

/-- Bounded local drain: `n` oldest-first flushes on core `c`.
    `none` = the buffer ran empty before `n` steps. -/
def drainKernN : TSOZustand → Nat → Nat → Option TSOZustand
  | s, _, 0 => some s
  | s, c, n+1 =>
    match flushKern s c with
    | none => none
    | some s' => drainKernN s' c n

/-- Zero steps drain to the start state. -/
theorem drainKernN_null (s : TSOZustand) (c : Nat) :
    drainKernN s c 0 = some s := by
  rfl

/-- One drain step unfolds through the canonical `flushKern`. -/
theorem drainKernN_succ (s s' s'' : TSOZustand) (c n : Nat)
    (h1 : flushKern s c = some s')
    (h2 : drainKernN s' c n = some s'') :
    drainKernN s c (n + 1) = some s'' := by
  simp only [drainKernN, h1, h2]

/-- Draining core `c` never changes another core's buffer. -/
theorem drain_fremd_puffer (n : Nat) (s s' : TSOZustand) (c : Nat)
    {d : Nat} (hd : d ≠ c)
    (h : drainKernN s c n = some s') :
    s'.puffer d = s.puffer d := by
  induction n generalizing s s' with
  | zero =>
    simp only [drainKernN] at h
    cases h
    rfl
  | succ n ih =>
    simp only [drainKernN] at h
    cases hf : flushKern s c with
    | none =>
      rw [hf] at h
      cases h
    | some s1 =>
      rw [hf] at h
      simp only at h
      have h1 := ih s1 s' h
      have hframe := flush_anderer_kern s s1 c hf hd
      rw [h1, hframe]

/-- Full local drain: exactly as many steps as own entries. -/
def drainVoll (s : TSOZustand) (c : Nat) : Option TSOZustand :=
  drainKernN s c (s.puffer c).length

/-- Local fence admission as a decided `Bool`: ready exactly when the
    OWN buffer is empty. This is validator/profile admission, not a
    hardware fault and not a claim about any other core. -/
def mfenceZulaessig (s : TSOZustand) (c : Nat) : Bool :=
  zaunBereit s c

/-- A successful drain of at least the buffer length empties the own
    buffer. -/
theorem drainKernN_leert (n : Nat) (s s' : TSOZustand) (c : Nat)
    (hlen : (s.puffer c).length ≤ n)
    (h : drainKernN s c n = some s') :
    s'.puffer c = [] := by
  induction n generalizing s s' with
  | zero =>
    have hempty : s.puffer c = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [drainKernN] at h
    cases h
    exact hempty
  | succ n ih =>
    simp only [drainKernN] at h
    cases hf : flushKern s c with
    | none =>
      rw [hf] at h
      cases h
    | some s1 =>
      rw [hf] at h
      simp only at h
      cases hb : s.puffer c with
      | nil =>
        rw [flush_leer s c hb] at hf
        cases hf
      | cons e rest =>
        have htail : s1.puffer c = rest :=
          flush_entfernt_kopf s s1 c hf e rest hb
        have hlen2 : (s1.puffer c).length ≤ n := by
          rw [htail]
          rw [hb] at hlen
          simp at hlen ⊢
          omega
        exact ih s1 s' hlen2 h

/-- A successful full drain leaves the own buffer empty. -/
theorem drain_voll_leer (s s' : TSOZustand) (c : Nat)
    (h : drainVoll s c = some s') :
    s'.puffer c = [] := by
  unfold drainVoll at h
  exact drainKernN_leert _ s s' c (Nat.le_refl _) h

/-- A successful full drain makes the local fence ready. -/
theorem drain_voll_bereit (s s' : TSOZustand) (c : Nat)
    (h : drainVoll s c = some s') :
    zaunBereit s' c = true := by
  have hempty := drain_voll_leer s s' c h
  rw [zaunBereit_iff_leer]
  exact hempty

/-- NON-theorem (OBS-5 boundary): a local drain keeps every foreign
    pending entry pending. -/
theorem drain_laesst_fremd (n : Nat) (s s' : TSOZustand) (c : Nat)
    {d : Nat} (hd : d ≠ c)
    (h : drainKernN s c n = some s')
    (hp : s.puffer d ≠ []) :
    s'.puffer d ≠ [] := by
  have hframe := drain_fremd_puffer n s s' c hd h
  rw [hframe]
  exact hp

/-- FIFO order under local drain: two issues from empty, one drain
    step writes the older address and leaves the younger pending. -/
theorem drain_fifo_ordnung (s s1 s2 s3 : TSOZustand) (c : Nat)
    (a b : Adresse) (v w : Byte)
    (h1 : issueByte s c a v = some s1)
    (h2 : issueByte s1 c b w = some s2)
    (hempty : s.puffer c = [])
    (h3 : drainKernN s2 c 1 = some s3)
    (hne : a ≠ b) :
    s3.mem.bytes a = v ∧ s3.mem.bytes b = s2.mem.bytes b ∧
      s3.puffer c = [⟨b, w⟩] := by
  simp only [drainKernN] at h3
  cases hf : flushKern s2 c with
  | none =>
    rw [hf] at h3
    cases h3
  | some s3' =>
    rw [hf] at h3
    simp only at h3
    cases h3
    have e1 := issue_haengt_an s s1 c a v h1
    have e2 := issue_haengt_an s1 s2 c b w h2
    rw [hempty] at e1
    simp only [List.nil_append] at e1
    rw [e1] at e2
    have he : s2.puffer c = ⟨a, v⟩ :: [⟨b, w⟩] := e2
    refine ⟨flush_schreibt_kopf s2 s3 c hf ⟨a, v⟩ [⟨b, w⟩] he,
      flush_rahmen s2 s3 c hf ⟨a, v⟩ [⟨b, w⟩] he b (Ne.symm hne),
      flush_entfernt_kopf s2 s3 c hf ⟨a, v⟩ [⟨b, w⟩] he⟩

/-- REFUSAL (proved, not a prose caveat): a locally admitted fence does
    NOT discharge a foreign pending store. Concretely, core 0 can be
    fence-ready while core 1 still forwards its own buffered byte past
    canonical memory. No local `MFENCE` claim over a foreign or device
    read satisfies this shape. -/
theorem mfence_loest_fremd_nicht :
    ∃ (s : TSOZustand) (a : Adresse) (v : Byte),
      mfenceZulaessig s 0 = true ∧ s.puffer 1 ≠ [] ∧
      loadByte s 1 a = some v ∧ v ≠ s.mem.bytes a := by
  refine ⟨⟨zeugenSpeicher,
    fun d => if d = 1 then [⟨(0 : Adresse), BitVec.ofNat 8 7⟩] else []⟩,
    0, BitVec.ofNat 8 7, by decide, by decide, by decide, by decide⟩

/-! ## Two-core witness: local drain touches only the acting core -/

/-- Witness addresses: bytes zero and one. -/
def fdX : Adresse := 0
/-- Second witness address. -/
def fdY : Adresse := 1

/-- Witness values: one and seven. -/
def fdEins : Byte := 1
/-- Second witness value. -/
def fdSieben : Byte := 7

/-- Witness start: zeroed fully-permissive memory, all buffers empty. -/
def fdStart : TSOZustand := ⟨zeugenSpeicher, fun _ => []⟩

/-- After core 0 issues `fdX := 1`. -/
def fdS1 : TSOZustand :=
  ⟨zeugenSpeicher, pufferSetze fdStart.puffer 0 [⟨fdX, fdEins⟩]⟩

/-- After core 1 additionally issues `fdY := 7`. -/
def fdS2 : TSOZustand :=
  ⟨fdS1.mem, pufferSetze fdS1.puffer 1 [⟨fdY, fdSieben⟩]⟩

/-- After core 0 locally drains its single entry. -/
def fdS3 : TSOZustand :=
  ⟨{ fdS2.mem with
      bytes := fun x => if x = fdX then fdEins else fdS2.mem.bytes x },
    pufferSetze fdS2.puffer 0 []⟩

/-- First witness issue computes as claimed. -/
theorem fd_schritt1 : issueByte fdStart 0 fdX fdEins = some fdS1 := by
  rfl

/-- Second witness issue computes as claimed. -/
theorem fd_schritt2 : issueByte fdS1 1 fdY fdSieben = some fdS2 := by
  rfl

/-- The local drain step computes as claimed. -/
theorem fd_drain_schritt : drainKernN fdS2 0 1 = some fdS3 := by
  rfl

/-- The underlying canonical flush computes as claimed. -/
theorem fd_flush_schritt : flushKern fdS2 0 = some fdS3 := by
  rfl

/-- Before the drain, core 0 is not fence-ready. -/
theorem fd_vorher_nicht_bereit : zaunBereit fdS2 0 = false := by
  decide

/-- After the local drain, core 0 is fence-ready. -/
theorem fd_nachher_bereit : zaunBereit fdS3 0 = true := by
  decide

/-- The foreign buffer survives the local drain unchanged. -/
theorem fd_fremd_bleibt : fdS3.puffer 1 = fdS2.puffer 1 := by
  decide

/-- The foreign buffer is non-empty before and after. -/
theorem fd_fremd_wartend : fdS2.puffer 1 ≠ [] ∧ fdS3.puffer 1 ≠ [] := by
  refine ⟨by decide, by decide⟩

/-- The drain observably changes canonical memory at `fdX`. -/
theorem fd_speicher_aendert :
    fdS2.mem.bytes fdX ≠ fdS3.mem.bytes fdX := by
  decide

/-- Core 1 loads the stale zero for `fdX` before the drain. -/
theorem fd_fremd_liest_alt : loadByte fdS2 1 fdX = some 0 := by
  decide

/-- Core 1 loads the drained value for `fdX` after the drain. -/
theorem fd_fremd_liest_neu : loadByte fdS3 1 fdX = some fdEins := by
  decide

/-- Core 1's forwarded read of its OWN pending store is unaffected by
    the foreign drain. -/
theorem fd_eigen_bleibt : loadByte fdS2 1 fdY = loadByte fdS3 1 fdY := by
  decide

/-- The full local drain computes as claimed on the witness. -/
theorem fd_voll_schritt : drainVoll fdS2 0 = some fdS3 := by
  rfl

/-- **Witness: reached, memory-changing, local-only.** From the empty
    start, two issues reach a state where core 0 is not fence-ready;
    one local drain step makes core 0 fence-ready, leaves core 1's
    buffer byte-identical and still pending, observably changes the
    canonical byte at `fdX`, and moves core 1's load of `fdX` from the
    stale zero to the drained value. -/
theorem fd_lokal_nur :
    ∃ s2 s3 : TSOZustand,
      TSOErreichbar fdStart s2 ∧
      drainKernN s2 0 1 = some s3 ∧
      zaunBereit s2 0 = false ∧ zaunBereit s3 0 = true ∧
      s3.puffer 1 = s2.puffer 1 ∧ s3.puffer 1 ≠ [] ∧
      s2.mem.bytes fdX ≠ s3.mem.bytes fdX ∧
      loadByte s2 1 fdX = some 0 ∧ loadByte s3 1 fdX = some fdEins := by
  exact ⟨fdS2, fdS3,
    .schritt (.schritt .start (.issue _ _ _ _ _ fd_schritt1))
      (.issue _ _ _ _ _ fd_schritt2),
    fd_drain_schritt, fd_vorher_nicht_bereit, fd_nachher_bereit,
    fd_fremd_bleibt, fd_fremd_wartend.2,
    fd_speicher_aendert, fd_fremd_liest_alt, fd_fremd_liest_neu⟩

/-! ## Joint witnesses (`_zeuge`): every premise jointly inhabited -/

/-- Joint witness for `drain_fremd_puffer`: all premises together on a
    non-degenerate reached run with a memory-changing drain. -/
theorem drain_fremd_puffer_zeuge :
    ∃ (n : Nat) (s s' : TSOZustand) (c d : Nat),
      d ≠ c ∧ drainKernN s c n = some s' ∧
      s'.puffer d = s.puffer d ∧ s.puffer d ≠ [] ∧
      s.puffer c ≠ [] ∧ s'.puffer c = [] ∧
      s.mem.bytes fdX ≠ s'.mem.bytes fdX ∧
      TSOErreichbar fdStart s := by
  refine ⟨1, fdS2, fdS3, 0, 1, by decide, fd_drain_schritt, fd_fremd_bleibt,
    fd_fremd_wartend.1, by decide, by decide,
    fd_speicher_aendert, ?_⟩
  exact .schritt (.schritt .start (.issue _ _ _ _ _ fd_schritt1))
    (.issue _ _ _ _ _ fd_schritt2)

/-- Joint witness for `drain_voll_leer` / `drain_voll_bereit`: the full
    drain succeeds on a non-degenerate reached run and the fence flips. -/
theorem drain_voll_leer_zeuge :
    ∃ (s s' : TSOZustand) (c : Nat),
      drainVoll s c = some s' ∧ s.puffer c ≠ [] ∧ s'.puffer c = [] ∧
      zaunBereit s c = false ∧ zaunBereit s' c = true ∧
      s.mem.bytes fdX ≠ s'.mem.bytes fdX ∧
      TSOErreichbar fdStart s := by
  refine ⟨fdS2, fdS3, 0, fd_voll_schritt, by decide, by decide,
    fd_vorher_nicht_bereit, fd_nachher_bereit, fd_speicher_aendert, ?_⟩
  exact .schritt (.schritt .start (.issue _ _ _ _ _ fd_schritt1))
    (.issue _ _ _ _ _ fd_schritt2)

/-- Joint witness for `drain_laesst_fremd`: the foreign entry survives
    a successful local drain on a reached memory-changing run. -/
theorem drain_laesst_fremd_zeuge :
    ∃ (n : Nat) (s s' : TSOZustand) (c d : Nat),
      d ≠ c ∧ drainKernN s c n = some s' ∧ s.puffer d ≠ [] ∧
      s'.puffer d ≠ [] ∧ s.mem.bytes fdX ≠ s'.mem.bytes fdX ∧
      TSOErreichbar fdStart s := by
  refine ⟨1, fdS2, fdS3, 0, 1, by decide, fd_drain_schritt,
    fd_fremd_wartend.1, fd_fremd_wartend.2, fd_speicher_aendert, ?_⟩
  exact .schritt (.schritt .start (.issue _ _ _ _ _ fd_schritt1))
    (.issue _ _ _ _ _ fd_schritt2)

/- CUTS:
    - `drainKernN`/`drainVoll` iterate the ONE canonical `flushKern`;
      no second evaluator, no new memory, no source change.
    - `mfenceZulaessig` is a decided validator/profile admission Bool
      (own buffer empty), NOT a hardware fault and NOT a claim about
      any other core, device, MMIO or DMA.
    - No aligned multi-byte single-copy atomicity and no LOCK RMW are
      claimed here; per-byte TSO facts of `Grammatik.X86.TSO` are reused
      unchanged (`fifo_reihenfolge` shape via `drain_fifo_ordnung`).
    - No source-to-target simulation: no `W`/`GX` run induction, no
      lowering map, no per-access linearisation of G steps.
    - Spawn/join/handler visibility needs the publication lemma: OPEN.
      A fence alone publishes nothing; only flushed bytes become
      canonical (`fd_fremd_liest_neu` shows the flush, not the gate).
      O-irq/O-spawn close only their local half here.
    - No fairness, progress, timing or cycle-cost claim: drain liveness,
      CAS retry bounds and any `FortschrittG`/`ZeitAbX` transfer are OPEN.
    - No interrupt, device, MMIO or DMA model; a local fence discharging
      a foreign/device read is REFUSED (`mfence_loest_fremd_nicht`).
    - Actual x86 allows many unaligned ordinary accesses; this module
      imposes no alignment beyond what `TSO` already decides and keeps
      every refusal a `Bool`/`Option.none`, never an invented fault.
-/

#print axioms drainKernN_null
#print axioms drainKernN_succ
#print axioms drain_fremd_puffer
#print axioms drainKernN_leert
#print axioms drain_voll_leer
#print axioms drain_voll_bereit
#print axioms drain_laesst_fremd
#print axioms drain_fifo_ordnung
#print axioms mfence_loest_fremd_nicht
#print axioms fd_schritt1
#print axioms fd_schritt2
#print axioms fd_drain_schritt
#print axioms fd_flush_schritt
#print axioms fd_vorher_nicht_bereit
#print axioms fd_nachher_bereit
#print axioms fd_fremd_bleibt
#print axioms fd_fremd_wartend
#print axioms fd_speicher_aendert
#print axioms fd_fremd_liest_alt
#print axioms fd_fremd_liest_neu
#print axioms fd_eigen_bleibt
#print axioms fd_voll_schritt
#print axioms fd_lokal_nur
#print axioms drain_fremd_puffer_zeuge
#print axioms drain_voll_leer_zeuge
#print axioms drain_laesst_fremd_zeuge

end Gabbro.Grammatik.X86
