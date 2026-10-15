/-
  File:      Grammatik/X86/FeatureProfile.lean
  Subject:   Finite admitted performance-feature profile with fail-closed
             selection over the canonical width/FP/vector interfaces.

  Lane 424 (continuous Lean proof reserve): a small generic finite profile
  separating silicon support from control-state readiness, with proved
  fail-closed strict selection (refusal) and a proved scalar fallback for
  every optional feature. Existence never implies speed; the actual native
  extension bridge stays OPEN. Scalar fallback runs on the canonical
  `Speicher` words already proved elsewhere; nothing here re-proves them.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Gleitprofil
import Grammatik.X86.Vektor

namespace Gabbro.Grammatik.X86

/-- Finite admitted performance features: two scalar widths, scalar
    double (SSE2 DOUBLE family, f64 only) and one packed-integer tier. -/
inductive PerfMerkmal where
  | skalar64
  | skalar32
  | sseDoppel
  | paketInt128
  deriving DecidableEq, Repr, Inhabited

/-- The complete enumeration: every feature is listed here. -/
def alleMerkmale : List PerfMerkmal :=
  [.skalar64, .skalar32, .sseDoppel, .paketInt128]

/-- Silicon support: what the silicon HAS (instruction existence).
    Existence implies nothing about speed or readiness. -/
structure HwProfil where
  hatSkalar64 : Bool
  hatSkalar32 : Bool
  hatSseDoppel : Bool
  hatPaketInt : Bool
  deriving DecidableEq, Repr

/-- Control-state readiness: the actual MXCSR word plus whether the OS
    enabled vector state. Readiness is separate from silicon support. -/
structure BereitProfil where
  mxcsr : MXCSR
  osXmm : Bool
  deriving DecidableEq, Repr

/-- Silicon support at one feature: what the silicon HAS. -/
def hat : HwProfil → PerfMerkmal → Bool
  | hw, .skalar64 => hw.hatSkalar64
  | hw, .skalar32 => hw.hatSkalar32
  | hw, .sseDoppel => hw.hatSseDoppel
  | hw, .paketInt128 => hw.hatPaketInt

/-- Control-state readiness at one feature: scalar integer needs no
    control state; scalar double needs the MXCSR profile AND OS vector
    state; the packed-integer tier needs OS vector state only. -/
def bereit : BereitProfil → PerfMerkmal → Bool
  | _, .skalar64 => true
  | _, .skalar32 => true
  | b, .sseDoppel => mxcsrGueltig b.mxcsr && b.osXmm
  | b, .paketInt128 => b.osXmm

/-- Admission is the conjunction: silicon AND readiness. Either side
    alone admits nothing; existence never implies speed. -/
def merkmalZugelassen (hw : HwProfil) (b : BereitProfil) (m : PerfMerkmal) : Bool :=
  hat hw m && bereit b m

/-- Fail-closed strict selection: an unadmitted feature selects to
    nothing, never to a silent substitute. -/
def waehle (hw : HwProfil) (b : BereitProfil) (m : PerfMerkmal) :
    Option PerfMerkmal :=
  match merkmalZugelassen hw b m with
  | true => some m
  | false => none

/-- The enumeration is complete: every feature is listed. -/
theorem alleMerkmale_vollstaendig (m : PerfMerkmal) : m ∈ alleMerkmale := by
  cases m <;> decide

/-- Admission means both sides: silicon support and readiness. -/
theorem merkmalZugelassen_heisst_beide (hw : HwProfil) (b : BereitProfil)
    (m : PerfMerkmal) (h : merkmalZugelassen hw b m = true) :
    hat hw m = true ∧ bereit b m = true := by
  unfold merkmalZugelassen at h
  constructor
  · cases hh : hat hw m <;> simp_all
  · cases hb : bereit b m <;> simp_all

/-- Strict refusal: what is not admitted selects to nothing. -/
theorem waehle_verweigert_strikt (hw : HwProfil) (b : BereitProfil)
    (m : PerfMerkmal) (h : merkmalZugelassen hw b m = false) :
    waehle hw b m = none := by
  unfold waehle
  rw [h]

/-- Admitted selection returns exactly the requested feature. -/
theorem waehle_gibt_zurueck (hw : HwProfil) (b : BereitProfil)
    (m : PerfMerkmal) (h : merkmalZugelassen hw b m = true) :
    waehle hw b m = some m := by
  unfold waehle
  rw [h]

/-- Silicon without readiness admits nothing: support present, FTZ word
    in control state, OS state on -- the scalar-double feature refuses. -/
theorem hat_ohne_bereit_verweigert :
    ∃ (hw : HwProfil) (b : BereitProfil),
      hat hw .sseDoppel = true ∧ bereit b .sseDoppel = false :=
  ⟨⟨true, true, true, true⟩, ⟨0x9F80, true⟩, rfl, by decide⟩

/-- The baseline: full silicon, reset MXCSR word, OS vector state on. -/
def basisHw : HwProfil := ⟨true, true, true, true⟩

/-- Baseline readiness: the architectural reset word with OS state on. -/
def basisBereit : BereitProfil := ⟨0x1F80, true⟩

/-- The scalar 64-bit path is admitted on the baseline. -/
theorem basis_skalar_zugelassen :
    merkmalZugelassen basisHw basisBereit .skalar64 = true := rfl

/-- Scalar double refuses at every invalid control word, however
    complete the silicon: admission needs the MXCSR profile. -/
theorem sse_verweigert_ohne_profil (hw : HwProfil) (b : BereitProfil)
    (hh : hat hw .sseDoppel = true) (hmx : mxcsrGueltig b.mxcsr = false) :
    merkmalZugelassen hw b .sseDoppel = false := by
  simp [merkmalZugelassen, bereit, hh, hmx]

/-- Concrete case: the flush-to-zero word disarms the MXCSR profile,
    so the baseline refuses scalar double there. -/
theorem sse_verweigert_bei_ftz :
    merkmalZugelassen basisHw ⟨0x9F80, true⟩ .sseDoppel = false := by
  decide

/-- The packed-integer tier without OS vector state refuses, at every
    control word: readiness is not implied by silicon. -/
theorem paket_braucht_os (hw : HwProfil)
    (hh : hat hw .paketInt128 = true) (mx : MXCSR) :
    merkmalZugelassen hw ⟨mx, false⟩ .paketInt128 = false := by
  simp [merkmalZugelassen, bereit, hh]

/-- Even the scalar path refuses without silicon: readiness alone
    admits nothing. -/
theorem skalar_braucht_silizium (b : BereitProfil) :
    merkmalZugelassen ⟨false, true, true, true⟩ b .skalar64 = false := by
  cases b <;> rfl

/-- The canonical width each feature selects at: scalar and packed
    tiers over the existing `Breite` vocabulary. -/
def merkmalBreite : PerfMerkmal → Breite
  | .skalar64 => .b64
  | .skalar32 => .b32
  | .sseDoppel => .b64
  | .paketInt128 => .b32

/-- The scalar fallback path is the full 64-bit canonical width. -/
theorem skalar_fallback_breite :
    merkmalBreite .skalar64 = .b64
      ∧ Breite.bits (merkmalBreite .skalar64) = 64 := ⟨rfl, rfl⟩

/-- Fail-closed fallback: the requested feature when admitted, the
    proven scalar path otherwise. No silent substitute. -/
def fallback (hw : HwProfil) (b : BereitProfil) (m : PerfMerkmal) :
    PerfMerkmal :=
  match waehle hw b m with
  | some x => x
  | none => .skalar64

/-- A refused feature falls back to exactly the scalar path. -/
theorem fallback_verweigert_bleibt_skalar (hw : HwProfil)
    (b : BereitProfil) (m : PerfMerkmal)
    (href : waehle hw b m = none) :
    fallback hw b m = .skalar64 := by
  unfold fallback
  rw [href]

/-- Admission never implies atomicity: the admitted packed tier still
    carries memory as two ordered canonical 64-bit chunks with an
    observably mixed intermediate state (no vector atomicity, cf.
    `vecWrite_teilt`). Per-byte TSO is not multi-byte atomicity. -/
theorem aufnahme_kein_atomar (m m1 : Speicher) (a : Adresse)
    (v : Vektor) (h1 : write64 m a (vLo v) = some m1)
    (hrd1 : lesbar8 m a = true) (hno : OhneUmbruch16 a) :
    read64 m1 a = some (vLo v)
      ∧ read64 m1 (vecHiAddr a) = read64 m (vecHiAddr a) :=
  vecWrite_teilt m m1 a v h1 hrd1 hno

/-- Joint witness: the baseline admits the scalar path AND canonical
    memory observably changes through a nonzero write/read round-trip.
    The profile selects; the already-proved `Speicher` words move data. -/
theorem profil_skalar_zeuge :
    ∃ (hw : HwProfil) (b : BereitProfil) (m m' : Speicher)
      (a : Adresse) (v : Wort),
      waehle hw b .skalar64 = some .skalar64
        ∧ v ≠ 0 ∧ write64 m a v = some m'
        ∧ read64 m' a = some v ∧ m.bytes a ≠ m'.bytes a := by
  obtain ⟨m, m', a, v, hne, hwr, hrd, hchg⟩ := write_read_zeuge
  exact ⟨basisHw, basisBereit, m, m', a, v,
    by unfold waehle; rw [basis_skalar_zugelassen], hne, hwr, hrd, hchg⟩

/- CUTS: what is not proved here.

    - No native extension bridge: nothing here concludes anything about
      executed bytes, instruction semantics, decoder/encoder output, or
      measured speed. `hat` records claimed silicon existence; admission
      is a data predicate over two profiles, not a hardware probe.
      `SSEAdd32Entspricht` (Gleitprofil) stays the named open claim.
    - No source lowering: no correspondence between a Gabbro source form
      and any selected feature, no `Ty`/Spec/checker/emitter change, no
      budget transfer for the fallback path, no call-log (`FolgeG`)
      effect. `fallback` is a pure profile-level default, not a compiler
      pass.
    - No concurrency claim: the memory round-trip reuses the sequential
      `Speicher` lemmas; per-access TSO granularity, tearing beyond
      `aufnahme_kein_atomar`, and the GX refinement stay open.
    - MXCSR bit positions are stated from the Intel layout via the reused
      `mxcsrGueltig`, not verified against hardware here; sticky flags,
      NaN payloads, x87/FPCR, other rounding modes and OS context-switch
      semantics stay with Gleitprofil's CUTS.
    - Only four features are modelled (two scalar widths, scalar double
      f64, one packed-integer tier). AVX/AVX-512, other widths, FP vector
      lanes and feature dependencies (e.g. tiers implying each other)
      are not modelled.
-/

#print axioms alleMerkmale_vollstaendig
#print axioms merkmalZugelassen_heisst_beide
#print axioms waehle_verweigert_strikt
#print axioms waehle_gibt_zurueck
#print axioms hat_ohne_bereit_verweigert
#print axioms basis_skalar_zugelassen
#print axioms sse_verweigert_ohne_profil
#print axioms sse_verweigert_bei_ftz
#print axioms paket_braucht_os
#print axioms skalar_braucht_silizium
#print axioms skalar_fallback_breite
#print axioms fallback_verweigert_bleibt_skalar
#print axioms aufnahme_kein_atomar
#print axioms profil_skalar_zeuge

end Gabbro.Grammatik.X86
