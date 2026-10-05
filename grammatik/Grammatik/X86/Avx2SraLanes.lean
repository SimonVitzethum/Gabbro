/-
  File:      Grammatik/X86/Avx2SraLanes.lean
  Subject:   AVX2 arithmetic shift right: per-lane equation on the coherent machine.

  Lane 1267 (follow-up of lane 1239 `Avx2Ops.lean`): `vecSraImm`/`sraLane`
  had witnesses only, no per-lane equation in the admitted range. This file
  proves the per-lane equation for VPSRAW/VPSRAD by immediate (sign fill,
  count >= width saturates to the sign), lane separation, and half agreement
  with the accepted evaluator (the old evaluator is lifted, never redefined).
  `.b8` shifts and `.b64` arithmetic have no AVX2 VEX encoding: they are a
  refusal by type (`SraBreite` has no such constructor), not a semantics.

  Manual provenance (checked 2026-10-05, clone-local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  Intel SDM 325462-093US September 2026): PSRAW/D `COUNT > 15/31` clamps
  so lanes become their sign fill; VPSRAQ exists EVEX-only, never VEX
  (see the line citations in `Avx2Ops.lean`). No page or quotation beyond
  those lines is claimed; silicon correspondence stays OPEN (see CUTS).
-/
import Grammatik.X86.Avx2Ops
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Admitted AVX2 arithmetic-shift widths: W (VPSRAW) and D (VPSRAD).
    `.b8` shifts and `.b64` arithmetic have no AVX2 VEX encoding, so they
    have no constructor here: refused by type, never silently substituted. -/
inductive SraBreite where
  | w16
  | w32
  deriving DecidableEq, Repr, Inhabited

/-- The lane width an admitted form shifts. -/
def SraBreite.breite : SraBreite → Breite
  | .w16 => .b16
  | .w32 => .b32

/-! ## 1. Refused widths: no `.b8`, no `.b64`.

  `.b8` shifts and `.b64` arithmetic have no AVX2 VEX encoding
  (VPSRAQ is EVEX-only; no byte immediate shift exists -- see the
  provenance in `Avx2Ops.lean`). The refusal is by type: `SraBreite`
  has no such constructor, so no producer can name them. -/

/-- No admitted form shifts bytes: every `SraBreite` misses `.b8`. -/
theorem sraBreite_kein_b8 (s : SraBreite) : s.breite ≠ .b8 := by
  cases s <;> decide

/-- No admitted form is a quadword arithmetic shift: every `SraBreite`
    misses `.b64`. -/
theorem sraBreite_kein_b64 (s : SraBreite) : s.breite ≠ .b64 := by
  cases s <;> decide

/-! ## 2. Half agreement and lane separation.

  Each 256-bit half IS the accepted 128-bit half shift (`ymmSra`
  from `Avx2Ops.lean`, lifted unchanged); each result lane depends
  only on its same-lane input, in its own half. -/

/-- Both halves of a 256-bit arithmetic shift are the accepted half shift. -/
theorem ymmSra_halb (b : Breite) (x : Ymm) (c : Nat) :
    (ymmSra b x c).1 = vecSraImm b x.1 c ∧
      (ymmSra b x c).2 = vecSraImm b x.2 c := ⟨rfl, rfl⟩

/-- Lane separation for one 128-bit arithmetic half: the result lane
    depends only on the same-lane input. -/
theorem vecSra_allein (b : Breite) (v v' : Vektor) (c i : Nat)
    (h : laneNat b v i = laneNat b v' i)
    (hi : i < laneCount b) :
    laneNat b (vecSraImm b v c) i =
      laneNat b (vecSraImm b v' c) i := by
  unfold vecSraImm
  by_cases hc : b.bits ≤ c
  · simp only [if_pos hc, laneGet_mk b _ i hi, h]
  · simp only [if_neg hc, laneGet_mk b _ i hi, h]

/-- Lane separation for the 256-bit arithmetic shift, low half. -/
theorem ymmSra_allein_lo (b : Breite) (x x' : Ymm) (c i : Nat)
    (hx : laneNat b x.1 i = laneNat b x'.1 i)
    (hi : i < laneCount b) :
    laneNat b (ymmSra b x c).1 i =
      laneNat b (ymmSra b x' c).1 i :=
  vecSra_allein b x.1 x'.1 c i hx hi

/-- Lane separation for the 256-bit arithmetic shift, high half. -/
theorem ymmSra_allein_hi (b : Breite) (x x' : Ymm) (c i : Nat)
    (hx : laneNat b x.2 i = laneNat b x'.2 i)
    (hi : i < laneCount b) :
    laneNat b (ymmSra b x c).2 i =
      laneNat b (ymmSra b x' c).2 i :=
  vecSra_allein b x.2 x'.2 c i hx hi

/-! ## 3. Per-lane equation: admitted range and saturation.

  Below the width the result lane is the two's-complement lane shift
  `sraLane`; at or past the width every lane becomes its sign fill
  (zero for a positive lane, all-ones for a negative lane -- the SDM
  clamp of PSRAW/D to 16/32). -/

/-- PER-LANE EQUATION (admitted range): below the width, the result
    lane is the two's-complement lane shift. -/
theorem laneNat_sraImm (b : Breite) (v : Vektor) (c i : Nat)
    (hc : ¬ b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (vecSraImm b v c) i =
      sraLane b.bits (laneNat b v i) c % 2 ^ b.bits := by
  unfold vecSraImm
  rw [if_neg hc]
  exact laneGet_mk b _ i hi

/-- SATURATION (count at/past the width): the result lane is its sign
    fill -- zero for a positive lane, all-ones for a negative lane. -/
theorem laneNat_sraImm_satt (b : Breite) (v : Vektor) (c i : Nat)
    (hc : b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (vecSraImm b v c) i =
      (if laneNat b v i < 2 ^ (b.bits - 1) then 0
        else 2 ^ b.bits - 1) := by
  unfold vecSraImm
  rw [if_pos hc, laneGet_mk b _ i hi]
  by_cases h : laneNat b v i < 2 ^ (b.bits - 1)
  · rw [if_pos h, Nat.zero_mod]
  · rw [if_neg h]
    exact Nat.mod_eq_of_lt (by have hpos := laneMod_pos b; omega)

/-- A saturated negative lane is all-ones (sign fill). -/
theorem laneNat_sraImm_satt_neg (b : Breite) (v : Vektor) (c i : Nat)
    (hc : b.bits ≤ c) (hi : i < laneCount b)
    (hsign : ¬ laneNat b v i < 2 ^ (b.bits - 1)) :
    laneNat b (vecSraImm b v c) i = 2 ^ b.bits - 1 := by
  rw [laneNat_sraImm_satt b v c i hc hi, if_neg hsign]

/-- A saturated positive lane is zero. -/
theorem laneNat_sraImm_satt_pos (b : Breite) (v : Vektor) (c i : Nat)
    (hc : b.bits ≤ c) (hi : i < laneCount b)
    (hsign : laneNat b v i < 2 ^ (b.bits - 1)) :
    laneNat b (vecSraImm b v c) i = 0 := by
  rw [laneNat_sraImm_satt b v c i hc hi, if_pos hsign]

/-- 256-bit per-lane equation, low half, admitted range. -/
theorem ymmSra_lane_lo (b : Breite) (x : Ymm) (c i : Nat)
    (hc : ¬ b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (ymmSra b x c).1 i =
      sraLane b.bits (laneNat b x.1 i) c % 2 ^ b.bits :=
  laneNat_sraImm b x.1 c i hc hi

/-- 256-bit per-lane equation, high half, admitted range. -/
theorem ymmSra_lane_hi (b : Breite) (x : Ymm) (c i : Nat)
    (hc : ¬ b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (ymmSra b x c).2 i =
      sraLane b.bits (laneNat b x.2 i) c % 2 ^ b.bits :=
  laneNat_sraImm b x.2 c i hc hi

/-- 256-bit saturation, low half: the lane is its sign fill. -/
theorem ymmSra_satt_lo (b : Breite) (x : Ymm) (c i : Nat)
    (hc : b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (ymmSra b x c).1 i =
      (if laneNat b x.1 i < 2 ^ (b.bits - 1) then 0
        else 2 ^ b.bits - 1) :=
  laneNat_sraImm_satt b x.1 c i hc hi

/-- 256-bit saturation, high half: the lane is its sign fill. -/
theorem ymmSra_satt_hi (b : Breite) (x : Ymm) (c i : Nat)
    (hc : b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (ymmSra b x c).2 i =
      (if laneNat b x.2 i < 2 ^ (b.bits - 1) then 0
        else 2 ^ b.bits - 1) :=
  laneNat_sraImm_satt b x.2 c i hc hi

/-! ## 4. Witness values (all `decide`).

  Every witness pins a concrete admitted or saturated shift at both
  widths, with a carrying lane beside an independent one. -/

/-- ADMITTED word shift: `0xFF00 (-256) >> 4 = 0xFFF0 (-16)`. -/
theorem vecSra_spur_wort :
    laneNat .b16 (vecSraImm .b16 (vecMk .b16 (fun _ => 0xFF00)) 4) 0 =
      0xFFF0 := by
  decide

/-- ADMITTED dword shift: `0x80000000 >> 1 = 0xC0000000` (sign bit
    replicated into the top). -/
theorem vecSra_spur_dwort :
    laneNat .b32 (vecSraImm .b32 (vecMk .b32 (fun _ => 0x80000000)) 1) 0 =
      0xC0000000 := by
  decide

/-- SATURATED negative word lane is all-ones. -/
theorem vecSra_spur_saettigung_neg :
    laneNat .b16
      (vecSraImm .b16
        (vecMk .b16 (fun i => if i = 0 then 0x8000 else 0x0001)) 20) 0 =
      0xFFFF := by
  decide

/-- SATURATED positive word lane is zero. -/
theorem vecSra_spur_saettigung_pos :
    laneNat .b16
      (vecSraImm .b16
        (vecMk .b16 (fun i => if i = 0 then 0x8000 else 0x0001)) 20) 1 =
      0 := by
  decide

/-- SATURATED negative dword lane is all-ones. -/
theorem vecSra_spur_dwort_saettigung :
    laneNat .b32 (vecSraImm .b32 (vecMk .b32 (fun _ => 0x80000000)) 40) 0 =
      0xFFFFFFFF := by
  decide

/-! ## 5. The family on the coherent machine.

  The two 128-bit halves ride two XMM registers of one core (`dstLo`
  the low half, `dstHi` the high half) through the accepted half
  shift; profiles are untouched, so `HwWf` survives. RIP is unchanged:
  no VEX decoder is constructed here, so no length advance is claimed
  (see CUTS). The family is register-only: canonical memory never
  moves under an SRA step. -/

/-- Follower update: both halves shift in place over the core
    projection; canonical memory and RIP are kept. -/
def sraFolge (t : FpZustand) (dstLo dstHi : XmmReg) (s : SraBreite)
    (imm : Nat) : FpZustand :=
  let lo := vecSraImm s.breite (t.xmm dstLo) imm
  let hi := vecSraImm s.breite (t.xmm dstHi) imm
  { t with xmm := xmmSet (xmmSet t.xmm dstLo lo) dstHi hi }

/-- The follower keeps canonical memory (register path only). -/
theorem sraFolge_speicher (t : FpZustand) (dstLo dstHi : XmmReg)
    (s : SraBreite) (imm : Nat) :
    (sraFolge t dstLo dstHi s imm).kern.speicher =
      t.kern.speicher := rfl

/-- Register successor on the machine: the accepted half shift over the
    core projection, re-embedded as core data. `none` is a refused
    Tier-3 gate, never a silent substitution. -/
def sraRegSchritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (dstLo dstHi : XmmReg)
    (s : SraBreite) (imm : Nat) : Option HwMaschine :=
  if avx2TierZugelassen m.hw (m.bereit c) cpu x k then
    some (setKernVonFp m c (sraFolge (projFp m c) dstLo dstHi s imm))
  else none

/-- The plug IS the accepted shift: success unfolds to the follower. -/
theorem sraRegSchritt_gleich (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (dstLo dstHi : XmmReg)
    (s : SraBreite) (imm : Nat)
    (hgate : avx2TierZugelassen m.hw (m.bereit c) cpu x k = true) :
    sraRegSchritt m c cpu x k dstLo dstHi s imm =
      some (setKernVonFp m c (sraFolge (projFp m c) dstLo dstHi s imm)) := by
  unfold sraRegSchritt
  simp [hgate]

/-- Refused Tier-3 admission refuses the plug (validator admission,
    not a hardware fault). -/
theorem sraRegSchritt_profil_verweigert (m : HwMaschine) (c : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (dstLo dstHi : XmmReg) (s : SraBreite) (imm : Nat)
    (h : avx2TierZugelassen m.hw (m.bereit c) cpu x k = false) :
    sraRegSchritt m c cpu x k dstLo dstHi s imm = none := by
  unfold sraRegSchritt
  simp [h]

/-- The low half write IS the accepted half shift (distinct halves). -/
theorem sraFolge_lo (t : FpZustand) (lo hi : XmmReg) (s : SraBreite)
    (imm : Nat) (h : lo ≠ hi) :
    (sraFolge t lo hi s imm).xmm lo =
      vecSraImm s.breite (t.xmm lo) imm := by
  have h1 : (sraFolge t lo hi s imm).xmm =
    xmmSet (xmmSet t.xmm lo (vecSraImm s.breite (t.xmm lo) imm)) hi
      (vecSraImm s.breite (t.xmm hi) imm) := rfl
  rw [h1, xmmSet_fremd _ _ _ _ h, xmmSet_gleich]

/-- The high half write IS the accepted half shift (no side condition:
    the high write is youngest). -/
theorem sraFolge_hi (t : FpZustand) (lo hi : XmmReg) (s : SraBreite)
    (imm : Nat) :
    (sraFolge t lo hi s imm).xmm hi =
      vecSraImm s.breite (t.xmm hi) imm := by
  have h1 : (sraFolge t lo hi s imm).xmm =
    xmmSet (xmmSet t.xmm lo (vecSraImm s.breite (t.xmm lo) imm)) hi
      (vecSraImm s.breite (t.xmm hi) imm) := rfl
  rw [h1, xmmSet_gleich]

/-- The low half write IS the 256-bit low half (lifted, never redefined). -/
theorem sraFolge_ymm_lo (t : FpZustand) (lo hi : XmmReg) (s : SraBreite)
    (imm : Nat) (h : lo ≠ hi) :
    (sraFolge t lo hi s imm).xmm lo =
      (ymmSra s.breite (t.xmm lo, t.xmm hi) imm).1 :=
  sraFolge_lo t lo hi s imm h

/-- The high half write IS the 256-bit high half. -/
theorem sraFolge_ymm_hi (t : FpZustand) (lo hi : XmmReg) (s : SraBreite)
    (imm : Nat) :
    (sraFolge t lo hi s imm).xmm hi =
      (ymmSra s.breite (t.xmm lo, t.xmm hi) imm).2 :=
  sraFolge_hi t lo hi s imm

/-! ## 6. Events, adapter plug, and the extended step relation.

  The family's event type carries the checked CPU/control inputs, so
  the adapter checks them per step, never assuming them. The extended
  relation embeds `HwSchritt` exactly (`alt`, with projection back)
  and adds the checked SRA register shift (`sra`, memory-unchanged
  like `HwSchritt.reg`). -/

/-- SRA family events on the coherent machine: the checked shift over
    two XMM halves, the old machine events, and explicit refusal. -/
inductive HwSraEreignis where
  | hwAlt : HwEreignis → HwSraEreignis
  | sraReg : Nat → CpuMerkmal → Xcr0Bild → KontrollBild → XmmReg →
      XmmReg → SraBreite → Nat → HwSraEreignis
  | verweigert : Nat → HwSraEreignis
  deriving DecidableEq, Repr

/-- The SRA producer plug: the checked shift on its own core,
    everything else refused. A mismatched core is refused, never
    rerouted. -/
def adapterSra : HwAdapter HwSraEreignis :=
  ⟨fun m c e => match e with
    | .sraReg c' cpu x k lo hi s imm =>
      if c' = c then sraRegSchritt m c cpu x k lo hi s imm else none
    | _ => none⟩

/-- The extended step relation: the old coherent steps exactly
    (`alt`) and the checked SRA register shift (`sra`). -/
inductive HwSraSchritt : HwMaschine → HwMaschine → HwSraEreignis → Prop where
  | alt {m m' : HwMaschine} {e : HwEreignis} (h : HwSchritt m m' e) :
      HwSraSchritt m m' (.hwAlt e)
  | sra {m : HwMaschine} {c : Nat} {cpu : CpuMerkmal} {x : Xcr0Bild}
      {k : KontrollBild} {lo hi : XmmReg} {s : SraBreite} {imm : Nat}
      {t' : FpZustand}
      (hgate : avx2TierZugelassen m.hw (m.bereit c) cpu x k = true)
      (hstep : sraFolge (projFp m c) lo hi s imm = t')
      (hmem : t'.kern.speicher = m.mem) :
      HwSraSchritt m (setKernVonFp m c t') (.sraReg c cpu x k lo hi s imm)

/-- Every extended step preserves well-formedness: core-data and
    memory/buffer updates alike leave the checked profiles untouched. -/
theorem hwSraSchritt_wf (m m' : HwMaschine) (e : HwSraEreignis)
    (h : HwSraSchritt m m' e) (hwf : HwWf m) : HwWf m' := by
  cases h with
  | alt h => exact hwSchritt_wf _ _ _ h hwf
  | sra hgate hstep hmem => exact setKernDaten_wf _ _ _ hwf

/-- Exact embedding: every old coherent step is an extended step. -/
theorem hwSraSchritt_einbettet (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) : HwSraSchritt m m' (.hwAlt e) :=
  .alt h

/-- Exact projection: an embedded step is the old step back. -/
theorem hwSraSchritt_projiziert (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSraSchritt m m' (.hwAlt e)) : HwSchritt m m' e := by
  cases h with
  | alt h => exact h

/-- The adapter refuses old events: nothing is admitted silently. -/
theorem adapterSra_verweigert_alt (m : HwMaschine) (c : Nat)
    (e : HwEreignis) :
    adapterSra.schritt m c (.hwAlt e) = none := rfl

/-- The adapter refuses bare refusals. -/
theorem adapterSra_verweigert_fehler (m : HwMaschine) (c d : Nat) :
    adapterSra.schritt m c (.verweigert d) = none := rfl

/-- The adapter refuses a mismatched core, never rerouting it. -/
theorem adapterSra_fremder_kern (m : HwMaschine) (c c' : Nat)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (lo hi : XmmReg) (s : SraBreite) (imm : Nat) (h : c' ≠ c) :
    adapterSra.schritt m c
      (.sraReg c' cpu x k lo hi s imm) = none := by
  unfold adapterSra
  simp [h]

/-- A plug success with the checked gate IS an extended step. -/
theorem sraReg_ist_schritt (m : HwMaschine) (c : Nat) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) (lo hi : XmmReg) (s : SraBreite)
    (imm : Nat) (t' : FpZustand)
    (hgate : avx2TierZugelassen m.hw (m.bereit c) cpu x k = true)
    (hstep : sraFolge (projFp m c) lo hi s imm = t')
    (hmem : t'.kern.speicher = m.mem) :
    HwSraSchritt m (setKernVonFp m c t')
      (.sraReg c cpu x k lo hi s imm) :=
  .sra hgate hstep hmem

/-! ## 7. Reached two-core witness.

  Core 0 shifts an admitted word-lane pair by 4; core 1 shifts a
  saturating pair by 20. Both steps change XMM state on their core and
  keep canonical memory (the family is register-only). A third step is
  an embedded base-machine store issue (`alt`), whose byte is visible
  to the owner through forwarding while the foreign core still reads
  canonical memory -- the machine-level memory path beside the family.
  The memory-changing step belongs to the base machine, honestly
  attributed via `alt`, never claimed as an SRA effect. -/

/-- Witness shared memory: one readable/writable byte at 8192, zeroed. -/
def hsraWitMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0,
    lesbar := fun a => decide (a.toNat = 8192),
    schreibbar := fun a => decide (a.toNat = 8192),
    ausfuehrbar := fun _ => false }

/-- Witness core-0 XMM: negative word lanes in xmm0, positive in xmm1. -/
def hsraWitXmm0 : XmmDatei := fun q =>
  if q = .xmm0 then vecMk .b16 (fun _ => 0xFF00)
  else if q = .xmm1 then vecMk .b16 (fun _ => 0x0001)
  else BitVec.ofNat 128 0

/-- Witness core-1 XMM: saturation operands in xmm2/xmm3. -/
def hsraWitXmm1 : XmmDatei := fun q =>
  if q = .xmm2 then vecMk .b16 (fun _ => 0x8000)
  else if q = .xmm3 then vecMk .b16 (fun _ => 0x0001)
  else BitVec.ofNat 128 0

/-- Witness registers: the witness byte address in rax. -/
def hsraWitReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 runs the admitted shift, core 1 the
    saturating shift. -/
def hsraWitKern : Nat → HwKern
  | 0 => ⟨hsraWitReg, zeugeFlags, BitVec.ofNat 64 4096, hsraWitXmm0,
      kontextReset⟩
  | _ => ⟨hsraWitReg, zeugeFlags, BitVec.ofNat 64 8192, hsraWitXmm1,
      kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    Tier-3 AVX2 silicon with OS vector state. -/
def hsraWitStart : HwMaschine :=
  ⟨hsraWitMem, hsraWitKern, fun _ => [], basisHw, fun _ => vecZeugeBereit⟩

/-- Witness store address. -/
def hsraWitAdr : Adresse := BitVec.ofNat 64 8192

/-- The Tier-3 gate admits at the witness profiles. -/
theorem hsraWit_gate :
    avx2TierZugelassen hsraWitStart.hw (hsraWitStart.bereit 0) avx2Cpu
      avx2Xcr0 basisKontrolle = true :=
  avx2Tier_basis_zugelassen

/-- The witness machine is well-formed: full silicon admits all. -/
theorem hsraWitStart_wf : HwWf hsraWitStart := by
  intro c f _
  cases f <;> rfl

/-- Explicit follower after core 0 shifts W lanes by 4. -/
def hsraWitT1 : FpZustand :=
  sraFolge (projFp hsraWitStart 0) .xmm0 .xmm1 .w16 4

/-- Explicit machine successor after the core-0 shift. -/
def hsraWitM1 : HwMaschine := setKernVonFp hsraWitStart 0 hsraWitT1

/-- The Tier-3 gate still admits over the core-0 successor: profiles
    are untouched by core-data updates. -/
theorem hsraWit_gate_m1 :
    avx2TierZugelassen hsraWitM1.hw (hsraWitM1.bereit 1) avx2Cpu
      avx2Xcr0 basisKontrolle = true :=
  avx2Tier_basis_zugelassen

/-- First witness step: the admitted shift on core 0. -/
theorem hsraWit_schritt1 :
    HwSraSchritt hsraWitStart hsraWitM1
      (.sraReg 0 avx2Cpu avx2Xcr0 basisKontrolle .xmm0 .xmm1 .w16 4) :=
  .sra hsraWit_gate rfl rfl

/-- Explicit follower after core 1 shifts W lanes by 20 (saturated). -/
def hsraWitT2 : FpZustand :=
  sraFolge (projFp hsraWitM1 1) .xmm2 .xmm3 .w16 20

/-- Explicit machine successor after the core-1 shift. -/
def hsraWitM2 : HwMaschine := setKernVonFp hsraWitM1 1 hsraWitT2

/-- Second witness step: the saturating shift on core 1. -/
theorem hsraWit_schritt2 :
    HwSraSchritt hsraWitM1 hsraWitM2
      (.sraReg 1 avx2Cpu avx2Xcr0 basisKontrolle .xmm2 .xmm3 .w16 20) :=
  .sra hsraWit_gate_m1 rfl rfl

/-! ## 8. Computed outcomes and lane pins (all `decide`).

  The plugs run over the witness machine; each pin reads one
  observation (lane value, memory byte, buffer length, forwarded
  load) out of the computed outcome. -/

/-- First plug outcome: the admitted shift on core 0. -/
def hsraWitR1 : Option HwMaschine :=
  sraRegSchritt hsraWitStart 0 avx2Cpu avx2Xcr0 basisKontrolle .xmm0
    .xmm1 .w16 4

/-- Second plug outcome: the saturating shift on core 1 over the first. -/
def hsraWitR2 : Option HwMaschine :=
  match hsraWitR1 with
  | some m1 => sraRegSchritt m1 1 avx2Cpu avx2Xcr0 basisKontrolle .xmm2
      .xmm3 .w16 20
  | none => none

/-- Third outcome: one base-machine byte issue on core 0 over the two
    shifts (the `alt` memory path, computed). -/
def hsraWitM3 : Option HwMaschine :=
  match issueByte (tsoAnsicht hsraWitM2) 0 hsraWitAdr
    (BitVec.ofNat 8 0xA5) with
  | some s' => some (setTso hsraWitM2 s')
  | none => none

/-- Read a word lane out of a machine outcome. -/
def hsraLaneOut (o : Option HwMaschine) (c : Nat) (q : XmmReg)
    (i : Nat) : Option Nat :=
  match o with
  | some m => some (laneNat .b16 ((m.kerne c).xmm q) i)
  | none => none

/-- Read a shared-memory byte out of a machine outcome. -/
def hsraMemOut (o : Option HwMaschine) (a : Adresse) : Option Byte :=
  match o with
  | some m => some (m.mem.bytes a)
  | none => none

/-- Read a TSO buffer length out of a machine outcome. -/
def hsraBufOut (o : Option HwMaschine) (c : Nat) : Option Nat :=
  match o with
  | some m => some (m.puffer c).length
  | none => none

/-- Read a forwarded byte load out of a machine outcome. -/
def hsraLoadOut (o : Option HwMaschine) (c : Nat) : Option Byte :=
  match o with
  | some m => loadByte (tsoAnsicht m) c hsraWitAdr
  | none => none

/-- Step one shifts the negative lane to its admitted value
    (`0xFF00 >> 4 = 0xFFF0`). -/
theorem hsraWit_r1_lo :
    hsraLaneOut hsraWitR1 0 .xmm0 0 = some 0xFFF0 := by
  decide

/-- Step one shifts the positive lane down (`0x0001 >> 4 = 0`). -/
theorem hsraWit_r1_hi :
    hsraLaneOut hsraWitR1 0 .xmm1 7 = some 0 := by
  decide

/-- Step one leaves shared memory alone (register-only family). -/
theorem hsraWit_r1_mem_still :
    hsraMemOut hsraWitR1 hsraWitAdr = some (BitVec.ofNat 8 0) := by
  decide

/-- Step two saturates the negative lane to all-ones. -/
theorem hsraWit_r2_lo :
    hsraLaneOut hsraWitR2 1 .xmm2 0 = some 0xFFFF := by
  decide

/-- Step two saturates the positive lane to zero. -/
theorem hsraWit_r2_hi :
    hsraLaneOut hsraWitR2 1 .xmm3 5 = some 0 := by
  decide

/-- The embedded issue buffers exactly one byte on core 0. -/
theorem hsraWit_m3_buf : hsraBufOut hsraWitM3 0 = some 1 := by
  decide

/-- The owner sees its buffered byte via forwarding. -/
theorem hsraWit_m3_fwd_eigen :
    hsraLoadOut hsraWitM3 0 = some (BitVec.ofNat 8 0xA5) := by
  decide

/-- The foreign core still reads canonical memory (owner-only
    forwarding). -/
theorem hsraWit_m3_fwd_fremd :
    hsraLoadOut hsraWitM3 1 = some (BitVec.ofNat 8 0) := by
  decide

/-- The issue changes no canonical byte (buffer only). -/
theorem hsraWit_m3_mem_still :
    hsraMemOut hsraWitM3 hsraWitAdr = some (BitVec.ofNat 8 0) := by
  decide

/-! ## 9. Joint witness.

  The `_zeuge` theorem joins every premise: Tier-3 admission and
  well-formedness at the start machine, the admitted shift on core 0,
  the saturating shift on core 1, the embedded store issue, admitted
  and saturated lane values, and owner-only forwarding with unchanged
  canonical memory. -/

/-- Third witness step: the embedded base-machine store issue. -/
theorem hsraWit_schritt3 :
    ∃ m3, HwSraSchritt hsraWitM2 m3
      (.hwAlt (.schreibAusgabe 0 hsraWitAdr (BitVec.ofNat 8 0xA5))) := by
  have hperm : (tsoAnsicht hsraWitM2).mem.schreibbar hsraWitAdr = true :=
    rfl
  have h : ∃ s', issueByte (tsoAnsicht hsraWitM2) 0 hsraWitAdr
      (BitVec.ofNat 8 0xA5) = some s' := by
    unfold issueByte
    rw [hperm]
    exact ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ := h
  exact ⟨setTso hsraWitM2 s',
    .alt (.gibAus 0 hsraWitAdr (BitVec.ofNat 8 0xA5) s' hs')⟩

/-- JOINT WITNESS: Tier-3 admission, both SRA steps, the embedded
    store issue, admitted and saturated lane values on two cores, and
    owner-only forwarding with unchanged canonical memory. The family
    itself is register-only; the memory-changing step is the embedded
    base-machine issue, attributed via `alt`. -/
theorem hsraWit_zeuge :
    HwWf hsraWitStart ∧
    HwSraSchritt hsraWitStart hsraWitM1
      (.sraReg 0 avx2Cpu avx2Xcr0 basisKontrolle .xmm0 .xmm1 .w16 4) ∧
    HwSraSchritt hsraWitM1 hsraWitM2
      (.sraReg 1 avx2Cpu avx2Xcr0 basisKontrolle .xmm2 .xmm3 .w16 20) ∧
    (∃ m3, HwSraSchritt hsraWitM2 m3
      (.hwAlt (.schreibAusgabe 0 hsraWitAdr
        (BitVec.ofNat 8 0xA5)))) ∧
    hsraLaneOut hsraWitR1 0 .xmm0 0 = some 0xFFF0 ∧
    hsraLaneOut hsraWitR2 1 .xmm2 0 = some 0xFFFF ∧
    hsraBufOut hsraWitM3 0 = some 1 ∧
    hsraLoadOut hsraWitM3 0 = some (BitVec.ofNat 8 0xA5) ∧
    hsraLoadOut hsraWitM3 1 = some (BitVec.ofNat 8 0) ∧
    hsraMemOut hsraWitM3 hsraWitAdr = some (BitVec.ofNat 8 0) := by
  exact ⟨hsraWitStart_wf, hsraWit_schritt1, hsraWit_schritt2,
    hsraWit_schritt3, hsraWit_r1_lo, hsraWit_r2_lo, hsraWit_m3_buf,
    hsraWit_m3_fwd_eigen, hsraWit_m3_fwd_fremd, hsraWit_m3_mem_still⟩

/- CUTS: what is not proved here.

   - Pure shift semantics is lifted from `Avx2Ops.lean` (`vecSraImm`,
     `sraLane`, `ymmSra`, the Tier-3 gate): nothing is redefined. No
     VEX decoder/encoder is constructed, so no byte correspondence and
     no RIP advance is claimed; the plug leaves RIP unchanged by
     construction.
   - No YMM register file exists on `HwMaschine`: the two 128-bit
     halves ride two XMM registers of one core (`dstLo`/`dstHi`). That
     pairing is a modelling choice, not silicon (silicon has one YMM
     file with VEX.128 lane-zeroing rules); no 128-bit zeroing or
     preservation rule is claimed.
   - SSE2 half-agreement, as worded in the task, is VACUOUS: a grep
     over the tree shows `VectorIntegerHardwareForms.lean` holds only
     the LOGICAL quadword shifts (`vecShlQ`/`vecShrQ`) and no packed
     arithmetic shift at any width, so there is no accepted SSE2
     arithmetic evaluator to agree with. The agreement proved here is
     each 256-bit half IS the accepted `vecSraImm` half (`ymmSra_halb`,
     `sraFolge_ymm_lo/hi`, all `rfl`). The task wording exceeds what
     exists; this is reported, not worked around.
   - `.b8` shifts and `.b64` arithmetic have no AVX2 VEX encoding
     (VPSRAQ is EVEX-only; no byte immediate shift exists): refused by
     the `SraBreite` type (`sraBreite_kein_b8/b64`), never given a
     semantics. The refused shapes keep their total math functions in
     `Avx2Ops.lean`, unclaimed as instructions.
   - The witness's memory-changing step is a base-machine byte issue
     through `alt`, not an SRA effect: the family is register-only
     (`sraFolge_speicher`, `hsraWit_r1_mem_still`), so the task's
     "cores where the family touches memory" phrasing has no family
     instance. Forwarding is shown at the machine level beside the
     family steps, each step honestly attributed.
   - No bridge to W/GX, no source correspondence, no budget transfer,
     no timing or fault-class claim beyond the Tier-3 admission gate
     (validator admission, not a hardware fault). Silicon
     correspondence beyond the cited SDM extract lines is OPEN: the
     theorems are self-consistency of the stated functions over the
     coherent machine, not hardware proofs.
-/

#print axioms sraBreite_kein_b8
#print axioms sraBreite_kein_b64
#print axioms ymmSra_halb
#print axioms vecSra_allein
#print axioms ymmSra_allein_lo
#print axioms ymmSra_allein_hi
#print axioms laneNat_sraImm
#print axioms laneNat_sraImm_satt
#print axioms laneNat_sraImm_satt_neg
#print axioms laneNat_sraImm_satt_pos
#print axioms ymmSra_lane_lo
#print axioms ymmSra_lane_hi
#print axioms ymmSra_satt_lo
#print axioms ymmSra_satt_hi
#print axioms vecSra_spur_wort
#print axioms vecSra_spur_dwort
#print axioms vecSra_spur_saettigung_neg
#print axioms vecSra_spur_saettigung_pos
#print axioms vecSra_spur_dwort_saettigung
#print axioms sraFolge_speicher
#print axioms sraRegSchritt_gleich
#print axioms sraRegSchritt_profil_verweigert
#print axioms sraFolge_lo
#print axioms sraFolge_hi
#print axioms sraFolge_ymm_lo
#print axioms sraFolge_ymm_hi
#print axioms hwSraSchritt_wf
#print axioms hwSraSchritt_einbettet
#print axioms hwSraSchritt_projiziert
#print axioms adapterSra_verweigert_alt
#print axioms adapterSra_verweigert_fehler
#print axioms adapterSra_fremder_kern
#print axioms sraReg_ist_schritt
#print axioms hsraWit_gate
#print axioms hsraWitStart_wf
#print axioms hsraWit_schritt1
#print axioms hsraWit_schritt2
#print axioms hsraWit_schritt3
#print axioms hsraWit_r1_lo
#print axioms hsraWit_r1_hi
#print axioms hsraWit_r1_mem_still
#print axioms hsraWit_r2_lo
#print axioms hsraWit_r2_hi
#print axioms hsraWit_m3_buf
#print axioms hsraWit_m3_fwd_eigen
#print axioms hsraWit_m3_fwd_fremd
#print axioms hsraWit_m3_mem_still
#print axioms hsraWit_zeuge

end Gabbro.Grammatik.X86
