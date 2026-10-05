/-
  File:      Grammatik/X86/PipelineEntry.lean
  Subject:   The ENTRY of the end-to-end pipeline. The register
             representation `EnvRepr` of the source environment, a premise
             of `pipeline_correct_loaded`, is no longer assumed of the entry
             registers: it is ESTABLISHED by a checked entry sequence (moves
             from the parameter registers of a stated ABI into the
             pipeline's variable registers), executed from the loaded image
             by the byte machine, and the entry state is the admitted entry
             of `EntryState`/`EntryExecution` (listed executable entry,
             aligned readable/writable stack word, MXCSR and IF discipline,
             guard where promised, admitted gates).

  Reused, not duplicated:
    - pipeline and image: `Pipeline.pipeline_correct`, `pipeline_refuses`,
      `validate_sound`, `lauf_zu_laufBytes`, `laufBytes_add`, `kanon`,
      `encodeAll`, `abbOf`, `varIdx`, `exitAdr`; `PipelineImage.imageOk`
      (`imageOk_teile`, `imageOk_codeAt`, `imageOk_layoutSep`,
      `imageOk_worldRep`), `weltOk`, `startZustand`, `ladung`,
      `laufBytes_rahmen`, `codeAt_lauf`, `byteschritt_stop`, `grund_mem`,
      `stubBefehl`, and the builder `bildFuerP` with its completeness
      (`bildFuerP_ok`, `baueBildP_extent_rw`, `baueBildP_valX86`);
    - entry: `EntryState.eintrittOk`/`EintrittZustand`/`ifErwartet`/
      `guardErforderlich`, `EntryExecution.eintrittZulassung`/
      `zulassung_eintritt`/`zulassung_stapel_rw`;
    - machine: `Ausfuehrung.schritt_movReg64`, `regSet_gleich`/
      `regSet_fremd`, `LoadedExecution.bildZustand`.
  No second machine, no second loader, no per-program rule.

  THE PARAMETER ABI (stated, user logic): the caller passes integer
  parameter `i` as its word in register `abi[i]` (`AbiArgs`). The entry
  sequence copies `abi[i]` to the pipeline register `regs[i]` for every
  parameter; `prologOk` decides that the copies cannot clobber each other
  and never write `rsp`. That the caller honours the ABI is the caller's
  duty (an `AbiArgs` premise), not a hardware assumption.

  The joint witnesses and the poison probes live in
  `Grammatik/X86/PipelineImageWitnesses.lean`.
-/
import Grammatik.X86.PipelineImage
import Grammatik.X86.EntryExecution

namespace Gabbro.Grammatik.X86.PipelineEntry

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineImage

variable {D : Deklaration}

/-! ## 1. The parameter ABI and the entry sequence -/

/-- The integer parameter registers of the System V AMD64 call ABI, in
    order (one stated ABI; any other list is admitted by the same check). -/
def sysvParameter : List Register := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- THE CALLER'S SIDE OF THE ABI: integer parameter `x` arrives as the word
    of its value in register `abi[varIdx x]`. -/
def AbiArgs (abi : List Register) {Γ : Ctx} (ρ : Env D Γ) (reg : Register → Wort) : Prop :=
  ∀ (lo hi : Int) (x : Var Γ (.int lo hi)), reg (abi.getD (varIdx x) .rsp) = intWort (ρ.get x).n

/-- The register copies of the entry sequence: `(regs[i], abi[i])`. -/
def prologPaare (c : PipeCfg) (abi : List Register) (n : Nat) : List (Register × Register) :=
  (List.range n).map fun i => (c.regs.getD i .rsp, abi.getD i .rsp)

/-- The entry sequence for `n` parameters: `mov regs[i], abi[i]`. -/
def prolog (c : PipeCfg) (abi : List Register) (n : Nat) : List Befehl :=
  (prologPaare c abi n).map fun q => .movReg64 q.1 q.2

/-- Two copies in order do not interfere: the earlier destination is
    neither the later source nor the later destination. -/
def ZugOk (q r : Register × Register) : Prop := q.1 ≠ r.2 ∧ q.1 ≠ r.1

instance : DecidableRel ZugOk := fun q r => inferInstanceAs (Decidable (q.1 ≠ r.2 ∧ q.1 ≠ r.1))

/-- THE DECIDED ENTRY-SEQUENCE CHECK: every parameter has a pipeline
    register and an ABI register, no copy clobbers a later one, and `rsp`
    is never written. -/
def prologOk (c : PipeCfg) (abi : List Register) (n : Nat) : Bool :=
  decide (n ≤ c.regs.length) && decide (n ≤ abi.length) &&
  decide ((prologPaare c abi n).Pairwise ZugOk) &&
  (prologPaare c abi n).all (fun q => decide (q.1 ≠ .rsp))

theorem prologOk_teile (c : PipeCfg) (abi : List Register) (n : Nat) (h : prologOk c abi n = true) :
    (prologPaare c abi n).Pairwise ZugOk ∧ ∀ q ∈ prologPaare c abi n, q.1 ≠ .rsp := by
  unfold prologOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.2, h.2⟩

theorem prolog_gerade (c : PipeCfg) (abi : List Register) (n : Nat) :
    (prolog c abi n).all gerade = true := by
  unfold prolog
  simp [gerade]

/-- THE ENTRY SEQUENCE RUNS: the copies execute one after the other, keep
    memory, set every destination to its source's ENTRY value, and keep
    every register that is no destination. -/
theorem zuege_lauf : ∀ (qs : List (Register × Register)) (s : Zustand), qs.Pairwise ZugOk →
    ∃ s', lauf ((qs.map fun q => Befehl.movReg64 q.1 q.2).map kanon) s = some s' ∧
      s'.speicher = s.speicher ∧
      (∀ q ∈ qs, s'.register q.1 = s.register q.2) ∧
      (∀ r, (∀ q ∈ qs, r ≠ q.1) → s'.register r = s.register r)
  | [], s, _ => ⟨s, rfl, rfl, by simp, fun _ _ => rfl⟩
  | q :: qs, s, h => by
    rw [List.pairwise_cons] at h
    have hs1 := schritt_movReg64 (kanon (.movReg64 q.1 q.2)) s q.1 q.2 (laengeOk_encode _) rfl
    obtain ⟨s', hrun, hmem, hset, hrest⟩ := zuege_lauf qs _ h.2
    refine ⟨s', ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, lauf]
      rw [hs1]
      exact hrun
    · rw [hmem]
      rfl
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · rw [hrest r.1 (fun q' hq' => (h.1 q' hq').2)]
        exact regSet_gleich _ _ _
      · rw [hset r hr']
        exact regSet_fremd _ _ _ _ (fun e => (h.1 r hr').1 e.symm)
    · intro r hr
      rw [hrest r (fun q' hq' => hr q' (List.mem_cons_of_mem _ hq'))]
      exact regSet_fremd _ _ _ _ (hr q List.mem_cons_self)

/-- Every variable index is below the context length. -/
theorem varIdx_lt : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), varIdx x < Γ.length
  | _, _, .hier => by simp [varIdx]
  | _, _, .dort x => by
    simp only [varIdx, List.length_cons]
    have := varIdx_lt x
    omega

/-- THE ENTRY SEQUENCE ESTABLISHES `EnvRepr`: after the copies, every
    integer parameter sits in its pipeline register as the word of its
    value -- from the caller's ABI duty, not assumed. -/
theorem prolog_envRepr (c : PipeCfg) (abi : List Register) {Γ : Ctx} (ρ : Env D Γ)
    (reg reg' : Register → Wort) (hargs : AbiArgs abi ρ reg)
    (hset : ∀ q ∈ prologPaare c abi Γ.length, reg' q.1 = reg q.2) :
    EnvRepr ρ reg' (abbOf c) := by
  intro lo hi x
  have hmem : (c.regs.getD (varIdx x) .rsp, abi.getD (varIdx x) .rsp) ∈
      prologPaare c abi Γ.length :=
    List.mem_map.mpr ⟨varIdx x, List.mem_range.mpr (varIdx_lt x), rfl⟩
  have := hset _ hmem
  simp only at this
  show reg' (c.regs.getD (varIdx x) .rsp) = _
  rw [this]
  exact hargs lo hi x

/-! ## 2. The entry state -/

/-- The loaded entry state: the existing loader's state at the entry
    sequence, `codeBase - |pro|`. With no entry sequence it IS the
    pipeline's `startZustand`. -/
def eintrittStart (bild : Bild) (c : PipeCfg) (plen : Nat) (reg : Register → Wort)
    (fl : Flags) : Zustand :=
  bildZustand bild (effBias bild.modus) (natAdresse (c.codeBase - plen)) reg fl

theorem eintrittStart_null (bild : Bild) (c : PipeCfg) (reg : Register → Wort) (fl : Flags) :
    eintrittStart bild c 0 reg fl = startZustand bild c reg fl := rfl

/-- What the entry run needs of an image beyond `imageOk`: the entry
    sequence in front of the code, decided over the loaded memory. -/
def prologImageOk (bild : Bild) (c : PipeCfg) (abi : List Register) (n : Nat) : Bool :=
  prologOk c abi n &&
  decide ((encodeAll (prolog c abi n)).length ≤ c.codeBase) &&
  codeAtB (ladung bild) (natAdresse (c.codeBase - (encodeAll (prolog c abi n)).length))
    (encodeAll (prolog c abi n))

/-- THE ENTRY RUN: from the entry state the fetched entry sequence reaches
    `codeBase` with memory unchanged, `rsp` unchanged and `EnvRepr`
    established. -/
theorem prolog_lauf (bild : Bild) (c : PipeCfg) (abi : List Register) {Γ : Ctx} (ρ : Env D Γ)
    (hpro : prologImageOk bild c abi Γ.length = true) (s : Zustand)
    (hs : s.speicher = ladung bild)
    (hrip : s.rip = natAdresse (c.codeBase - (encodeAll (prolog c abi Γ.length)).length))
    (hargs : AbiArgs abi ρ s.register) :
    ∃ s1, laufBytes (prolog c abi Γ.length).length s = .weiter s1 ∧
      s1.rip = natAdresse c.codeBase ∧ s1.speicher = ladung bild ∧
      s1.register .rsp = s.register .rsp ∧ EnvRepr ρ s1.register (abbOf c) := by
  unfold prologImageOk at hpro
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpro
  obtain ⟨⟨hok, hle⟩, hcode⟩ := hpro
  obtain ⟨hpw, hrsp⟩ := prologOk_teile c abi _ hok
  obtain ⟨s1, hrun, hmem, hset, hrest⟩ := zuege_lauf (prologPaare c abi Γ.length) s hpw
  have hc : CodeAt s.speicher (natAdresse (c.codeBase - (encodeAll (prolog c abi Γ.length)).length))
      (encodeAll (prolog c abi Γ.length)) := by
    rw [hs]
    exact codeAtB_sound _ _ _ hcode
  obtain ⟨hb, hr, -, -, -⟩ := lauf_zu_laufBytes _ (encodeAll (prolog c abi Γ.length))
    (prolog c abi Γ.length) [] [] s s1 (prolog_gerade c abi _)
    (by unfold prolog; simpa using hrun) hc (by simp) (by rw [hrip]; exact (addrOff_null _).symm)
  refine ⟨s1, hb, ?_, by rw [hmem, hs], ?_, prolog_envRepr c abi ρ s.register s1.register hargs hset⟩
  · rw [hr, List.length_nil, Nat.zero_add, addrOff_natAdresse, Nat.sub_add_cancel hle]
  · exact hrest .rsp (fun q hq e => hrsp q hq e.symm)

/-! ## 3. The closing theorems from an admitted entry -/

section Schluss
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- **PIPELINE CORRECTNESS FROM AN ADMITTED ENTRY.** Premises: the code
    validator, the image check, the initial-world check, the entry-sequence
    check, an ADMITTED entry (`eintrittZulassung`: checked mapping, listed
    executable entry, aligned readable/writable stack word, guard, MXCSR,
    IF, admitted gates) whose machine state is the loaded entry state, the
    caller's parameter ABI (`AbiArgs`) -- and the source run of the
    ORIGINAL block. `EnvRepr` is NOT a premise: the fetched entry sequence
    establishes it. Conclusion: the fetched run from the entry reaches the
    code end with world and environment represented and stops there, and
    the entry stack word is still readable and writable. -/
theorem pipeline_correct_entry (p : Profil) (bild : Bild) (c : PipeCfg) (abi : List Register)
    (ps : List (Platz D)) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c (layoutVon ps) certs src bytes = true)
    (himg : imageOk p bild c ps es certs src bytes = true)
    (hpro : prologImageOk bild c abi Γ.length = true)
    (σ : World D) (hwelt : weltOk bild ps σ = true)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (hzul : eintrittZulassung p bild (effBias bild.modus) art z tore = true)
    (reg : Register → Wort) (fl : Flags)
    (hz : z.zustand = eintrittStart bild c (encodeAll (prolog c abi Γ.length)).length reg fl)
    (ρ : Env D Γ) (hargs : AbiArgs abi ρ reg)
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ' : World D) (ρ' : Env D Γ) (hsrc : execBlock O passes R src σ ρ = .ok σ' ρ') :
    ∃ n s', laufBytes n z.zustand = .weiter s' ∧
      s'.rip = natAdresse (c.codeBase + bytes.length) ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧ EnvRepr ρ' s'.register (abbOf c) ∧
      byteschritt s' = .verweigert ∧
      lesbar8 s'.speicher (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 s'.speicher (eintrittRsp z - BitVec.ofNat 64 8) = true := by
  have ht := imageOk_teile p bild c ps es certs src bytes himg
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = (prolog c abi Γ.length).length := ⟨_, rfl⟩
  obtain ⟨s1, hrun1, hrip1, hmem1, -, hE1⟩ := prolog_lauf bild c abi ρ hpro z.zustand
    (by rw [hz]; rfl) (by rw [hz]; rfl) (by rw [hz]; exact hargs)
  obtain ⟨n2, s', hrun2, hrip, hW, hE'⟩ := pipeline_correct c (layoutVon ps) certs src bytes hval
    (imageOk_layoutSep p bild c ps es certs src bytes himg) O passes R σ ρ s1
    (by rw [hmem1]; exact imageOk_codeAt p bild c ps es certs src bytes himg) hrip1
    (by rw [hmem1]; exact imageOk_worldRep p bild c ps es certs src bytes himg σ hwelt) hE1
    σ' ρ' hsrc
  have hrun : laufBytes ((prolog c abi Γ.length).length + n2) z.zustand = .weiter s' := by
    rw [laufBytes_add _ _ _ _ hrun1]
    exact hrun2
  obtain ⟨hx, hsw, hl, -⟩ := laufBytes_rahmen _ _ _ hrun
  have hstop : byteschritt s' = .verweigert := by
    apply byteschritt_stop
    rw [hx, hrip, hz]
    exact ht.2.2.2.2.2.1
  obtain ⟨hstl, hsts⟩ := zulassung_stapel_rw p bild _ art z tore hzul
  refine ⟨_, s', hrun, hrip, hW, hE', hstop, ?_, ?_⟩
  · unfold lesbar8 at hstl ⊢
    rw [hl]
    exact hstl
  · unfold schreibbar8 at hsts ⊢
    rw [hsw]
    exact hsts

/-- **PIPELINE REFUSAL FROM AN ADMITTED ENTRY**: the same entry for a
    source run that stops at a failed check with reason `r` ends after the
    checked stub at `exitAdr c r + 10` with `rax = r`, the world
    represented, and stops there. -/
theorem pipeline_refuses_entry (p : Profil) (bild : Bild) (c : PipeCfg) (abi : List Register)
    (ps : List (Platz D)) (es : List TabLayout) (certs : List (PassKind × BlockCert))
    (src : Block D V l Γ Λ Λ') (bytes : List Byte)
    (hval : validate c (layoutVon ps) certs src bytes = true)
    (himg : imageOk p bild c ps es certs src bytes = true)
    (hpro : prologImageOk bild c abi Γ.length = true)
    (σ : World D) (hwelt : weltOk bild ps σ = true)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (hzul : eintrittZulassung p bild (effBias bild.modus) art z tore = true)
    (reg : Register → Wort) (fl : Flags)
    (hz : z.zustand = eintrittStart bild c (encodeAll (prolog c abi Γ.length)).length reg fl)
    (ρ : Env D Γ) (hargs : AbiArgs abi ρ reg)
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ' : World D) (r : Fin V.gruende) (hsrc : execBlock O passes R src σ ρ = .grund σ' r) :
    ∃ n s', laufBytes n z.zustand = .weiter s' ∧
      s'.rip = natAdresse (exitAdr c r.val + 10) ∧ s'.register exitReg = intWort r.val ∧
      WorldRep (layoutVon ps) s'.speicher σ' ∧ byteschritt s' = .verweigert ∧
      lesbar8 s'.speicher (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 s'.speicher (eintrittRsp z - BitVec.ofNat 64 8) = true := by
  have ht := imageOk_teile p bild c ps es certs src bytes himg
  obtain ⟨prog, -, hlow, -, -, -⟩ := validate_sound c (layoutVon ps) certs src bytes hval
  have hmemg : r.val ∈ grundListe (optimise certs src) := by
    apply grund_mem c (layoutVon ps) O passes R (optimise certs src) 0 prog hlow σ ρ σ' r
    rw [optimise_sound certs src O passes R σ ρ]
    exact hsrc
  obtain ⟨hstubB, hstopB⟩ := ht.2.2.2.2.2.2.1 r.val hmemg
  obtain ⟨s1, hrun1, hrip1, hmem1, -, hE1⟩ := prolog_lauf bild c abi ρ hpro z.zustand
    (by rw [hz]; rfl) (by rw [hz]; rfl) (by rw [hz]; exact hargs)
  obtain ⟨n2, s2, hrun2, hrip2, hW⟩ := pipeline_refuses c (layoutVon ps) certs src bytes hval
    (imageOk_layoutSep p bild c ps es certs src bytes himg) O passes R σ ρ s1
    (by rw [hmem1]; exact imageOk_codeAt p bild c ps es certs src bytes himg) hrip1
    (by rw [hmem1]; exact imageOk_worldRep p bild c ps es certs src bytes himg σ hwelt) hE1
    σ' r hsrc
  have hrun : laufBytes ((prolog c abi Γ.length).length + n2) z.zustand = .weiter s2 := by
    rw [laufBytes_add _ _ _ _ hrun1]
    exact hrun2
  have hstub : CodeAt s2.speicher (natAdresse (exitAdr c r.val)) (stubBytes r.val) := by
    apply codeAt_lauf _ _ s2 hrun
    rw [hz]
    exact codeAtB_sound _ _ _ hstubB
  have hbs := byteschritt_im_code s2 (natAdresse (exitAdr c r.val)) (stubBytes r.val) [] []
    (stubBefehl r.val) hstub (by simp [stubBytes]) (by rw [hrip2]; exact (addrOff_null _).symm)
  rw [schritt_movImm64 (kanon (stubBefehl r.val)) s2 exitReg (intWort r.val)
    (laengeOk_encode _) rfl] at hbs
  let s' := schrittRegister s2 (ripNach s2.rip (kanon (stubBefehl r.val)).laenge) s2.flags
    exitReg (intWort r.val)
  have hrip' : s'.rip = natAdresse (exitAdr c r.val + 10) := by
    show ripNach s2.rip 10 = _
    rw [hrip2, ripNach_addrOff, addrOff_natAdresse]
  have hstop : byteschritt s' = .verweigert := by
    apply byteschritt_stop
    obtain ⟨hx, -⟩ := laufBytes_rahmen _ _ s2 hrun
    show s2.speicher.ausfuehrbar s'.rip = false
    rw [hx, hrip', hz]
    exact hstopB
  have hfin : laufBytes ((prolog c abi Γ.length).length + n2 + 1) z.zustand = .weiter s' := by
    rw [laufBytes_add _ 1 _ s2 hrun]
    simp only [laufBytes, hbs]
    rfl
  obtain ⟨-, hsw, hl, -⟩ := laufBytes_rahmen _ _ _ hfin
  obtain ⟨hstl, hsts⟩ := zulassung_stapel_rw p bild _ art z tore hzul
  refine ⟨_, s', hfin, hrip', regSet_gleich s2.register exitReg (intWort r.val), hW, hstop, ?_, ?_⟩
  · unfold lesbar8 at hstl ⊢
    rw [hl]
    exact hstl
  · unfold schreibbar8 at hsts ⊢
    rw [hsw]
    exact hsts

end Schluss

/-! ## 4. Completeness of the entry for the built image

    The image `bildFuerP` built with the entry sequence passes the
    entry-sequence check, and an entry state on a stack word inside one of
    its table extents is ADMITTED -- so the whole chain from compile to an
    admitted entry is a total, checked path under decided conditions. -/

theorem natAdresse_sub8 (n : Nat) (h1 : 8 ≤ n) (h2 : n < 2 ^ 64) :
    natAdresse n - BitVec.ofNat 64 8 = natAdresse (n - 8) := by
  apply BitVec.eq_of_toNat_eq
  unfold natAdresse
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega : n - 8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 8 < 2 ^ 64)]
  omega

theorem halbe_lt (p : Profil) : halbe p < 2 ^ 64 := by cases p <;> decide

section Bau
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- The decided entry conditions on the stack word and the entry state
    fields (kind, IF bit, no XMM use, guard where the kind promises one). -/
def eintrittBedingung (art : EintrittArt) (es : List TabLayout) (top : Nat)
    (z : EintrittZustand) : Bool :=
  decide (z.zustand.register .rsp = natAdresse top) && decide (top % 16 = 0) &&
  es.any (fun e => decide (e.basis + 8 ≤ top ∧ top ≤ e.basis + e.len)) &&
  !z.xmmBeruehrt && decide (z.ifBit = ifErwartet art) &&
  (!guardErforderlich art || z.guardOk)

/-- **ENTRY COMPLETENESS.** For the image `bildFuerP` built with the entry
    sequence of a checked ABI, under `bauOk` (with the entry sequence) and
    the decided stack/state conditions, the entry-sequence check holds and
    the loaded entry state is ADMITTED by `eintrittOk`. -/
theorem bildFuerP_eintritt (p : Profil) (c : PipeCfg) (abi : List Register) (prog : List Befehl)
    (ps : List (Platz D)) (σ : World D) (es : List TabLayout)
    (certs : List (PassKind × BlockCert)) (src : Block D V l Γ Λ Λ')
    (hok : prologOk c abi Γ.length = true)
    (hb : bauOk p c (encodeAll (prolog c abi Γ.length)) (encodeAll prog)
      (ohneDoppel (grundListe (optimise certs src))) ps es = true)
    (art : EintrittArt) (top : Nat) (reg : Register → Wort) (fl : Flags) (z : EintrittZustand)
    (hz : z.zustand = eintrittStart
      (bildFuerP c (encodeAll (prolog c abi Γ.length)) certs src (encodeAll prog) ps σ es) c
      (encodeAll (prolog c abi Γ.length)).length reg fl)
    (hbed : eintrittBedingung art es top z = true) :
    prologImageOk (bildFuerP c (encodeAll (prolog c abi Γ.length)) certs src (encodeAll prog)
        ps σ es) c abi Γ.length = true ∧
      eintrittOk p (bildFuerP c (encodeAll (prolog c abi Γ.length)) certs src (encodeAll prog)
        ps σ es) 0 art z = true := by
  have F := bauOk_fakten p c _ _ _ ps es hb
  have hnd := ohneDoppel_nodup (grundListe (optimise certs src))
  have hall := bildFuerP_ok p c (prolog c abi Γ.length) prog ps σ es certs src hb
  have hpro := F.pro_le
  have hlen := F.lang
  have hh := F.code_halb
  have hhl := halbe_lt p
  unfold eintrittBedingung at hbed
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.any_eq_true,
    Bool.or_eq_true] at hbed
  obtain ⟨⟨⟨⟨⟨hrsp, h16⟩, ⟨e, he, hlo, hhi⟩⟩, hxmm⟩, hif⟩, hguard⟩ := hbed
  have heh := F.daten_halb e he
  refine ⟨?_, ?_⟩
  · unfold prologImageOk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hok, hpro⟩, hall.2.2⟩
  · have hval := baueBildP_valX86 p c (prolog c abi Γ.length) prog _ ps σ es F hnd
    have hrip : z.zustand.rip = natAdresse (c.codeBase - (encodeAll (prolog c abi Γ.length)).length) := by
      rw [hz]; rfl
    have hripN : z.zustand.rip.toNat = c.codeBase - (encodeAll (prolog c abi Γ.length)).length := by
      rw [hrip]
      exact natAdresse_toNat_lt _ (by omega)
    have hmem : z.zustand.speicher = ladung (bildFuerP c (encodeAll (prolog c abi Γ.length)) certs
        src (encodeAll prog) ps σ es) := by
      rw [hz]; rfl
    obtain ⟨hl8, hs8⟩ := baueBildP_extent_rw p c (prolog c abi Γ.length) prog _ ps σ es F hnd e he
      (top - 8) (by omega) (by omega)
    unfold eintrittOk
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨valX86_wohlgeformt p _ hval, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · unfold eintragGelisted
      rw [hripN]
      simp [bildFuerP, baueBildP]
    · rw [hripN]
      have hpw := baueBildP_pairwise p c (prolog c abi Γ.length) prog _ ps σ es F hnd
      have hf := abteilFinden_eindeutig _ hpw
        (codeAbschnittP c (encodeAll (prolog c abi Γ.length)) (encodeAll prog)) List.mem_cons_self
        (c.codeBase - (encodeAll (prolog c abi Γ.length)).length)
        (by simp [codeAbschnittP]) (by simp only [codeAbschnittP]; omega)
      show ladenAusfuehrbar (baueBildP c (encodeAll (prolog c abi Γ.length)) (encodeAll prog)
        (ohneDoppel (grundListe (optimise certs src))) ps σ es) 0 _ = true
      unfold ladenAusfuehrbar
      rw [hf]
      rfl
    · unfold stapelOk ausgerichtet16 eintrittRsp
      rw [hrsp, natAdresse_toNat_lt _ (by omega)]
      exact decide_eq_true h16
    · unfold stapelRW eintrittRsp
      simp only
      rw [hrsp, natAdresse_sub8 top (by omega) (by omega), hmem]
      simp only [Bool.and_eq_true]
      exact ⟨hl8, hs8⟩
    · unfold guardOk
      simpa using hguard
    · unfold mxcsrOk
      simp [hxmm]
    · unfold ifOk
      exact decide_eq_true hif

end Bau

/- CUTS (exactly what is NOT proved here):

   ABI. `AbiArgs` is the caller's side of a STATED parameter ABI (integer
   parameters in registers, in order): a premise on the entry registers,
   the caller's duty. What a caller, a loader or an operating system
   actually puts there is not modelled; no stack-passed, float, pointer or
   aggregate parameter is covered, and at most `abi.length` parameters.
   `sysvParameter` names the System V order but no other part of that ABI
   (callee-saved registers, red zone, return value) is claimed.

   Entry sequence. Register-to-register copies only (`movReg64`), checked
   non-interfering by `prologOk`; parallel-move resolution (a cycle of
   copies) is refused, not solved. With `abi = regs` the copies are the
   identity moves and still run.

   Admission. `eintrittZulassung` is a PREMISE of the closing theorems;
   what it contributes there is the stack word below the entry `rsp`,
   which stays readable and writable through the whole run (the frame of
   every byte step). The entry `rsp` itself is preserved through the
   entry sequence (`prolog_lauf`), NOT claimed after the block body (the
   pipeline claims no register beyond the variables). MXCSR, IF and guard
   are admission facts of the entry; this fragment uses no XMM, no
   interrupt and no stack, so nothing in the run depends on them, and no
   interrupt or guard-page behaviour is modelled.

   Completeness. `bildFuerP_eintritt` shows the built image passes
   `prologImageOk` and that an entry state on a stack word inside a table
   extent is admitted by `eintrittOk` (with bias 0, the image's own); the
   gate half of `eintrittZulassung` (`valTore`) depends on the caller's
   gate list and is not decided here. A stack extent is an ordinary
   `TabLayout` extent with no placement; nothing reserves it against a
   placement in the same extent beyond the stated conditions.

   Everything of the CUTS of `Pipeline.lean` and `PipelineImage.lean`
   still applies (pilot ISA, one core, model memory, no time, no TSO). -/

#print axioms prologOk_teile
#print axioms prolog_gerade
#print axioms zuege_lauf
#print axioms varIdx_lt
#print axioms prolog_envRepr
#print axioms eintrittStart_null
#print axioms prolog_lauf
#print axioms pipeline_correct_entry
#print axioms pipeline_refuses_entry
#print axioms natAdresse_sub8
#print axioms halbe_lt
#print axioms bildFuerP_eintritt

end Gabbro.Grammatik.X86.PipelineEntry
