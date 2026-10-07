/-
  File:      Grammatik/Kern/Semantik/SyscallAllg.lean
  Subject:   ONE GENERIC SYSTEM-CALL GATE, a per-architecture ABI record (x86_64 and AArch64).

  Until now `Ax`'s syscall side (`KernelEintrag`, `UserSyscall`, `syscall_paarung`) was bound to
  the x86 `SysAbi`, and `SysAbiArm` (`SyscallArm.lean`) hung beside it. Machine G itself never
  sees the ABI (`Deklaration.Ax` carries parameters, result and writes only; the register map is
  a field of the user and kernel declarations), so the generalisation is exactly this:

  * `SyscallPaarung.lean`: `KernelEintragG A`, `UserSyscallG A`, and `syscall_paarung` /
    `paarung_gibt_gutO` over ANY ABI record type `A` (the pairing only compares the ABI and hands
    it to the implementation). `KernelEintrag`/`UserSyscall` are the `A := SysAbi` abbreviations,
    so every earlier statement and witness is unchanged (checked by the build).
  * THIS file: the class `ArchAbi A` (register type, number, number register, input map, answer
    register, clobbers), its generic well-formedness `ArchAbi.gut`, the instances for `SysAbi`
    and `SysAbiArm`, the generic clone shape `CloneAbiG`, `syscall_paarung_arch` (the pairing plus
    the ABI's well-formedness), and a NON-DEGENERATE AArch64 witness: the toy `write` of
    `SyscallPaarung.lean` paired through `Arm.schreibAbiArm` (number 64), next to the x86 one.

  NOT done here (see the CUTS at the end): the Rust exporter `lean_g.rs` still names x86 registers;
  `CloneHandoff.lean`'s `CloneAbi` is untouched (it imports machine G); `CloneAbiG` restates its
  shape generically (the x86 embedding IS proved, in `CloneHandoff.lean` §3b: `cloneAbi_good_iff`).
-/
import Grammatik.Kern.Semantik.SyscallPaarung
import Grammatik.Kern.Semantik.SyscallArmLinux

namespace Gabbro.Grammatik

/-! ## 1. The per-architecture ABI record -/

/-- What every architecture's gate record provides. `Reg` is the architecture's register type,
    `nummerReg` the register the call number is loaded into (x86_64: `rax`, which is also the
    answer register; AArch64: `x8`). -/
class ArchAbi (A : Type) where
  Reg : Type
  [dec : DecidableEq Reg]
  nummer : A → Nat
  nummerReg : A → Reg
  ein : A → List (Reg × Nat)
  aus : A → Reg
  clobber : A → List Reg

attribute [instance] ArchAbi.dec

/-- Generic well-formedness: input registers pairwise distinct, no parameter bound twice, the
    number register is no input register, the answer register is not clobbered. -/
def ArchAbi.gut {A : Type} [ArchAbi A] (a : A) : Prop :=
  ((ArchAbi.ein a).map Prod.fst).Nodup ∧ ((ArchAbi.ein a).map Prod.snd).Nodup ∧
    ArchAbi.nummerReg a ∉ (ArchAbi.ein a).map Prod.fst ∧ ArchAbi.aus a ∉ ArchAbi.clobber a

instance : ArchAbi SysAbi where
  Reg := SysReg
  nummer a := a.nummer
  nummerReg _ := .rax
  ein a := a.ein
  aus a := a.aus
  clobber a := a.clobber

instance : ArchAbi Arm.SysAbiArm where
  Reg := Arm.ArmReg
  nummer a := a.nummer
  nummerReg a := a.nummerReg
  ein a := a.ein
  aus a := a.aus
  clobber a := a.clobber

/-- AArch64: the generic notion IS `SysAbiArm.gut`. -/
theorem arch_gut_arm (a : Arm.SysAbiArm) : ArchAbi.gut a ↔ a.gut := Iff.rfl

/-- x86_64: the generic notion is `SysAbi.gut` plus "`rax` (the number register) is no input
    register" -- which the x86 record leaves implicit because it fixes the number in `rax`. -/
theorem arch_gut_x86 (a : SysAbi) :
    ArchAbi.gut a ↔ a.gut ∧ SysReg.rax ∉ a.ein.map Prod.fst := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2, h4⟩, h3⟩
    exact ⟨h1, h2, h3, h4⟩

/-- `write` on both architectures is well-formed under the generic notion. -/
theorem schreib_beide_gut :
    ArchAbi.gut schreibAbi ∧ ArchAbi.gut Arm.schreibAbiArm := by
  constructor
  · exact (arch_gut_x86 _).2 ⟨schreibAbi_gut, by decide⟩
  · exact Arm.schreibAbiArm_gut

/-- Every gate of the AArch64 Linux binding is well-formed under the generic notion. -/
theorem arm_tore_arch_gut : ∀ p ∈ Arm.alleTore, ArchAbi.gut p.1 :=
  fun p hp => (Arm.alleTore_gut_und_nummer p hp).1

/-! ## 2. The generic clone shape -/

/-- `CloneAbiG`: an ABI record plus the handed-stack register (`stack` clause). The same four
    demands as `CloneAbi.good` (`N446`), over any architecture. -/
structure CloneAbiG (A : Type) [ArchAbi A] where
  abi : A
  stack : ArchAbi.Reg A

def CloneAbiG.good {A : Type} [ArchAbi A] (c : CloneAbiG A) : Prop :=
  ArchAbi.gut c.abi ∧ c.stack ∈ (ArchAbi.ein c.abi).map Prod.fst ∧
    c.stack ≠ ArchAbi.aus c.abi ∧ c.stack ∉ ArchAbi.clobber c.abi

/-- The AArch64 clone gate of `linux-aarch64.gab` (`stack x1`). -/
def klonTorArm : CloneAbiG Arm.SysAbiArm := ⟨Arm.gateKlon, Arm.klonStapelReg⟩

/-- **Witness (AArch64):** the clone gate's handoff shape is good under the generic notion:
    registers distinct, `x8` no input, `x1` bound and neither answer nor clobbered. -/
theorem klonTorArm_good : klonTorArm.good := by
  have hg : ArchAbi.gut Arm.gateKlon :=
    arm_tore_arch_gut (Arm.gateKlon, 220) (by simp [Arm.alleTore])
  obtain ⟨h1, h2, _, h4⟩ := Arm.klon_stapelreg_gut
  exact ⟨hg, h1, h2, h4⟩

/-- The planted defect, red direction: handing `x0` (the answer register) is no handoff. -/
theorem klonTorArm_schlecht :
    ¬ (CloneAbiG.good (A := Arm.SysAbiArm) ⟨Arm.gateKlon, Arm.ergebnisReg⟩) := by
  intro h
  exact h.2.2.1 rfl

/-! ## 3. The pairing, with the ABI's well-formedness -/

/-- **`syscall_paarung` for any architecture**, with the gate's ABI record well-formed: the
    oracle premise for `a` holds as before, AND the ABI that both sides name is well-formed
    under the generic notion. (The pairing itself is `syscall_paarung`, unchanged; this is the
    packaged statement for a gate that has a per-architecture record.) -/
theorem syscall_paarung_arch (D : Deklaration) (a : D.Ax) (O : Orakel D)
    {A : Type} [ArchAbi A] {Grund : Type} [DecidableEq Grund]
    (k : KernelEintragG A D (D.aparams a)) (u : UserSyscallG A D (D.aparams a) Grund)
    (K : Nat → A → World D → Env D (D.aparams a) → World D → Int → Prop)
    (hgut : ArchAbi.gut u.abi)
    (hnum : k.nummer = u.nummer)
    (habi : k.abi = u.abi)
    (hreq : ∀ σ ρ, u.Pu σ ρ → k.Pk σ ρ)
    (hens : ∀ σ σ' roh ρ, k.Qk σ σ' roh ρ →
      u.Qu σ σ' (antwortInt (dekodiere u.tab u.lo u.hi roh)) ρ)
    (hsub : ∀ t, k.Ek t = true → u.Eu t = true)
    (hsubG : ∀ g, k.EkG g = true → u.EuG g = true)
    (hEu : ∀ t, u.Eu t = D.aschreibt a t)
    (hEuG : ∀ g, u.EuG g = D.agschreibt a g)
    (hKeff : ∀ σ ρ σ' roh, K k.nummer k.abi σ ρ σ' roh →
      Rahmen k.Ek k.EkG σ σ' ∧ σ'.haelt = σ.haelt ∧
      ((∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt) →
       (∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt) →
       ∃ tabs : List D.Tab, ∃ globs : List D.Glob, ∃ Λe : List (Res D),
         (∀ t, D.aschreibt a t = true → t ∈ tabs) ∧
         (∀ g, D.agschreibt a g = true → g ∈ globs) ∧
         (∀ t, D.aschreibt a t = true → darf D t Λe) ∧
         (∀ g, D.agschreibt a g = true → gdarf D g Λe) ∧
         (∀ m st, Res.marke m st ∉ Λe) ∧
         HeldIn Λe σ.haelt ∧
         σ'.spur = axiomSpur tabs globs a Λe σ.haelt ++ σ.spur))
    (hKcon : ∀ σ ρ σ' roh, K k.nummer k.abi σ ρ σ' roh → k.Pk σ ρ →
      k.Qk σ σ' roh ρ)
    (hO : ∀ σ ρ, ∃ σ' roh, K u.nummer u.abi σ ρ σ' roh ∧
      O.wirkt a σ ρ = (σ', roh)) :
    PaarGut D a O u ∧ ArchAbi.gut u.abi :=
  ⟨syscall_paarung D a O k u K hnum habi hreq hens hsub hsubG hEu hEuG hKeff hKcon hO, hgut⟩

/-! ## 4. The AArch64 witness: the toy `write` through `schreibAbiArm`

  The x86 witness (`swK`, `swU`, `swKbeh` of `SyscallPaarung.lean`) with the register record
  replaced: number 64, `x0 x1 x2`, answer `x0`. The ABI is opaque to the pairing, so every proof
  is the x86 one with `schreibAbiArm` in place of `schreibAbi`. -/

/-- Kernel entry, AArch64 record. -/
def swKArm : KernelEintragG Arm.SysAbiArm swD (swD.aparams ()) where
  nummer := Arm.nrWrite
  abi := Arm.schreibAbiArm
  Pk := swK.Pk
  Qk := swK.Qk
  Ek := swK.Ek
  EkG := swK.EkG

/-- User declaration, AArch64 record. -/
def swUArm : UserSyscallG Arm.SysAbiArm swD (swD.aparams ()) IoFehler where
  nummer := Arm.nrWrite
  abi := Arm.schreibAbiArm
  tab := swU.tab
  lo := swU.lo
  hi := swU.hi
  Pu := swU.Pu
  Qu := swU.Qu
  Eu := swU.Eu
  EuG := swU.EuG

/-- Kernel implementation relation, indexed by dispatch identity (number 64, `schreibAbiArm`). -/
def swKbehArm (n : Nat) (ab : Arm.SysAbiArm) (σ : World swD)
    (ρ : Env swD (swD.aparams ())) (σ' : World swD) (roh : Int) : Prop :=
  n = Arm.nrWrite ∧ ab = Arm.schreibAbiArm ∧ swK.Qk σ σ' roh ρ ∧
    Rahmen swK.Ek swK.EkG σ σ' ∧ σ'.haelt = σ.haelt ∧
    σ'.spur = axiomSpur [()] [] () [] σ.haelt ++ σ.spur

theorem swEffArm : ∀ σ ρ σ' roh, swKbehArm swKArm.nummer swKArm.abi σ ρ σ' roh →
    Rahmen swKArm.Ek swKArm.EkG σ σ' ∧ σ'.haelt = σ.haelt ∧
    ((∀ t, swD.aschreibt () t = true → ∀ L, Sum.inl L ∈ swD.braucht t → L ∈ σ.haelt) →
     (∀ g, swD.agschreibt () g = true → ∀ L, Sum.inl L ∈ swD.gbraucht g → L ∈ σ.haelt) →
     ∃ tabs : List swD.Tab, ∃ globs : List swD.Glob, ∃ Λe : List (Res swD),
       (∀ t, swD.aschreibt () t = true → t ∈ tabs) ∧
       (∀ g, swD.agschreibt () g = true → g ∈ globs) ∧
       (∀ t, swD.aschreibt () t = true → darf swD t Λe) ∧
       (∀ g, swD.agschreibt () g = true → gdarf swD g Λe) ∧
       (∀ m st, Res.marke m st ∉ Λe) ∧
       HeldIn Λe σ.haelt ∧
       σ'.spur = axiomSpur tabs globs () Λe σ.haelt ++ σ.spur) := by
  intro σ ρ σ' roh h
  obtain ⟨hn, hab, hQk, hfr, hha, hspur⟩ := h
  refine ⟨hfr, hha, fun hgt hgg => ?_⟩
  refine ⟨[()], [], [], ?_, ?_, ?_, ?_, ?_, ?_, hspur⟩
  · intro t _
    cases t
    exact List.Mem.head _
  · intro g hg
    exact nomatch g
  · intro t _ w hw
    have hnil : swD.braucht t = [] := rfl
    rw [hnil] at hw
    simp at hw
  · intro g hg
    exact nomatch g
  · intro m st hm
    exact nomatch m
  · intro L hL
    exact nomatch L

theorem swO_trifftArm : ∀ σ ρ, ∃ σ' roh,
    swKbehArm swUArm.nummer swUArm.abi σ ρ σ' roh ∧ swO.wirkt () σ ρ = (σ', roh) := by
  intro σ ρ
  refine ⟨(σ.storeSlot () (swFd ρ) () ⟨1, by decide, by decide⟩).merke
      (axiomSpur [()] [] () [] σ.haelt), 0,
    ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, rfl⟩
  · exact .inl ⟨by omega, (swLen_bereich ρ).1, rfl⟩
  · exact (rahmen_storeSlot swK.Ek swK.EkG σ () (swFd ρ) ()
      (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192)) rfl).trans
      (rahmen_gleich rfl rfl)

/-- **ZEUGE (AArch64):** the pairing holds for the toy `write` through the AArch64 record, the
    record is well-formed under the generic notion, and the program is non-degenerate (a
    `storeSlot` step moves memory). Next to `syscall_paarung_zeuge` (x86): ONE theorem
    (`syscall_paarung_arch`), two architectures. -/
theorem syscall_paarung_arch_zeuge :
    (PaarGut swD () swO swUArm ∧ ArchAbi.gut swUArm.abi) ∧ swD.schreibt () () = true ∧
    ∃ (σ σ' : World swD), σ'.slots () 0 () ≠ σ.slots () 0 () := by
  refine ⟨syscall_paarung_arch swD () swO swKArm swUArm swKbehArm
      Arm.schreibAbiArm_gut rfl rfl (fun _ _ h => h) swEns swSub swSubG swEu swEuG
      swEffArm (fun _ _ _ _ h _ => h.2.2.1) swO_trifftArm, rfl, swWelt0,
    swWelt0.storeSlot () 0 () (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192)), ?_⟩
  have hn1 : ((swWelt0.storeSlot () 0 ()
      (⟨1, by decide, by decide⟩ : Wert swD (.int 0 8192))).slots () 0 ()).n = 1 := rfl
  have hn0 : (swWelt0.slots () 0 ()).n = 0 := rfl
  intro hcon
  have hn := congrArg Zahl.n hcon
  rw [hn1, hn0] at hn
  omega

/-- ... and BOTH architectures' toy `write` pairings hold in one statement. -/
theorem syscall_paarung_beide_zeuge :
    PaarGut swD () swO swU ∧ PaarGut swD () swO swUArm :=
  ⟨syscall_paarung_zeuge.1, syscall_paarung_arch_zeuge.1.1⟩

end Gabbro.Grammatik

/- CUTS: what is NOT claimed.
   - Machine G and `gabbro_ziel` are untouched; the ABI is not part of `Deklaration` (it never
     was). What moved is the syscall PAIRING, which is now generic in the record type `A`.
   - The checker's register tables ARE generated from the Lean records now
     (`instrumente/erzeuge-abi-tabelle.py` -> `crates/gabbro-check/src/abi_tabelle.rs`, guardian
     `--pruefe`); `lean_g.rs` names no register (the exporter drops the ABI, header "NO FORM").
   - `swKArm`'s kernel side restates the x86 toy kernel with another record: it proves that the
     generalisation accepts an AArch64 record, not anything about the Linux kernel.
   - `CloneHandoff.lean` §3b embeds `CloneAbi` into `CloneAbiG SysAbi` (exact up to "`rax` is no
     input"); the clone machine and `ChildNoReturn` do not read the record. `CloneAbiG` carries
     the SHAPE (`N446`) only.
-/

#print axioms Gabbro.Grammatik.arch_gut_arm
#print axioms Gabbro.Grammatik.arch_gut_x86
#print axioms Gabbro.Grammatik.schreib_beide_gut
#print axioms Gabbro.Grammatik.arm_tore_arch_gut
#print axioms Gabbro.Grammatik.klonTorArm_good
#print axioms Gabbro.Grammatik.klonTorArm_schlecht
#print axioms Gabbro.Grammatik.syscall_paarung_arch
#print axioms Gabbro.Grammatik.syscall_paarung_arch_zeuge
#print axioms Gabbro.Grammatik.syscall_paarung_beide_zeuge
