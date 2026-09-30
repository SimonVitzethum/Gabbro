/-
  File:      Grammatik/SchablonenOhneLibc.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md), the two templates
             of a program without a C library (C-free lane, 2026-09-30).

  Rows of `crates/gabbro-check/src/schablonen.rs`:

  * `tor.nie` -- the `_Noreturn` stub of a `-> never` gate
    (`emit.rs::syscall_stumpf`, `Antwort::Nie`): `static _Noreturn void g(…)`,
    the `syscall` instruction, then `__builtin_unreachable()`. SEMANTICS-TIED:
    over the real block semantics (`execBlock`, Semantik.lean), a call of an
    axiom whose declared answer is `never` never runs what stands behind it --
    under EVERY oracle, so no assumption about the machine is spent on it --
    and the head it stops at is the goal theorem's named stop `nieZurueck`
    (`KopfHalt`, Zielsatz/Spec.lean). That is exactly what the C promises
    with `_Noreturn` and `__builtin_unreachable()`: the code behind the call
    is dead in G as in the C.
    **Witness:** the real certified program `beispiele/174` (its gate
    `exit_group`, `Zertifikat/G174_tor_im_modell.lean`).

  * `start.nolibc` -- the generated process entry of a `nolibc` program
    (`bau.rs::prozess_start`): `xor %ebp,%ebp; and $-16,%rsp; call main; ud2`.
    An ABSTRACT CORE like the rows of SchablonenT5.lean: machine G has no
    process entry (the loader and the thread start are the runtime premise
    (d), `Laufzeit`), so the core is stated over a small model of the three
    instructions -- NOT tied to `execBlock`. It proves the two things the
    stub is for: the stack pointer `main` sees meets the x86_64 SysV entry
    alignment and the return address lands BELOW the kernel's stack pointer
    (argc stays intact), and the trailing `ud2` is reached only if `main`
    returns -- which the entry rule and `S009` exclude.

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness
  instantiating ALL its premises jointly.
-/

import Grammatik.Zertifikat.G174_tor_im_modell

namespace Gabbro.Grammatik

namespace OhneLibc

/-! ## 1. `tor.nie` -- the `_Noreturn` stub of a `-> never` gate -/

section Nie

variable {D : Deklaration}

/-- No raw word answers `never`, under any image: the empty answer class
    (`AntwortLeer`), stated for the one type the checker admits it at. -/
theorem einpassenErg_nie (z : Int → Option D.Fn) (n : Int) :
    einpassenErg z (some Ty.never) n = none := rfl

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}

/-- **Soundness of `tor.nie`, over the real block semantics.** A call of an
    axiom whose declared answer is `never` (`h`, from the gate's `-> never`,
    `lean_g.rs::read_gate`) ends the block in the hardware outcome of that
    axiom, under EVERY oracle: the rest -- whatever the program wrote behind
    the call -- is never run. The emitted `__builtin_unreachable()` after the
    `syscall` instruction states the same thing to the C compiler. -/
theorem nie_tor_kehrt_nicht_zurueck (a : D.Ax) (h : D.aerg a = some Ty.never)
    (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ = .hardware (.annahme a) := by
  simp only [execBlock, axiomAntwort]
  have hleer : ∀ n, einpassenErg O.zeiger (D.aerg a) n = none := by
    intro n; rw [h]; rfl
  rw [hleer]

/-- **The stop is NAMED.** The head of such a call is the goal theorem's stop
    `nieZurueck` (`KopfHalt`, Zielsatz/Spec.lean) -- the kind `FortschrittG`
    lists, and the only empty answer the checker admits (`antwortenB`). -/
theorem nie_tor_halt_benannt (a : D.Ax) (h : D.aerg a = some Ty.never)
    (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) :
    Zielsatz.KopfHalt O passes σ ρ .nieZurueck (.bindAxiom a args he hw hg hd hgd rest) := h

end Nie

/-! ### The witness: the real gate of `beispiele/174` -/

section Zeuge174

open G174_tor_im_modell_oblig in
abbrev D174 : Deklaration := G174_tor_im_modell_oblig.gD

/-- An oracle for the certified program 174: every gate call leaves the world
    and answers `1` (a valid `getpid` answer; `exit_group` has no answer to
    give). -/
def o174 : Orakel D174 where
  wirkt := fun _ σ _ => (σ, 1)
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => true

/-- The then-block of `ende_wenn` in the certified export, verbatim: the
    call `exit_group(1)` as `Block.bindAxiom` with the empty rest. -/
def endeBlock : Block D174 (vertragVon D174 G174_tor_im_modell_oblig.g_ende_wenn) false G174_tor_im_modell_oblig.gCtx_ende_wenn G174_tor_im_modell_oblig.gL_ende_wenn G174_tor_im_modell_oblig.gL_ende_wenn :=
  .bindAxiom G174_tor_im_modell_oblig.GAx.exit_group
    (.cons ((.weiter (by decide) (by decide)
      (((.lit 1)) : Expr D174 G174_tor_im_modell_oblig.gCtx_ende_wenn G174_tor_im_modell_oblig.gL_ende_wenn (.int 1 1))) :
        Expr D174 G174_tor_im_modell_oblig.gCtx_ende_wenn G174_tor_im_modell_oblig.gL_ende_wenn (.int 0 18446744073709551615)) .nil)
    rfl (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) .nil

/-- **Witness for `nie_tor_kehrt_nicht_zurueck` and `nie_tor_halt_benannt`**,
    on the real program: the gate `exit_group` of `beispiele/174` is declared
    `never` in the certified declaration (`rfl`), the run of its block under a
    concrete oracle ends at the gate, and its head is the named stop. -/
theorem nie_tor_zeuge (σ : World D174) (ρ : Env D174 G174_tor_im_modell_oblig.gCtx_ende_wenn) :
    D174.aerg G174_tor_im_modell_oblig.GAx.exit_group = some Ty.never ∧
    execBlock o174 0 (rufAt G174_tor_im_modell_oblig.gP o174 0 0) endeBlock σ ρ = .hardware (.annahme G174_tor_im_modell_oblig.GAx.exit_group) ∧
    Zielsatz.KopfHalt o174 0 σ ρ .nieZurueck endeBlock :=
  ⟨rfl, nie_tor_kehrt_nicht_zurueck _ _ _ _ rfl _ _ _ _ _ _ _ _ _,
    nie_tor_halt_benannt _ _ _ rfl _ _ _ _ _ _ _ _ _⟩

end Zeuge174

/-! ## 2. `start.nolibc` -- the generated process entry (abstract core) -/

/-- `and $-16, %rsp`: the stack pointer rounded down to 16. -/
def ausrichten (rsp : Nat) : Nat := rsp - rsp % 16

/-- The three instructions of the stub after `xor %ebp, %ebp`, and what they
    leave: the stack pointer `main` is entered with (after `call` pushed the
    return address) and whether the trailing `ud2` executes -- which happens
    exactly when `main` returns. -/
structure StartLauf where
  rspEintritt : Nat
  rueckAdresse : Nat
  ud2 : Bool

def startLauf (rsp : Nat) (mainKehrtZurueck : Bool) : StartLauf where
  rspEintritt := ausrichten rsp - 8
  rueckAdresse := ausrichten rsp - 8
  ud2 := mainKehrtZurueck

/-- **Soundness of `start.nolibc`.** Premises: the kernel hands a stack of at
    least 16 bytes (`hrsp`, the loader -- runtime premise (d)) and `main` does
    not return (`hnie`, the entry rule `bau.rs::eintrittsregel` under `nolibc`
    plus `S009`). Conclusions: at `main`'s first instruction `rsp + 8` is
    16-aligned (the SysV x86_64 entry condition every C function assumes);
    the return address is written strictly BELOW the kernel's stack pointer,
    so `argc`/`argv`/`envp` above it stay intact; and `ud2` never executes. -/
theorem start_nolibc (rsp : Nat) (hrsp : 16 ≤ rsp) (mainKehrtZurueck : Bool)
    (hnie : mainKehrtZurueck = false) :
    ((startLauf rsp mainKehrtZurueck).rspEintritt + 8) % 16 = 0 ∧
    (startLauf rsp mainKehrtZurueck).rueckAdresse < rsp ∧
    (startLauf rsp mainKehrtZurueck).ud2 = false := by
  simp only [startLauf, ausrichten]
  refine ⟨?_, ?_, hnie⟩ <;> omega

/-- The premise `hnie` is not decoration: were `main` to return, the stub
    would run into `ud2` (the build's own trap, never a fall-through into
    whatever bytes follow). -/
theorem start_nolibc_ud2_wenn_main_zurueckkehrt (rsp : Nat) :
    (startLauf rsp true).ud2 = true := rfl

/-- **Witness for `start_nolibc`**: ALL premises jointly on a concrete stack
    pointer the kernel may hand (`0x7ffc_1234_5678`, 8-aligned only). -/
theorem start_nolibc_zeuge :
    ((startLauf 0x7ffc12345678 false).rspEintritt + 8) % 16 = 0 ∧
    (startLauf 0x7ffc12345678 false).rueckAdresse < 0x7ffc12345678 ∧
    (startLauf 0x7ffc12345678 false).ud2 = false :=
  start_nolibc 0x7ffc12345678 (by decide) false rfl

end OhneLibc

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_kehrt_nicht_zurueck
#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_halt_benannt
#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_zeuge
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc_zeuge
