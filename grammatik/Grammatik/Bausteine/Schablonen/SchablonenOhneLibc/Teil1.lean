module

public import Grammatik.Bausteine.Schablonen.ZeugeTorModell
public import Grammatik.Kern.Semantik.Syscall.Syscall
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik

namespace OhneLibc

/-! ## 1. `tor.nie` -- the `_Noreturn` stub of a `-> never` gate -/

section Nie

variable {D : Deklaration}

/-- No raw word answers `never`, under any image: the empty answer class
    (`AntwortLeer`), stated for the one type the checker admits it at. -/
theorem einpassenErg_nie (z : Int → Option D.Fn) (n : Int) :
    einpassenErg z (some Ty.never) n = none := by rfl

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
    (.cons ((.widen (by decide) (by decide)
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
    (startLauf rsp true).ud2 = true := by rfl

/-- **Witness for `start_nolibc`**: ALL premises jointly on a concrete stack
    pointer the kernel may hand (`0x7ffc_1234_5678`, 8-aligned only). -/
theorem start_nolibc_zeuge :
    ((startLauf 0x7ffc12345678 false).rspEintritt + 8) % 16 = 0 ∧
    (startLauf 0x7ffc12345678 false).rueckAdresse < 0x7ffc12345678 ∧
    (startLauf 0x7ffc12345678 false).ud2 = false :=
  start_nolibc 0x7ffc12345678 (by decide) false rfl

/-! ### The two hooks (C-free lane, 2026-09-30)

  Without a C library no constructor runs and nobody ends the process after `main` returns. The
  entry therefore calls the program's `gabbro_os_anfang()` first when the unit defines it, and --
  when `main` RETURNS its status -- hands that status (`eax` -> `edi`) to the program's
  `gabbro_os_ende(code)`, a `-> never` function of its binding. Both are names of the program; the
  entry knows no system call. `start_nolibc_haken` is the widened soundness statement; the
  hook-less entry of before is its case `anfang = ende = false` (`start_nolibc`). -/

/-- The calls the widened stub makes, as `rsp` at each callee's first instruction in call order,
    the status the end receives, and whether `ud2` runs. -/
structure StartLaufH where
  rufe : List Nat
  status : Option Nat
  ud2 : Bool

def startLaufH (rsp : Nat) (anfang ende : Bool) (mainErgebnis : Option Nat)
    (endeKehrtZurueck : Bool) : StartLaufH :=
  let a := ausrichten rsp - 8
  match mainErgebnis with
  | none => { rufe := (if anfang then [a] else []) ++ [a], status := none, ud2 := false }
  | some v =>
    if ende then
      { rufe := (if anfang then [a] else []) ++ [a, a], status := some (v % 4294967296),
        ud2 := endeKehrtZurueck }
    else
      { rufe := (if anfang then [a] else []) ++ [a], status := none, ud2 := true }

/-- **Soundness of the widened `start.nolibc`.** Premises: a kernel stack of at least 16 bytes
    (runtime premise (d)); `main` either does not return (`none`) or the unit binds the end
    (`hende`, the entry rule `bau.rs::eintrittsregel` with `nolibc_haken`), and the end does not
    return (`hnie`, its `-> never` declaration and `S009`). Then every call -- the start hook,
    `main`, the end -- is entered with `rsp + 8` 16-aligned and below the kernel's `rsp`; the end
    receives exactly the low 32 bits of `main`'s answer; and `ud2` never runs. -/
theorem start_nolibc_haken (rsp : Nat) (hrsp : 16 ≤ rsp) (anfang ende : Bool)
    (mainErgebnis : Option Nat) (endeKehrtZurueck : Bool)
    (hende : mainErgebnis.isSome = true → ende = true) (hnie : endeKehrtZurueck = false) :
    (∀ r ∈ (startLaufH rsp anfang ende mainErgebnis endeKehrtZurueck).rufe,
      (r + 8) % 16 = 0 ∧ r < rsp) ∧
    (∀ v, mainErgebnis = some v →
      (startLaufH rsp anfang ende mainErgebnis endeKehrtZurueck).status = some (v % 4294967296)) ∧
    (startLaufH rsp anfang ende mainErgebnis endeKehrtZurueck).ud2 = false := by
  have ha : ((ausrichten rsp - 8) + 8) % 16 = 0 ∧ ausrichten rsp - 8 < rsp := by
    simp only [ausrichten]; omega
  cases mainErgebnis with
  | none =>
    refine ⟨?_, ?_, rfl⟩
    · intro r hr
      cases anfang <;> simp only [startLaufH, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, List.cons_append, or_self] at hr <;> subst_vars <;> exact ha
    · intro v h; exact nomatch h
  | some v =>
    have he : ende = true := hende rfl
    subst he
    refine ⟨?_, ?_, hnie⟩
    · intro r hr
      cases anfang <;> simp only [startLaufH, ↓reduceIte, Bool.false_eq_true, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, or_self, List.cons_append] at hr <;> subst_vars <;> exact ha
    · intro w h
      cases h
      rfl

/-- The end premise is not decoration: a `main` that returns with no end bound runs into `ud2`. -/
theorem start_nolibc_ohne_ende (rsp v : Nat) :
    (startLaufH rsp false false (some v) false).ud2 = true := by rfl

/-- **Witness** (all premises jointly): the stack pointer of `start_nolibc_zeuge`, both hooks, a
    `main` answering 42 -- the end receives 42 and `ud2` does not run. -/
theorem start_nolibc_haken_zeuge :
    (∀ r ∈ (startLaufH 0x7ffc12345678 true true (some 42) false).rufe,
      (r + 8) % 16 = 0 ∧ r < 0x7ffc12345678) ∧
    (∀ v, some 42 = some v →
      (startLaufH 0x7ffc12345678 true true (some 42) false).status = some (v % 4294967296)) ∧
    (startLaufH 0x7ffc12345678 true true (some 42) false).ud2 = false :=
  start_nolibc_haken 0x7ffc12345678 (by decide) true true (some 42) false (fun _ => rfl) rfl

/-! ## 3. `tor.fehlbar` -- the stub of a fallible gate -/
end OhneLibc
end Gabbro.Grammatik
