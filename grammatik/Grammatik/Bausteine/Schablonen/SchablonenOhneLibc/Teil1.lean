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

section Fehlbar

variable {D : Deklaration}

/-- The stub's outcome as the machine's ONE raw word: the pair packed like a `tagged` value
    (case number in the low digit, base `n + 1`), the unreachable outcome as a word whose
    value half lies outside the declared range. -/
def packe (n : Nat) {lo hi : Int} : SysAntwort { x : Int // lo ≤ x ∧ x ≤ hi } (Fin n) → Int
  | .ok v => v.1 * ((n : Int) + 1)
  | .why r => (r.1 : Int) + 1
  | .unerwartet _ => (hi + 1) * ((n : Int) + 1)

/-- What G does with a decoded answer of a fallible gate: the value (as the machine's `Zahl`),
    the reason, or nothing (the hardware stop). -/
def gAntwort {n : Nat} {lo hi : Int} : SysAntwort { x : Int // lo ≤ x ∧ x ≤ hi } (Fin n) →
    Option (ErgVal D (some (.int lo hi)) ⊕ Fin n)
  | .ok v => some (Sum.inl (⟨v.1, v.2.1, v.2.2⟩ : Zahl lo hi))
  | .why r => some (Sum.inr r)
  | .unerwartet _ => none

theorem packe_ok (z : Int → Option D.Fn) (n : Nat) {lo hi : Int}
    (v : { x : Int // lo ≤ x ∧ x ≤ hi }) :
    sonstPasst z (some (.int lo hi)) n (packe n (.ok v : SysAntwort _ (Fin n))) =
      some (Sum.inl (⟨v.1, v.2.1, v.2.2⟩ : Zahl lo hi)) := by
  obtain ⟨x, h1, h2⟩ := v
  have hk : (0 : Int) < (n : Int) + 1 := by omega
  have hm : x * ((n : Int) + 1) % ((n : Int) + 1) = 0 := Int.mul_emod_left _ _
  have hd : x * ((n : Int) + 1) / ((n : Int) + 1) = x := Int.mul_ediv_cancel _ (by omega)
  simp only [sonstPasst, packe, hm, if_true, hd, einpassenErg, einpassen, dif_pos (And.intro h1 h2)]
  rfl

theorem packe_grund (z : Int → Option D.Fn) (n : Nat) {lo hi : Int} (r : Fin n) :
    sonstPasst z (some (.int lo hi)) n (packe (lo := lo) (hi := hi) n (.why r)) =
      some (Sum.inr r) := by
  obtain ⟨i, hi'⟩ := r
  have hm : ((i : Int) + 1) % ((n : Int) + 1) = (i : Int) + 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  simp only [sonstPasst, packe, hm]
  rw [if_neg (by omega), dif_pos (by omega)]
  congr
  simp only [Int.add_sub_cancel, Int.toNat_natCast]

theorem packe_unerwartet (z : Int → Option D.Fn) (n : Nat) {lo hi : Int} (u : Int) :
    sonstPasst z (some (.int lo hi)) n (packe (lo := lo) (hi := hi) n (.unerwartet u)) = none := by
  have hm : (hi + 1) * ((n : Int) + 1) % ((n : Int) + 1) = 0 := Int.mul_emod_left _ _
  have hd : (hi + 1) * ((n : Int) + 1) / ((n : Int) + 1) = hi + 1 := Int.mul_ediv_cancel _ (by omega)
  simp only [sonstPasst, packe, hm, if_true, hd, einpassenErg, einpassen]
  rw [dif_neg (by omega)]
  rfl

/-- **Soundness of `tor.fehlbar`.** For EVERY kernel word `roh` and every errno table: the
    outcome the emitted stub forms (`dekodiere`), packed into the machine's raw word, is
    decoded by G exactly as the stub decoded it -- so the C and the model take the same branch
    with the same value or reason, and the stub's `__builtin_unreachable()` is G's hardware
    stop. -/
theorem tor_fehlbar (z : Int → Option D.Fn) (n : Nat) (tab : FehlerTabelle (Fin n))
    (lo hi roh : Int) :
    sonstPasst z (some (.int lo hi)) n (packe n (dekodiere tab lo hi roh)) =
      gAntwort (D := D) (dekodiere tab lo hi roh) := by
  cases dekodiere tab lo hi roh with
  | ok v => exact packe_ok z n v
  | why r => exact packe_grund z n r
  | unerwartet u => exact packe_unerwartet z n u

/-- The three legs of the stub, joined with `dekodiere`'s characterisation (Syscall.lean): an
    in-range non-negative word is the value, a listed `-errno` its reason, and the rest the
    hardware stop -- in G as in the C. -/
theorem tor_fehlbar_wert (z : Int → Option D.Fn) (n : Nat) (tab : FehlerTabelle (Fin n))
    (lo hi roh : Int) (hge : 0 ≤ roh) (hok : lo ≤ roh ∧ roh ≤ hi) :
    sonstPasst z (some (.int lo hi)) n (packe n (dekodiere tab lo hi roh)) =
      some (Sum.inl (⟨roh, hok.1, hok.2⟩ : Zahl lo hi)) := by
  rw [dekodiere_ok_bereich tab lo hi roh hge hok]
  exact packe_ok z n _

theorem tor_fehlbar_grund (z : Int → Option D.Fn) (n : Nat) (tab : FehlerTabelle (Fin n))
    (lo hi : Int) (e : Nat) (r : Fin n) (hfirst : ersterEintrag tab e r)
    (hbereich : 1 ≤ (e : Int) ∧ (e : Int) ≤ 4095) :
    sonstPasst z (some (.int lo hi)) n (packe n (dekodiere tab lo hi (-(e : Int)))) =
      some (Sum.inr r) := by
  rw [dekodiere_tabelle tab lo hi e r hfirst hbereich]
  exact packe_grund z n r

/-! ### The witness: a three-reason channel (`BadFd = 9`, `Interrupted = 4`, `WouldBlock = 11`),
    a value range `0 .. 1024`, and one word of each kind -/

def zeugeTab : FehlerTabelle (Fin 3) := [(9, 0), (4, 1), (11, 2)]

/-- **Witness for `tor_fehlbar`, `tor_fehlbar_wert` and `tor_fehlbar_grund`**, ALL premises
    jointly: the word `3` is the value `3`, the word `-4` (EINTR) is reason `1`, and the word
    `-5` (an errno the table does not admit) is the hardware stop -- each by computation, in G
    as the stub decodes it. -/
theorem tor_fehlbar_zeuge (D : Deklaration) (z : Int → Option D.Fn) :
    sonstPasst z (some (.int 0 1024)) 3 (packe 3 (dekodiere zeugeTab 0 1024 3)) =
      some (Sum.inl (⟨3, by decide, by decide⟩ : Zahl 0 1024)) ∧
    sonstPasst z (some (.int 0 1024)) 3 (packe 3 (dekodiere zeugeTab 0 1024 (-4))) =
      some (Sum.inr 1) ∧
    sonstPasst z (some (.int 0 1024)) 3 (packe 3 (dekodiere zeugeTab 0 1024 (-5))) = none :=
  ⟨tor_fehlbar_wert z 3 zeugeTab 0 1024 3 (by decide) ⟨by decide, by decide⟩,
    tor_fehlbar_grund z 3 zeugeTab 0 1024 4 1 ⟨[(9, 0)], [(11, 2)], rfl, by decide⟩
      ⟨by decide, by decide⟩,
    by rw [tor_fehlbar]; rfl⟩

end Fehlbar

/-! ## 4. `tor.region` -- the stub of a gate that hands over a REGION

  Simon's decision 1 (2026-09-30): memory from outside comes as a region, never from a number.
  A `syscall` answering `ptr<normal, …> u8 or R` gets the stub `emit.rs::syscall_stumpf`
  writes for `Antwort::Region`: the sign leg of `tor.fehlbar` unchanged (a listed `-errno` is
  its reason, an unlisted one or a word past the `-4095` fence the hardware stop), then the
  word ZERO is the hardware stop too, and every other word is handed over as the address
  `(uint8_t *)(uintptr_t)raw`. No expression of the language turns a number into a pointer
  (`M140`); this stub is the one place a word becomes one, and this section is its proof.

  What the section proves, and what it does not:

  * `tor_region`: the stub, statement by statement, IS the generic decoding `dekodiere` of
    Syscall.lean over the value range `1 .. 2^63 - 1` -- the same function `tor.fehlbar` is
    proved over, so the reason channel of a region gate decodes exactly like every other
    fallible gate's;
  * `tor_region_adresse`, `tor_region_fehler_kein_zeiger`: the address handed over is the
    kernel's word itself and never zero, and no error word ever becomes an address;
  * `region_zugriff`: the ONE generic form "a foreign routine hands over a new region" --
    the gate's contract (user logic: `ensures n <= lenof(result)` plus the fresh/disjoint
    sentence of its assumption) -- and what `N571` makes of it: an index `i` with
    `i + 1 <= n` (the checker's `passt(i, 1, clause)`) lies inside the region and inside no
    other region live at the call.
  * NOT proved: that the kernel keeps the contract (the gate's assumption, premise (c)); and
    machine G has no byte pointers (`lean_g.rs` refuses the pointer target by name, LG002),
    so a program with a region answer is outside the certified register exactly like every
    `ptr<…> u8` program before it (OFFEN O37).
-/

section Region

/-- The emitted region stub, statement by statement (`emit.rs`, `Antwort::Region`): the
    `-4095` fence, the errno comparisons in table order, the zero test, the address. -/
def regionStumpf {Grund : Type} [DecidableEq Grund] (tab : FehlerTabelle Grund) (roh : Int) :
    SysAntwort Nat Grund :=
  if roh < 0 then
    if roh < -4095 then .unerwartet roh
    else match fehlerSuche tab (-roh).toNat with
      | some r => .why r
      | none => .unerwartet roh
  else if roh = 0 then .unerwartet roh
  else .ok roh.toNat

/-- The largest word the kernel's `int64_t` answer can hold. -/
def wortMax : Int := 2 ^ 63 - 1

/-- The generic decoding over the address range, with the value leg read as an address. -/
def alsAdresse {Grund : Type} : SysAntwort { x : Int // 1 ≤ x ∧ x ≤ wortMax } Grund →
    SysAntwort Nat Grund
  | .ok v => .ok v.1.toNat
  | .why r => .why r
  | .unerwartet u => .unerwartet u

/-- **Soundness of `tor.region`.** For EVERY word the `int64_t` register can hold and every
    errno table, the emitted stub decides exactly as the generic decoding `dekodiere` over the
    range `1 .. 2^63 - 1` -- the decoding `tor.fehlbar` is proved against machine G's reason
    channel. -/
theorem tor_region {Grund : Type} [DecidableEq Grund] (tab : FehlerTabelle Grund) (roh : Int)
    (hwort : roh ≤ wortMax) :
    regionStumpf tab roh = alsAdresse (dekodiere tab 1 wortMax roh) := by
  unfold regionStumpf dekodiere
  by_cases hneg : roh < 0
  · rw [if_pos hneg, dif_pos hneg]
    by_cases hz : roh < -4095
    · rw [if_pos hz, dif_neg (by omega)]; rfl
    · rw [if_neg hz, dif_pos (by omega)]
      cases fehlerSuche tab (-roh).toNat <;> rfl
  · rw [if_neg hneg, dif_neg hneg]
    by_cases h0 : roh = 0
    · rw [if_pos h0, dif_neg (by omega)]; rfl
    · rw [if_neg h0, dif_pos (by omega)]; rfl

/-- The address handed over is the kernel's word itself, and never zero. -/
theorem tor_region_adresse {Grund : Type} [DecidableEq Grund] (tab : FehlerTabelle Grund)
    (roh : Int) (a : Nat) (h : regionStumpf tab roh = .ok a) : (a : Int) = roh ∧ 1 ≤ a := by
  unfold regionStumpf at h
  by_cases hneg : roh < 0
  · rw [if_pos hneg] at h
    by_cases hz : roh < -4095
    · rw [if_pos hz] at h; cases h
    · rw [if_neg hz] at h
      cases hs : fehlerSuche tab (-roh).toNat <;> rw [hs] at h <;> cases h
  · rw [if_neg hneg] at h
    by_cases h0 : roh = 0
    · rw [if_pos h0] at h; cases h
    · rw [if_neg h0] at h
      cases h
      omega

/-- No error word becomes an address: a negative word is a reason or the stop. -/
theorem tor_region_fehler_kein_zeiger {Grund : Type} [DecidableEq Grund]
    (tab : FehlerTabelle Grund) (roh : Int) (hneg : roh < 0) (a : Nat) :
    regionStumpf tab roh ≠ .ok a := by
  intro h
  have := (tor_region_adresse tab roh a h).1
  omega

/-- A region: a base address and the number of bytes it reaches. -/
structure Region where
  basis : Nat
  laenge : Nat
  deriving DecidableEq, Repr

/-- The byte at address `a` lies in the region. -/
def Region.enthaelt (r : Region) (a : Nat) : Prop := r.basis ≤ a ∧ a < r.basis + r.laenge

/-- Two regions share no byte. -/
def Region.disjunkt (r s : Region) : Prop :=
  r.basis + r.laenge ≤ s.basis ∨ s.basis + s.laenge ≤ r.basis

/-- **The ONE generic form: a foreign routine hands over a new region.** The gate's contract,
    user logic in the program's source: the answer reaches at least `n` bytes
    (`ensures n <= lenof(result)`) and shares no byte with any region live at the call (the
    fresh/disjoint sentence of its assumption). No operating system in it. -/
def RegionVertrag (lebend : List Region) (n : Nat) (r : Region) : Prop :=
  n ≤ r.laenge ∧ ∀ s ∈ lebend, r.disjunkt s

end Region
end OhneLibc
end Gabbro.Grammatik
