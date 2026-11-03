module

public import Grammatik.Parser.Profil.Register

@[expose] public section

/-!
  File:      Grammatik/Parser/Profil/Eintritt.lean
  Subject:   **C14: userspace entry and guest boundary, the part that can be stated before the C08/C12
             services exist.** What a userspace `entry` item may be to be admitted and what an `entrust` item
             needs to be admitted. (The link from an admitted entry's root to the roots the checker judged is
             `Zielsatz/Projekte/Profil.lean`, `eintritt_wurzel_in_ws`.)

  * `UserEntryBinding`/`eintrittB` -- a DISPATCH-ONLY entry: a decodable architecture, no vector, no
    interrupt routing, no register state (`regs in/out`, `preserves`, `clobbers`), no declared stack region,
    no per-CPU/IST/nesting, and every dispatch root a declared function. Anything else (the hardware entry,
    register-state manipulation, a declared stack region that needs the C08 start service and the C12
    forward-only handle) stays REFUSED by name; it is never erased. Extraction runs on the RESOLVED items
    (`pre108`), where dispatch roots and function names are the same keys.
  * Guest admission is canonical in `Logik/Ruf/Guest/Boundary.lean`; isolation
    is a `GuestServicePflicht` under C08 user logic. The source form still
    carries no service binding, so it has a named refusal below. The historical
    `assume` field cannot supply software isolation. Guest instructions are
    never executed as G code or given Gabbro body guarantees.

  Not here: the generated trampoline, the exact forwarding of C12's `Ty.entry` handle, the stack region and
  the C08 start service, activation/return/join behaviour against `FadenSchritt`/GX starts. Those need the
  C08/C12 interfaces and remain refused (`Stage0.Profil.checkEntry`).
-/

namespace Gabbro.Grammatik.Parser.ProfilBindung

open Gabbro.Grammatik

/-- The supported ordinary userspace ABI adapters (closed): dispatch only, no register state. -/
inductive UserAbi where
  | verteilung
  deriving DecidableEq, Repr

/-- A userspace entry as admitted. -/
structure UserEntryBinding where
  name : String
  arch : Nat
  abi : UserAbi
  wurzeln : List String
  deriving Repr

mutual
/-- The names of the functions of an item (`fn`, `extern`/prototype, `asm`), modules opened. -/
def fnNamenI : SItemTief → List String
  | .modT _ b => fnNamenL b
  | .pubT it => fnNamenI it
  | .gateT it => fnNamenI it
  | .fnT s _ => [s.name]
  | .protoT s => [s.name]
  | .asmT s _ => [s.name]
  | .adaptT s _ _ _ => [s.name]
  | _ => []
/-- The list form. -/
def fnNamenL : List SItemTief → List String
  | [] => []
  | it :: rest => fnNamenI it ++ fnNamenL rest
end

mutual
/-- The `entry` items of an item, modules opened. -/
def eintritteI : SItemTief → List SEingang
  | .modT _ b => eintritteL b
  | .pubT it => eintritteI it
  | .gateT it => eintritteI it
  | .entryT e => [e]
  | _ => []
/-- The list form. -/
def eintritteL : List SItemTief → List SEingang
  | [] => []
  | it :: rest => eintritteI it ++ eintritteL rest
end

/-- **A userspace entry is admitted**: dispatch only (right-nested, one clause per refusal). -/
def eintrittB (fns : List String) (e : SEingang) : Bool :=
  (wertVon .arch e.arch).isSome && (e.vektor.isNone && (e.via.isNone &&
    (e.regIn.isEmpty && (e.regOut.isEmpty && (e.erhaelt.isEmpty && (e.kills.isEmpty &&
    (strEq e.stapel "" && ((e.perCpu == false) && (e.ist.isNone && (e.nest.isNone &&
    e.dispatch.all (fun w => fns.any (fun f => strEq f w))))))))))))

/-- The binding of an admitted entry. -/
def eintrittVon (fns : List String) (e : SEingang) : Option UserEntryBinding :=
  if eintrittB fns e then
    (wertVon .arch e.arch).map fun a => ⟨e.name, a, .verteilung, e.dispatch⟩
  else none

theorem isNone_eq {α : Type} {o : Option α} (h : o.isNone = true) : o = none := by
  cases o <;> simp_all

theorem isEmpty_eq {α : Type} {l : List α} (h : l.isEmpty = true) : l = [] := by
  cases l <;> simp_all

/-- What an admitted entry is: a decodable architecture, nothing of the hardware entry, no register state,
    no stack region, and dispatch roots that are declared functions. -/
theorem eintrittB_sound {fns : List String} {e : SEingang} (h : eintrittB fns e = true) :
    (∃ a, wertVon .arch e.arch = some a) ∧ e.vektor = none ∧ e.via = none ∧ e.regIn = [] ∧ e.regOut = [] ∧
      e.erhaelt = [] ∧ e.kills = [] ∧ e.stapel = "" ∧ e.perCpu = false ∧ e.ist = none ∧ e.nest = none ∧
      ∀ w ∈ e.dispatch, ∃ f ∈ fns, strEq f w = true := by
  unfold eintrittB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨ha, hv, hvia, hri, hro, her, hk, hs, hp, hi, hn, hd⟩ := h
  refine ⟨?_, isNone_eq hv, isNone_eq hvia, isEmpty_eq hri, isEmpty_eq hro, isEmpty_eq her,
    isEmpty_eq hk, (strEq_eq _ _).mp hs, beq_iff_eq.mp hp, isNone_eq hi, isNone_eq hn, ?_⟩
  · cases hw : wertVon .arch e.arch with
    | none => simp [hw] at ha
    | some a => exact ⟨a, rfl⟩
  · intro w hw
    obtain ⟨f, hf, hsf⟩ := List.any_eq_true.mp (List.all_eq_true.mp hd w hw)
    exact ⟨f, hf, hsf⟩

/-- An admitted entry has no register state and no stack region: those stay refused. -/
theorem eintritt_ohne_registerzustand {fns : List String} {e : SEingang}
    (h : eintrittB fns e = true) : e.regIn = [] ∧ e.regOut = [] ∧ e.stapel = "" :=
  let s := eintrittB_sound h
  ⟨s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.2.2.1⟩

/-! ## The source guest boundary -/

/-- Shared source-header admission. Complete service resolution, ownership and
    contracts are checked by the canonical elaborator against the actual unit;
    this check never treats a historical assume name as software isolation. -/
def gastQuellePruefung (arch : String) (registers : List SRegBind)
    (stack assumption : String) (service : Option String) : Except String Unit := do
  if (wertVon .arch arch).isNone then throw "entrust: unknown userspace ABI"
  if !registers.isEmpty then throw "entrust: register-state or privileged transfer is excluded"
  if service.isNone then throw "entrust: missing isolation service binding"
  if !stack.isEmpty || !assumption.isEmpty then
    throw "entrust: register-state or privileged transfer is excluded"

/-- An absent source service is always refused, regardless of code labels. -/
theorem gastQuelle_ohne_dienst (arch : String)
    (ha : (wertVon .arch arch).isNone = false) :
    gastQuellePruefung arch [] "" "" none =
      .error "entrust: missing isolation service binding" := by
  simp [gastQuellePruefung, ha]

end Gabbro.Grammatik.Parser.ProfilBindung
