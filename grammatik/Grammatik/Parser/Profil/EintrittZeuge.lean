module

public import Grammatik.Parser.Profil.Eintritt
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

/-!
  File:      Grammatik/Parser/Profil/EintrittZeuge.lean
  Subject:   WITNESSES for the userspace entry admission and the guest boundary (C14): a dispatch-only entry
             admitted, its binding read off, one negative twin per refusal (vector, interrupt routing,
             register state, stack region, per-CPU, unsupported architecture, unknown root); a boundary that
             WOULD be admitted with a declared service, and the one read off the source, which is refused.
-/

namespace Gabbro.Grammatik.Parser.ProfilBindung

open Gabbro.Grammatik

set_option maxRecDepth 100000

/-- A dispatch-only userspace entry with one root. -/
def ezE : SEingang :=
  { name := "main_entry", vektor := none, via := none, arch := "x86_64", regIn := [], regOut := [],
    erhaelt := [], kills := [], stapel := "", perCpu := false, ist := none, nest := none,
    dispatch := ["worker"] }

theorem ez_zulaessig : eintrittB ["worker"] ezE = true := by decide

/-- The binding names the entry, the decoded architecture, the ABI adapter and the roots. -/
theorem ez_bindung :
    (eintrittVon ["worker"] ezE).map (fun b => (b.name, b.arch, b.abi, b.wurzeln)) =
      some ("main_entry", 1, UserAbi.verteilung, ["worker"]) := by
  decide

/-- JOINT: the admitted entry's soundness consequences instantiated on the fixture. -/
theorem ez_ohne_register : ezE.regIn = [] ∧ ezE.regOut = [] ∧ ezE.stapel = "" :=
  eintritt_ohne_registerzustand ez_zulaessig

theorem ez_vektor : eintrittB ["worker"] { ezE with vektor := some (.lit 14) } = false := by decide
theorem ez_via : eintrittB ["worker"] { ezE with via := some "idt" } = false := by decide
theorem ez_register : eintrittB ["worker"] { ezE with regIn := [.binds "a" "rdi"] } = false := by decide
theorem ez_stapel : eintrittB ["worker"] { ezE with stapel := "stack" } = false := by decide
theorem ez_percpu : eintrittB ["worker"] { ezE with perCpu := true } = false := by decide
theorem ez_arch : eintrittB ["worker"] { ezE with arch := "z80" } = false := by decide
theorem ez_wurzel : eintrittB ["worker"] { ezE with dispatch := ["ghost"] } = false := by decide
theorem ez_kills : eintrittB ["worker"] { ezE with kills := ["rax"] } = false := by decide

/-- The registry of the fixture: the assumption the boundary names. -/
def ezReg : List AnnahmeKennung :=
  [⟨"guest_stays_in_room", none, "The guest cannot leave its region.", .probe "probe_guest"⟩]

/-- A boundary with a declared service WOULD be admitted: the admission is not vacuous. -/
theorem ez_gast_mit_dienst :
    gastB ["guest_image"] ["isolate_svc"] ezReg
      ⟨"jit", "guest_image", "x86_64", some "isolate_svc", "guest_stays_in_room"⟩ = true := by decide

/-- The boundary read off an `entrust` item has no service and is refused. -/
theorem ez_gast_quelle :
    gastB ["guest_image"] ["isolate_svc"] ezReg
      (gastVon "jit" "guest_image" "x86_64" "guest_stays_in_room") = false :=
  gastVon_abgelehnt _ _ _ _ _ _ _

/-- A boundary whose service is no declared function, or whose assumption is unresolved, is refused. -/
theorem ez_gast_unbekannt :
    gastB ["guest_image"] ["isolate_svc"] ezReg
      ⟨"jit", "guest_image", "x86_64", some "ghost", "guest_stays_in_room"⟩ = false ∧
    gastB ["guest_image"] ["isolate_svc"] ezReg
      ⟨"jit", "guest_image", "x86_64", some "isolate_svc", "nowhere"⟩ = false := by
  constructor <;> decide

end Gabbro.Grammatik.Parser.ProfilBindung
