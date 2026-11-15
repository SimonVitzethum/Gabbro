/- C16 remaining forms (3): foreign gates end to end.

   A gate may name a C08 foreign body. The wrapper is still an ordinary nullary
   `UFn` threading the Duty; the gate call is the ordinary foreign call Stage 0
   already lowers. The infallible answer-less case rides `axCall`; the fallible
   `int`-answered case rides `bindAxElse` whose error branch rethrows the exact
   reason while retaining the Duty. Only a normal gate return completes the
   evidence fold. An unclosed error branch is refused by the lowering:
   dropping it would drop the Duty's discharge path. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Source
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Int.Repr
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

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

set_option Elab.async false

/-- The admission Props follow from the Bools. -/
theorem fremd_admission :
    CheckAdmission checkPFremd (List.finRange uFremd.fns.length) checkChecksFremd :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : uFremd.tabs.length = 0 := by rw [uFremd_tabs_leer]; rfl
      have t' : Fin uFremd.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : uFremd.globs.length = 0 := by rw [uFremd_globs_leer]; rfl
      have g' : Fin uFremd.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp fremd_checkB

theorem fremdFallible_admission :
    CheckAdmission checkPFremdFallible (List.finRange uFremdFallible.fns.length) checkChecksFremdFallible :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : uFremdFallible.tabs.length = 0 := by rw [uFremdFallible_tabs_leer]; rfl
      have t' : Fin uFremdFallible.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : uFremdFallible.globs.length = 0 := by rw [uFremdFallible_globs_leer]; rfl
      have g' : Fin uFremdFallible.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp fremdFallible_checkB

/-! ## The completed reports discharge through the foreign wrappers -/

/-- Every derived check carries exactly one floor entry. -/
theorem fremd_boeden :
    (checkChecksFremd.map fun d => d.boden.length) = [1] := by kernel_rfl

theorem fremdFallible_boeden :
    (checkChecksFremdFallible.map fun d => d.boden.length) = [1] := by kernel_rfl

theorem fremd_boden_laenge (d : CheckDecl (declOf uFremd))
    (hd : d ∈ checkChecksFremd) : d.boden.length = 1 := by
  have hm : d.boden.length ∈ checkChecksFremd.map (fun d => d.boden.length) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [fremd_boeden] at hm
  exact List.mem_singleton.mp hm

theorem fremdFallible_boden_laenge (d : CheckDecl (declOf uFremdFallible))
    (hd : d ∈ checkChecksFremdFallible) : d.boden.length = 1 := by
  have hm : d.boden.length ∈ checkChecksFremdFallible.map (fun d => d.boden.length) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [fremdFallible_boeden] at hm
  exact List.mem_singleton.mp hm

/-- The passing report completes the infallible foreign-gated check. -/
theorem fremd_abschluss (d : CheckDecl (declOf uFremd))
    (hd : d ∈ checkChecksFremd) :
    CheckAbschluss checkPFremd d messBerichtWahr := by
  obtain ⟨hexp, _, _, _, _⟩ := fremd_admission
  refine ⟨hexp d hd, messBerichtWahr_vollstaendig, ?_⟩
  show messBerichtWahr.boeden.length = d.boden.length
  rw [show messBerichtWahr.boeden.length = 1 from rfl, fremd_boden_laenge d hd]

/-- The passing report completes the fallible foreign-gated check. -/
theorem fremdFallible_abschluss (d : CheckDecl (declOf uFremdFallible))
    (hd : d ∈ checkChecksFremdFallible) :
    CheckAbschluss checkPFremdFallible d messBerichtWahr := by
  obtain ⟨hexp, _, _, _, _⟩ := fremdFallible_admission
  refine ⟨hexp d hd, messBerichtWahr_vollstaendig, ?_⟩
  show messBerichtWahr.boeden.length = d.boden.length
  rw [show messBerichtWahr.boeden.length = 1 from rfl, fremdFallible_boden_laenge d hd]

/-- The foreign wrapper discharges the completed report. -/
theorem fremd_entladung (d : CheckDecl (declOf uFremd))
    (hd : d ∈ checkChecksFremd) :
    ∃ g, CheckEntladung checkPFremd d messBerichtWahr g := by
  have hlen : d.gates.length = 1 := by
    have hm : d.gates.length ∈ checkChecksFremd.map (fun d => d.gates.length) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    have hr : (checkChecksFremd.map fun d => d.gates.length) = [1] := by kernel_rfl
    rw [hr] at hm
    exact List.mem_singleton.mp hm
  match hg : d.gates with
  | [] => simp [hg] at hlen
  | g :: _ =>
    refine ⟨g, fremd_abschluss d hd, ?_, hg ▸ List.mem_cons_self⟩
    have hall : (checkChecksFremd.all fun d =>
        d.gates.all fun g =>
          decide (d.duty ∈ ((declOf uFremd).signatur g).konsumiert)) = true := by
      decide +kernel
    have h1 := List.all_eq_true.mp hall d hd
    have hmem : g ∈ d.gates := hg ▸ List.mem_cons_self
    have h2 := List.all_eq_true.mp h1 g hmem
    exact of_decide_eq_true h2

/-- Structural eligibility to consume the completed report. Execution evidence
    additionally requires a normal gate return (`torAbschluss`); a reason
    return preserves the pending Duty instead. -/
theorem fremdFallible_entladung (d : CheckDecl (declOf uFremdFallible))
    (hd : d ∈ checkChecksFremdFallible) :
    ∃ g, CheckEntladung checkPFremdFallible d messBerichtWahr g := by
  have hlen : d.gates.length = 1 := by
    have hm : d.gates.length ∈ checkChecksFremdFallible.map (fun d => d.gates.length) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    have hr : (checkChecksFremdFallible.map fun d => d.gates.length) = [1] := by kernel_rfl
    rw [hr] at hm
    exact List.mem_singleton.mp hm
  match hg : d.gates with
  | [] => simp [hg] at hlen
  | g :: _ =>
    refine ⟨g, fremdFallible_abschluss d hd, ?_, hg ▸ List.mem_cons_self⟩
    have hall : (checkChecksFremdFallible.all fun d =>
        d.gates.all fun g =>
          decide (d.duty ∈ ((declOf uFremdFallible).signatur g).konsumiert)) = true := by
      decide +kernel
    have h1 := List.all_eq_true.mp hall d hd
    have hmem : g ∈ d.gates := hg ▸ List.mem_cons_self
    have h2 := List.all_eq_true.mp h1 g hmem
    exact of_decide_eq_true h2

/-- The discharged entries satisfy the goal leg. -/
theorem fremd_treue (d : CheckDecl (declOf uFremd))
    (hd : d ∈ checkChecksFremd) (g : (declOf uFremd).Fn)
    (h : CheckEntladung checkPFremd d messBerichtWahr g) :
    Zielsatz.CheckTreueG checkPFremd [d] [⟨d.probe, messBerichtWahr, false, some g⟩] :=
  treue_aus_entladung h

theorem fremdFallible_treue (d : CheckDecl (declOf uFremdFallible))
    (hd : d ∈ checkChecksFremdFallible) (g : (declOf uFremdFallible).Fn)
    (h : CheckEntladung checkPFremdFallible d messBerichtWahr g) :
    Zielsatz.CheckTreueG checkPFremdFallible [d] [⟨d.probe, messBerichtWahr, false, some g⟩] :=
  treue_aus_entladung h

/-! ## Refusal: an unclosed error branch drops the discharge path -/

/-- The fallible wrapper with its error branch unclosed: the end block marker
    is gone, so the error path falls through instead of threading the Duty. -/
def uFremdOhneFehler : UProg :=
  { uFremdFallible with
    fns := uFremdFallible.fns.map fun f =>
      if strEq f.name "p#tor#f" then
        { f with body := f.body.filter fun s => match s with
          | .blkEnd => false | _ => true }
      else f }
/-- The lowering refuses the unclosed error branch: no silent Duty drop. -/
theorem uFremdOhneFehler_verweigert :
    (lowerAllg uFremdOhneFehler).toOption.isNone = true := by
  decide +kernel

/-- The selected foreign gate wrapper retains the declared reason channel. -/
def fremdTorIndex : (declOf uFremdFallible).Fn :=
  (⟨3, by decide +kernel⟩ : Fin uFremdFallible.fns.length)

example : (declOf uFremdFallible).gruende fremdTorIndex = 1 := by kernel_rfl

/-- The generated error handler rethrows the foreign case rather than inventing
    a successful numeric answer. -/
example : (uFremdFallible.fns.find? (fun f => strEq f.name "p#tor#f")).map
    (fun f => (f.gruende, f.body)) =
    some (1, [.bindAxElse "ans" "f" [] "e", .matchWhyBeg "e",
      .ret (.why 0), .blkEnd, .ret (.why 0), .blkEnd]) := by kernel_rfl

/-- An error return cannot consume this gate's completed report, even when the
    log later contains unrelated normal returns. -/
theorem fremdTor_fehler_pending
    (rho : Env (declOf uFremdFallible) ((declOf uFremdFallible).params fremdTorIndex))
    (reason : Fin ((declOf uFremdFallible).gruende fremdTorIndex))
    (s0 s1 : World (declOf uFremdFallible))
    (rest : List (RufEreignisF (declOf uFremdFallible))) :
    torAbschluss fremdTorIndex 0 (.why fremdTorIndex rho reason s0 s1 :: rest) = false :=
  torAbschluss_fehler fremdTorIndex rho reason s0 s1 rest

section Erfolg
-- The unit stays folded: the statement only instantiates the generic lemma.
attribute [local irreducible] uFremdFallible fremdTorIndex
/-- A normal return completes the same activation. -/
theorem fremdTor_erfolg
    (rho : Env (declOf uFremdFallible) ((declOf uFremdFallible).params fremdTorIndex))
    (value : ErgVal (declOf uFremdFallible) ((declOf uFremdFallible).erg fremdTorIndex))
    (s0 s1 : World (declOf uFremdFallible)) :
    torPush fremdTorIndex [.eintritt fremdTorIndex rho s0,
      .rueck fremdTorIndex rho value s0 s1] = true :=
  torPush_erfolg fremdTorIndex rho value s0 s1
end Erfolg

/-- A gate's source declaration supplies no actual parameter arguments. -/
example : (elabText
    "impl fn g(x: u64) { return; } check p { claim \"c\" measures x gates g can_fail { return true; } }").toOption.isNone = true := by
  decide +kernel

/-- Ordinary fallible gate wrappers keep their named refusal until a written
    reason policy is supplied; no error is converted into normal success. -/
example : (elabText
    "reason R { A = 0 \"t\" exhaustive } impl fn g() -> u64 or R { return 1; } check p { claim \"c\" measures x gates g can_fail { return true; } }").toOption.isNone = true := by
  decide +kernel

end Gabbro.Grammatik.Parser.Uebersetze
