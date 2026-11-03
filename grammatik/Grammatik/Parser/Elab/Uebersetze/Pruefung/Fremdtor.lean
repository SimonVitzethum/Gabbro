/- C16 remaining forms (3): foreign gates end to end.

   A gate may name a C08 foreign body. The wrapper is still an ordinary nullary
   `UFn` threading the Duty; the gate call is the ordinary foreign call Stage 0
   already lowers. The infallible answer-less case rides `axCall`; the fallible
   `int`-answered case rides `bindAxElse` whose error branch rethrows the exact
   reason while retaining the Duty. Only a normal gate return completes the
   evidence fold. An unclosed error branch is refused by the lowering:
   dropping it would drop the Duty's discharge path. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Falte
public import Grammatik.Parser.Elab.UebersetzeAllg3
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckDecide
public import Grammatik.Zielsatz.Kern.Akzeptiert.CheckProof
public import Grammatik.Kern.Syntax.Satz.PruefungMessung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

/-! ## The foreign-gated units, from source text -/

/-- The infallible foreign gate: the `axiom` body stays foreign, the wrapper
    calls it with `axCall` while threading the Duty. -/
def checkTextFremd : String :=
  "axiom f() effects { pure } unfalsifiable \"hw\"; impl fn g() { return; } check p { claim \"c\" measures x gates f can_fail { return true; } floor 2 >= 1 }"

/-- The fallible foreign gate: the `extern fn` with a reason channel is called
    with `bindAxElse`; the error branch preserves the reason channel. -/
def checkTextFremdFallible : String :=
  "reason R { A = 0 \"t\" exhaustive } extern fn f() -> u64 or R effects { pure }; impl fn g() { return; } check p { claim \"c\" measures x gates f can_fail { return true; } floor 2 >= 1 }"

/-- Both foreign-gated units elaborate. -/
theorem checkTextFremd_ok : (elabText checkTextFremd).toOption.isSome = true := by
  decide +kernel

theorem checkTextFremdFallible_ok :
    (elabText checkTextFremdFallible).toOption.isSome = true := by
  decide +kernel

/-- The elaborated units behind the foreign-gate witnesses. -/
def uFremd : UProg := (elabText checkTextFremd).toOption.get checkTextFremd_ok

def uFremdFallible : UProg :=
  (elabText checkTextFremdFallible).toOption.get checkTextFremdFallible_ok

/-- The foreign bodies stay foreign: they elaborate to `axs`, never to `fns`. -/
example : (elabText checkTextFremd).map (fun u => u.axs.map (·.name)) =
    .ok ["f"] := rfl

example : (elabText checkTextFremdFallible).map (fun u => u.axs.map (·.name)) =
    .ok ["f"] := rfl

/-- The wrappers travel as ordinary functions of the units. -/
example : (elabText checkTextFremd).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#tor#f"] := rfl

example : (elabText checkTextFremdFallible).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#tor#f"] := rfl

/-- The infallible wrapper calls the foreign body with `axCall`, threading the Duty. -/
example : (elabText checkTextFremd).map
    (fun u => (u.fns.find? fun f => strEq f.name "p#tor#f").map (·.body)) =
    .ok (some [.axCall "f" []]) := rfl

/-- The fallible wrapper threads the Duty through both paths: the call, the
    error-branch return and the branch marker. -/
example : (elabText checkTextFremdFallible).map
    (fun u => (u.fns.find? fun f => strEq f.name "p#tor#f").map
      fun f => (f.nimmt, f.gibt, f.body.length)) =
    .ok (some (["p#duty"], ["p#duty"], 6)) := rfl

/-- The units have no tables and no statics. -/
theorem uFremd_tabs_leer : uFremd.tabs = [] := rfl

theorem uFremd_globs_leer : uFremd.globs = [] := rfl

theorem uFremdFallible_tabs_leer : uFremdFallible.tabs = [] := rfl

theorem uFremdFallible_globs_leer : uFremdFallible.globs = [] := rfl

/-- Both units lower. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uFremd_lowered : (lowerAllg uFremd).toOption.isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem uFremdFallible_lowered :
    (lowerAllg uFremdFallible).toOption.isSome = true := by
  decide +kernel

/-- The lowered programs behind the foreign-gate witnesses. -/
def checkPFremd : Programm (declOf uFremd) :=
  ((lowerAllg uFremd).toOption.get uFremd_lowered).1

def checkPFremdFallible : Programm (declOf uFremdFallible) :=
  ((lowerAllg uFremdFallible).toOption.get uFremdFallible_lowered).1

/-- The checks derive. -/
theorem uFremd_checks_ok : (uCheckDecls uFremd).toOption.isSome = true := by
  decide +kernel

theorem uFremdFallible_checks_ok :
    (uCheckDecls uFremdFallible).toOption.isSome = true := by
  decide +kernel

def checkChecksFremd : List (CheckDecl (declOf uFremd)) :=
  (uCheckDecls uFremd).toOption.get uFremd_checks_ok

def checkChecksFremdFallible : List (CheckDecl (declOf uFremdFallible)) :=
  (uCheckDecls uFremdFallible).toOption.get uFremdFallible_checks_ok

/-! ## The Duty is declared and threaded, non-vacuously -/

/-- The derived checks travel under their elaborated names. -/
theorem fremd_namen :
    (uCheckDecls uFremd).map (List.map CheckDecl.name) = .ok ["p"] := rfl

theorem fremdFallible_namen :
    (uCheckDecls uFremdFallible).map (List.map CheckDecl.name) = .ok ["p"] := rfl

/-- The Duty is the declared mark `p#duty` at stage 0. -/
theorem fremd_duty_marke :
    (uCheckDecls uFremd).map
      (List.map fun d => (uFremd.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := rfl

theorem fremdFallible_duty_marke :
    (uCheckDecls uFremdFallible).map
      (List.map fun d => (uFremdFallible.marken.get d.duty.1, d.duty.2)) =
    .ok [("p#duty", 0)] := rfl

/-- The foreign wrappers discharge the Duty: they consume it in their lowered
    signatures. -/
theorem fremd_tor_threadet :
    (uCheckDecls uFremd).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf uFremd).signatur g).konsumiert)) =
    .ok true := by
  decide +kernel

theorem fremdFallible_tor_threadet :
    (uCheckDecls uFremdFallible).map (fun cs => cs.all fun d =>
      d.gates.all fun g =>
        decide (d.duty ∈ ((declOf uFremdFallible).signatur g).konsumiert)) =
    .ok true := by
  decide +kernel

/-! ## Acceptance with the real Duty -/

/-- The lowered units with their derived checks are admitted. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fremd_checkB :
    checkB checkPFremd [] [] (List.finRange uFremd.fns.length) checkChecksFremd = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fremdFallible_checkB :
    checkB checkPFremdFallible [] [] (List.finRange uFremdFallible.fns.length) checkChecksFremdFallible = true := by
  decide +kernel

/-- End-to-end acceptance from source text with a real Duty. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fremd_akzeptiert :
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fremdFallible_akzeptiert :
    AkzeptiertX checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible)
      (List.finRange uFremdFallible.fns.length) [] [] [] [] checkChecksFremdFallible = true := by
  decide +kernel

/-- The admission Props follow from the Bools. -/
theorem fremd_admission :
    CheckAdmission checkPFremd (List.finRange uFremd.fns.length) checkChecksFremd :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : uFremd.tabs.length = 0 := by rw [uFremd_tabs_leer]
      have t' : Fin uFremd.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : uFremd.globs.length = 0 := by rw [uFremd_globs_leer]
      have g' : Fin uFremd.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp fremd_checkB

theorem fremdFallible_admission :
    CheckAdmission checkPFremdFallible (List.finRange uFremdFallible.fns.length) checkChecksFremdFallible :=
  (checkB_iff (fun g => List.mem_finRange g)
    (fun t => by
      have h0 : uFremdFallible.tabs.length = 0 := by rw [uFremdFallible_tabs_leer]
      have t' : Fin uFremdFallible.tabs.length := t
      exact Fin.elim0 (h0 ▸ t'))
    (fun g => by
      have h0 : uFremdFallible.globs.length = 0 := by rw [uFremdFallible_globs_leer]
      have g' : Fin uFremdFallible.globs.length := g
      exact Fin.elim0 (h0 ▸ g'))).mp fremdFallible_checkB

/-! ## The completed reports discharge through the foreign wrappers -/

/-- Every derived check carries exactly one floor entry. -/
theorem fremd_boeden :
    (checkChecksFremd.map fun d => d.boden.length) = [1] := rfl

theorem fremdFallible_boeden :
    (checkChecksFremdFallible.map fun d => d.boden.length) = [1] := rfl

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
  refine ⟨hexp d hd, by decide, ?_⟩
  show messBerichtWahr.boeden.length = d.boden.length
  rw [show messBerichtWahr.boeden.length = 1 from rfl, fremd_boden_laenge d hd]

/-- The passing report completes the fallible foreign-gated check. -/
theorem fremdFallible_abschluss (d : CheckDecl (declOf uFremdFallible))
    (hd : d ∈ checkChecksFremdFallible) :
    CheckAbschluss checkPFremdFallible d messBerichtWahr := by
  obtain ⟨hexp, _, _, _, _⟩ := fremdFallible_admission
  refine ⟨hexp d hd, by decide, ?_⟩
  show messBerichtWahr.boeden.length = d.boden.length
  rw [show messBerichtWahr.boeden.length = 1 from rfl, fremdFallible_boden_laenge d hd]

/-- The foreign wrapper discharges the completed report. -/
theorem fremd_entladung (d : CheckDecl (declOf uFremd))
    (hd : d ∈ checkChecksFremd) :
    ∃ g, CheckEntladung checkPFremd d messBerichtWahr g := by
  have hlen : d.gates.length = 1 := by
    have hm : d.gates.length ∈ checkChecksFremd.map (fun d => d.gates.length) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    have hr : (checkChecksFremd.map fun d => d.gates.length) = [1] := rfl
    rw [hr] at hm
    exact List.mem_singleton.mp hm
  match hg : d.gates with
  | [] => simp [hg] at hlen
  | g :: _ =>
    refine ⟨g, fremd_abschluss d hd, ?_, List.mem_cons.mpr (Or.inl rfl)⟩
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
    have hr : (checkChecksFremdFallible.map fun d => d.gates.length) = [1] := rfl
    rw [hr] at hm
    exact List.mem_singleton.mp hm
  match hg : d.gates with
  | [] => simp [hg] at hlen
  | g :: _ =>
    refine ⟨g, fremdFallible_abschluss d hd, ?_, List.mem_cons.mpr (Or.inl rfl)⟩
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
  { uFremdFallible with fns := uFremdFallible.fns.map fun f =>
    if strEq f.name "p#tor#f" then
      { f with body := f.body.filter fun s => match s with
        | .blkEnd => false | _ => true }
    else f }

/-- The lowering refuses the unclosed error branch: no silent Duty drop. -/
theorem uFremdOhneFehler_verweigert :
    (lowerAllg uFremdOhneFehler).toOption.isNone = true := by
  decide +kernel

/-- The selected foreign gate wrapper retains the declared reason channel. -/
def fremdTorIndex : Fin uFremdFallible.fns.length := ⟨2, by decide +kernel⟩

example : (declOf uFremdFallible).gruende fremdTorIndex = 1 := rfl

/-- The generated error handler rethrows the foreign case rather than inventing
    a successful numeric answer. -/
example : (uFremdFallible.fns.find? (fun f => strEq f.name "p#tor#f")).map
    (fun f => (f.gruende, f.body)) =
    some (1, [.bindAxElse "ans" "f" [] "e", .matchWhyBeg "e",
      .ret (.why 0), .blkEnd, .ret (.why 0), .blkEnd]) := rfl

/-- An error return cannot consume this gate's completed report, even when the
    log later contains unrelated normal returns. -/
theorem fremdTor_fehler_pending
    (rho : Env (declOf uFremdFallible) ((declOf uFremdFallible).params fremdTorIndex))
    (s0 s1 : World (declOf uFremdFallible))
    (rest : List (RufEreignisF (declOf uFremdFallible))) :
    torAbschluss fremdTorIndex 0
      (.why fremdTorIndex rho ⟨0, by decide +kernel⟩ s0 s1 :: rest) = false := rfl

/-- A normal return completes the same activation. -/
theorem fremdTor_erfolg
    (rho : Env (declOf uFremdFallible) ((declOf uFremdFallible).params fremdTorIndex))
    (value : ErgVal (declOf uFremdFallible) ((declOf uFremdFallible).erg fremdTorIndex))
    (s0 s1 : World (declOf uFremdFallible)) :
    torPush fremdTorIndex [.eintritt fremdTorIndex rho s0,
      .rueck fremdTorIndex rho value s0 s1] = true := by
  simp [torPush, torAbschluss]

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
