/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Ankunft.lean
  Subject:   ARRIVAL REGIONS ARE STABLE UNDER AN INSTRUCTION (MK-04). `Zustand.griff` issues a
             context's handle for a region cell from the arrival regions of that context's frame.
             A step may not quietly add or remove that grant, or authority could change between the
             checker's decision and the executed step. Every instruction keeps the acting frame's
             arrival-region list. `bindeRegion` and `starte` read it (to form a view or the callee's
             entry slots) but build their result with a `{ frame with … }` update, so neither case is
             exempt. The statement is proved once by case distinction; a witness shows the read is
             real: `bindeRegion` succeeds with a grant and refuses without one.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Klasse

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- **An instruction step leaves the arrival regions of the acting frame unchanged.** The handle
    issued by `Zustand.griff` therefore names the same slots before and after every step. The third
    argument is the liveness of the slots, as passed to `Befehl.auswerten`. No case is exempt:
    `bindeRegion` reads a granted extent and `starte` checks the number of owned-region parameters,
    but both return a frame update that keeps `arrivalRegions`. -/
def AnkunftUnveraendertAussage : Prop :=
  ∀ (b : Befehl) (frame : Rahmen) (live : Nat → Bool),
    (b.auswerten frame live).arrivalRegions = frame.arrivalRegions

/-- A successful entry keeps the grant of the caller's frame: both arms of
    `Rahmen.eintrittArgumente` are a `{ frame with … }` update. -/
private theorem eintrittArgumente_arrival {frame : Rahmen} {types : List (Ty .value)}
    {entry : Rahmen} (h : frame.eintrittArgumente types = some entry) :
    entry.arrivalRegions = frame.arrivalRegions := by
  unfold Rahmen.eintrittArgumente at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      rfl
    · cases h

/-- A call keeps the grant of the frame it enters from, on every guard outcome. -/
private theorem ruf_arrival (frame : Rahmen) (name : Identifier) (sources : List (Ty .value))
    (bind : Option (Ty .value)) :
    (frame.ruf name sources bind).arrivalRegions = frame.arrivalRegions := by
  simp only [Rahmen.ruf, Id.run]
  repeat
    first
    | rfl
    | split

/-- Case split on `Befehl`. Every arm of `Befehl.auswerten` is a frame write, a record update, a
    halt, or a call/return; the helper functions likewise only update the given frame. The two
    region-touching arms are no different: `bindeRegion` reads a granted extent and returns
    `{ frame with pc, lokale }`; `starte` reads the grant through `Rahmen.eintrittArgumente` and
    enters through `Rahmen.ruf`. The two helpers above carry those arms, so no case is exempt. -/
theorem ankunftUnveraendert : AnkunftUnveraendertAussage := by
  intro b frame live
  cases b <;>
    simp only [Befehl.auswerten, Rahmen.schreibe, Rahmen.installSchema, Rahmen.halt,
      Rahmen.pass, Rahmen.setzeMass, ruf_arrival, Rahmen.rueckkehr, Rahmen.bindeRegion, Id.run]
  all_goals
    repeat
      first
      | rfl
      | split
      | apply eintrittArgumente_arrival
        assumption

private def ankuenftsRahmen (regions : List Katalog.Strecke) : Rahmen :=
  { Rahmen.start [] with
    lokale := [some ⟨.ownedRegion, 0⟩]
    arrivalRegions := regions }

private theorem ankuenftsReceiver (regions : List Katalog.Strecke) :
    (ankuenftsRahmen regions).lokale[0]?.join.bind (wertAls .ownedRegion) = some 0 := by
  simp only [ankuenftsRahmen, List.getElem?_cons_zero, Option.join, Option.bind_some, id_eq,
    wertAls, dif_pos rfl]

private theorem ankuenftsUnborrowed (regions : List Katalog.Strecke) :
    (ankuenftsRahmen regions).borrowsRegion 0 = false := by
  simp only [Rahmen.borrowsRegion, Dynamisch.borrowsRegion, ankuenftsRahmen, Rahmen.start,
    List.any_cons, List.any_nil, Option.any_some, Bool.or_false, Bool.false_or]

/-- **The read is not vacuous.** There is a command and a frame for which the result depends on the
    arrival-region list: `bindeRegion` turns a granted slot into a physical address, and refuses the
    same frame with an empty grant. Both results differ in their stop status. -/
theorem ankunft_wird_gelesen :
    ∃ (frame : Rahmen) (regions : List Katalog.Strecke),
      (Befehl.bindeRegion 0 .address).auswerten frame (fun _ => true) ≠
        (Befehl.bindeRegion 0 .address).auswerten { frame with arrivalRegions := regions }
          (fun _ => true) := by
  let extent : Katalog.Strecke := ⟨0, 4096⟩
  let frame : Rahmen := ankuenftsRahmen [extent]
  have hpos : extent.von < 2 ^ frame.platform.ziel.physicalBits :=
    Nat.pow_pos (by decide) _
  let value : Dynamisch :=
    ⟨.address .physical, ⟨frame.platform.ziel.physicalBits, extent.von, hpos⟩⟩
  have hvalue : LowLevel.RegionInitializer.value frame.platform.ziel 0 extent .address =
      some value := by
    simp only [LowLevel.RegionInitializer.value, dif_pos hpos]
  have success : (Befehl.bindeRegion 0 .address).auswerten frame (fun _ => true) =
      { frame with pc := frame.pc + 1, lokale := some value :: frame.lokale } := by
    simp only [Befehl.auswerten, Rahmen.bindeRegion, Id.run, ankuenftsReceiver,
      List.getElem?_cons_zero, ankuenftsUnborrowed, Bool.not_true, Bool.false_or,
      Bool.false_eq_true, ite_false, hvalue]
    rfl
  have refused : (Befehl.bindeRegion 0 .address).auswerten
        { frame with arrivalRegions := [] } (fun _ => true) =
      ({ frame with arrivalRegions := [] } : Rahmen).halt .ungueltigerBereich := by
    simp only [Befehl.auswerten, Rahmen.bindeRegion, Id.run, ankuenftsReceiver,
      List.getElem?_nil, Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
  refine ⟨frame, [], ?_⟩
  intro equal
  have hs := congrArg (fun f : Rahmen => f.stopp) equal
  rw [success, refused] at hs
  change none = some .ungueltigerBereich at hs
  cases hs

end Gabbro.Core.Ast.Semantik
