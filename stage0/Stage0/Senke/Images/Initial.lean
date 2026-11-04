/- Attach canonical initialized world bytes to the single emitted image payload.
   Startup owns Bild and its stacks; this module changes only [Y.lo, Y.hi). -/
module
public import Stage0.Senke.Images.Bild
public import Stage0.Senke.Welt.Initial.Readback
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Replace exactly the typed world extent. The existing image supplies header, code,
    every initialized start stack, alignment padding and the zero lock suffix.
    The caller uses the checked unit's same sp0 witness and the final relocated layout. -/
def Bild.initializedBytes (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) : List Runner.B :=
  b.bytes.take (b.Y.lo - Runner.Prog.IMG) ++
    (initialWorldBytes u valid b.Y ++ b.bytes.drop (b.Y.hi - Runner.Prog.IMG))

/-- The actual builder preserves the canonical storage geometry when it relocates
    code addresses and records stack metadata. No independent layout witness is needed. -/
theorem initialLayout_bild {u : UProg} {P : Programm (declOf u)} {passes : Nat}
    {tor : (declOf u).Ax → Option TorB} {fs : List (declOf u).Fn}
    {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {args : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {slots req : Nat} {b : Bild (declOf u)}
    (emitted : bild passes P (layU u tor) fs pos name main args starts slots req = .ok b) :
    InitialLayout u b.Y := by
  simp only [bild] at emitted
  split at emitted
  · cases emitted
  · next preliminary firstPass =>
    split at emitted
    · cases emitted
    · next relocated secondPass =>
      split at emitted
      · simp only [Except.ok.injEq] at emitted
        subst b
        refine ⟨fun _ => rfl, fun _ _ => rfl, rfl, fun t => ?_⟩
        simp only [Lay.count, layU, ite_self, Int.natCast_zero, Int.add_zero]
      · split at emitted
        · cases emitted
        · split at emitted
          · cases emitted
          · split at emitted
            · cases emitted
            · split at emitted
              · cases emitted
              · split at emitted
                · cases emitted
                · split at emitted
                  · cases emitted
                  · cases emitted

/-- Bounds are inherited from the actual image layout check; initialization changes
    neither image size nor its permitted address range. -/
theorem Bild.initializedBytes_length {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (layout : InitialLayout u b.Y)
    (lower : Runner.Prog.IMG ≤ b.Y.lo) (upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length) :
    (b.initializedBytes u valid).length = b.bytes.length := by
  have extent := layout.extent
  have length := layout.bytes_length valid
  have takeBound : b.Y.lo - Runner.Prog.IMG ≤ b.bytes.length := by omega
  simp only [Bild.initializedBytes, List.length_append, List.length_take,
    List.length_drop, Nat.min_eq_left takeBound]
  omega

/-- Header, code, all source-start argument words and stack padding below the world
    are byte-for-byte identical to the startup image. -/
theorem Bild.initializedBytes_take {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (bound : b.Y.lo - Runner.Prog.IMG ≤ b.bytes.length) :
    (b.initializedBytes u valid).take (b.Y.lo - Runner.Prog.IMG) =
      b.bytes.take (b.Y.lo - Runner.Prog.IMG) := by
  have prefixLength : (b.bytes.take (b.Y.lo - Runner.Prog.IMG)).length =
      b.Y.lo - Runner.Prog.IMG := by simp only [List.length_take, Nat.min_eq_left bound]
  have kept := @List.take_append_length Runner.B
    (b.bytes.take (b.Y.lo - Runner.Prog.IMG))
    (initialWorldBytes u valid b.Y ++ b.bytes.drop (b.Y.hi - Runner.Prog.IMG))
  simpa only [Bild.initializedBytes, prefixLength] using kept

/-- Every byte after the typed world is retained, including all lock words. -/
theorem Bild.initializedBytes_drop {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (layout : InitialLayout u b.Y)
    (lower : Runner.Prog.IMG ≤ b.Y.lo) (upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length) :
    (b.initializedBytes u valid).drop (b.Y.hi - Runner.Prog.IMG) =
      b.bytes.drop (b.Y.hi - Runner.Prog.IMG) := by
  have extent := layout.extent
  have length := layout.bytes_length valid
  have takeBound : b.Y.lo - Runner.Prog.IMG ≤ b.bytes.length := by omega
  have prefixLength : (b.bytes.take (b.Y.lo - Runner.Prog.IMG) ++
      initialWorldBytes u valid b.Y).length = b.Y.hi - Runner.Prog.IMG := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left takeBound]
    omega
  have kept := @List.drop_append_length Runner.B
    (b.bytes.take (b.Y.lo - Runner.Prog.IMG) ++ initialWorldBytes u valid b.Y)
    (b.bytes.drop (b.Y.hi - Runner.Prog.IMG))
  simpa only [Bild.initializedBytes, prefixLength, List.append_assoc] using kept

/-- The one loaded payload decomposes at the same final layout used to encode values. -/
theorem Bild.initializedBytes_parts {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (layout : InitialLayout u b.Y)
    (lower : Runner.Prog.IMG ≤ b.Y.lo) (upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length)
    {m : Runner.Mem} (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) :
    BytesAt m Runner.Prog.IMG (b.bytes.take (b.Y.lo - Runner.Prog.IMG)) ∧
    BytesAt m b.Y.lo (initialWorldBytes u valid b.Y) ∧
    BytesAt m b.Y.hi (b.bytes.drop (b.Y.hi - Runner.Prog.IMG)) := by
  have extent := layout.extent
  have length := layout.bytes_length valid
  have takeBound : b.Y.lo - Runner.Prog.IMG ≤ b.bytes.length := by omega
  have prefixLength : (b.bytes.take (b.Y.lo - Runner.Prog.IMG)).length =
      b.Y.lo - Runner.Prog.IMG := by simp only [List.length_take, Nat.min_eq_left takeBound]
  have parts : BytesAt m Runner.Prog.IMG
      (b.bytes.take (b.Y.lo - Runner.Prog.IMG) ++
        (initialWorldBytes u valid b.Y ++ b.bytes.drop (b.Y.hi - Runner.Prog.IMG))) := loaded
  have world := parts.right.left
  have suffix := parts.right.right
  rw [prefixLength] at world suffix
  have worldAddress : Runner.Prog.IMG + (b.Y.lo - Runner.Prog.IMG) = b.Y.lo := by omega
  have suffixAddress : Runner.Prog.IMG + (b.Y.lo - Runner.Prog.IMG) +
      (initialWorldBytes u valid b.Y).length = b.Y.hi := by omega
  exact ⟨parts.left, by rwa [worldAddress] at world, by rwa [suffixAddress] at suffix⟩

/-- No fresh whole-image initialization or recursive validity premise: the bytes
    establish the source world whose same sp0 witness also initializes the starts. -/
theorem Bild.initializedBytes_world {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (layout : InitialLayout u b.Y)
    (lower : Runner.Prog.IMG ≤ b.Y.lo) (upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length)
    {m : Runner.Mem} (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) :
    WeltAt m b.Y (initialWorld u valid) :=
  initialWorldBytes_at layout (b.initializedBytes_parts valid layout lower upper loaded).2.1

end Gabbro.Stage0.Senke
