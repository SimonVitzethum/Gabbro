/- Loaded initialized images: unchanged complete startup prefix and free lock bytes. -/
module
public import Stage0.Senke.Images.Initial
public import Stage0.Senke.Images.BildLese
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Startup's accepted complete stack payload determines the original image extent.
    The zero suffix begins after ALL starts, not after main alone. -/
theorem Bild.bytes_length_of_stacks {D : Deklaration} (b : Bild D) {stacks : List Runner.B}
    (made : startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stacks)
    (rootCount : b.rootArgs.length = b.roots.length)
    (codeEnd : b.fp0 = codeBase + 16 * b.code.length)
    (room : b.Ks * (b.roots.length + 1) ≤ b.K) :
    b.bytes.length = b.fp0 - Runner.Prog.IMG + 8 * b.K := by
  have stackLength := startStackBytes_length made
  simp only [List.length_cons, rootCount, Nat.mul_assoc] at stackLength
  have base : Runner.Prog.IMG ≤ b.fp0 := by simp only [codeEnd, codeBase]; omega
  simp only [Bild.bytes, made, Option.getD_some, List.length_append,
    Runner.Prog.leN, List.length_map, List.length_range, List.length_replicate]
  rw [stackLength]
  rw [flatMap_enc_len]
  simp only [codeBase] at codeEnd
  omega

/-- Loaded header, code and complete typed starts survive world initialization.
    BildLage.code can consume the right component with an arbitrary tail. -/
theorem Bild.initializedBytes_startup {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (layout : InitialLayout u b.Y) {stacks : List Runner.B}
    (made : startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stacks)
    (rootCount : b.rootArgs.length = b.roots.length)
    (codeEnd : b.fp0 = codeBase + 16 * b.code.length)
    (separate : b.fp0 + 8 * (b.Ks * (b.roots.length + 1)) ≤ b.Y.lo)
    (upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length)
    {m : Runner.Mem} (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) :
    BytesAt m Runner.Prog.IMG (Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 b.baseReq) ∧
    BytesAt m codeBase (b.code.flatMap encII ++ stacks) := by
  let prefix := Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 b.baseReq ++ b.code.flatMap encII ++ stacks
  have stackLength := startStackBytes_length made
  simp only [List.length_cons, rootCount, Nat.mul_assoc] at stackLength
  have prefixLength : prefix.length = b.fp0 - Runner.Prog.IMG + 8 * (b.Ks * (b.roots.length + 1)) := by
    simp only [prefix, List.length_append, Runner.Prog.leN, List.length_map,
      List.length_range, flatMap_enc_len, stackLength, Nat.mul_assoc]
    simp only [codeBase] at codeEnd
    omega
  have lower : Runner.Prog.IMG ≤ b.Y.lo := by simp only [codeBase] at codeEnd; omega
  have raw : b.bytes = prefix ++ List.replicate (8 * (b.K - b.Ks * (b.roots.length + 1))) 0 := by
    simp only [Bild.bytes, made, Option.getD_some, prefix, List.append_assoc]
  have early := (b.initializedBytes_parts valid layout lower upper loaded).1.take prefix.length
  have prefixBound : prefix.length ≤ b.Y.lo - Runner.Prog.IMG := by omega
  simp only [List.take_take, Nat.min_eq_left prefixBound] at early
  rw [raw, List.take_append_length] at early
  have early' : BytesAt m Runner.Prog.IMG
      ((Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 b.baseReq) ++ (b.code.flatMap encII ++ stacks)) := by
    simpa only [prefix, List.append_assoc] using early
  refine ⟨early'.left, ?_⟩
  have code := early'.right
  simpa only [List.length_append, Runner.Prog.leN, List.length_map, List.length_range, codeBase] using code

/-- World replacement leaves every lock byte zero, after the complete stack area.
    This is exactly the premise consumed by BildLage.sync. -/
theorem Bild.initializedBytes_locks {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (layout : InitialLayout u b.Y) {stacks : List Runner.B}
    (made : startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stacks)
    (rootCount : b.rootArgs.length = b.roots.length)
    (codeEnd : b.fp0 = codeBase + 16 * b.code.length)
    (separate : b.fp0 + 8 * (b.Ks * (b.roots.length + 1)) ≤ b.Y.lo)
    (ordered : b.Y.hi ≤ b.Y.sye) (inside : b.Y.sye ≤ b.fp0 + 8 * b.K)
    {m : Runner.Mem} (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) :
    BytesAt m b.Y.hi (List.replicate (b.Y.sye - b.Y.hi) 0) := by
  let prefix := Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 b.baseReq ++ b.code.flatMap encII ++ stacks
  have extent := layout.extent
  have rootRoom : b.Ks * (b.roots.length + 1) ≤ b.K := by omega
  have stackLength := startStackBytes_length made
  simp only [List.length_cons, rootCount, Nat.mul_assoc] at stackLength
  have prefixLength : prefix.length = b.fp0 - Runner.Prog.IMG + 8 * (b.Ks * (b.roots.length + 1)) := by
    simp only [prefix, List.length_append, Runner.Prog.leN, List.length_map,
      List.length_range, flatMap_enc_len, stackLength, Nat.mul_assoc]
    simp only [codeBase] at codeEnd
    omega
  have raw : b.bytes = prefix ++ List.replicate (8 * (b.K - b.Ks * (b.roots.length + 1))) 0 := by
    simp only [Bild.bytes, made, Option.getD_some, prefix, List.append_assoc]
  have imageLength := b.bytes_length_of_stacks made rootCount codeEnd rootRoom
  have base : Runner.Prog.IMG ≤ b.fp0 := by simp only [codeEnd, codeBase]; omega
  have lower : Runner.Prog.IMG ≤ b.Y.lo := by omega
  have upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length := by omega
  have suffix := (b.initializedBytes_parts valid layout lower upper loaded).2.2.take (b.Y.sye - b.Y.hi)
  have afterPrefix : prefix.length ≤ b.Y.hi - Runner.Prog.IMG := by omega
  have dropPrefix : prefix.drop (b.Y.hi - Runner.Prog.IMG) = [] :=
    List.drop_eq_nil_of_le afterPrefix
  rw [raw, List.drop_append, dropPrefix, List.nil_append, List.drop_replicate, List.take_replicate] at suffix
  have suffixRoom : b.Y.sye - b.Y.hi ≤
      8 * (b.K - b.Ks * (b.roots.length + 1)) - (b.Y.hi - Runner.Prog.IMG - prefix.length) := by omega
  simpa only [Nat.min_eq_left suffixRoom] using suffix

/-- Initialized typed cells end before the lock band; no limb aliases a lock. -/
theorem initializedWorld_lock_separation {u : UProg} {b : Bild (declOf u)}
    (storage : LayIn b.Y) (locks : LaySync b.Y) (cell : Zelle (declOf u))
    (present : cell.da b.Y) (lock : (declOf u).Lock) :
    cell.adr b.Y + cell.bytes ≤ b.Y.lk lock := by
  have boundary : cell.adr b.Y + cell.bytes ≤ b.Y.hi := by
    cases cell with
    | glob g => exact (storage.2.1 g).2
    | elem t f k => exact (storage.1 t f k present).2
  have := (locks.1 lock).1
  omega

/-- Single-payload attachment contract used by the source emitter: loaded startup,
    canonical source world and free locks all follow from the same actual bytes. -/
theorem Bild.initializedBytes_loaded {u : UProg} (valid : GabbroV.sp0OkB u = true)
    (b : Bild (declOf u)) (layout : InitialLayout u b.Y) {stacks : List Runner.B}
    (made : startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stacks)
    (rootCount : b.rootArgs.length = b.roots.length)
    (codeEnd : b.fp0 = codeBase + 16 * b.code.length)
    (separate : b.fp0 + 8 * (b.Ks * (b.roots.length + 1)) ≤ b.Y.lo)
    (ordered : b.Y.hi ≤ b.Y.sye) (inside : b.Y.sye ≤ b.fp0 + 8 * b.K)
    {m : Runner.Mem} (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) :
    BytesAt m Runner.Prog.IMG (Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 b.baseReq) ∧
    BytesAt m codeBase (b.code.flatMap encII ++ stacks) ∧
    WeltAt m b.Y (initialWorld u valid) ∧
    BytesAt m b.Y.hi (List.replicate (b.Y.sye - b.Y.hi) 0) := by
  have extent := layout.extent
  have room : b.Ks * (b.roots.length + 1) ≤ b.K := by omega
  have imageLength := b.bytes_length_of_stacks made rootCount codeEnd room
  have base : Runner.Prog.IMG ≤ b.fp0 := by simp only [codeEnd, codeBase]; omega
  have lower : Runner.Prog.IMG ≤ b.Y.lo := by omega
  have upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length := by omega
  obtain ⟨header, startup⟩ := b.initializedBytes_startup valid layout made rootCount codeEnd separate upper loaded
  exact ⟨header, startup, b.initializedBytes_world valid layout lower upper loaded,
    b.initializedBytes_locks valid layout made rootCount codeEnd separate ordered inside loaded⟩

end Gabbro.Stage0.Senke
