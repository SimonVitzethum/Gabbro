/-
  Gabbro/Grammatik/SonstLeaveZeuge.lean

  **Witness: a `leave` in an `else` branch reaches the loop** (SATZKARTE
  §13.5 item 4, closed in §15.3).

  Before 2026-09-13, machine G replaced the whole residue by the `else`
  block of `narrow`/`pruefung`/float narrowing/register read (and by the
  reason block of `let … else`). A `leave`/`next` in that block then stood
  as `.ende (.leave _)` with the loop's continuation gone, and no rule of G
  fires on such a head (`ende_leave_steht`): the frame could never return,
  while the sequential semantics leaves the loop and goes on.

  Now the `else` block runs in BLOCK position in front of the layer
  `GRest.abbruch k`, and `peelAbbruchLeave`/`peelAbbruchNext` hand the exit
  to `k`. The fixture:

      fn true():  retry 1 until false { if !false { leave } }; return 7

  (`pruefung falsch { leave }` is the named refusal `if !c { … }`). The
  sequential semantics returns `7` (`sv_exec`). The machine, by steps of
  thread 0 alone (`sonst_leave_zeuge`): unfolds the `retry`, starts the
  one pass, takes the `else` branch of the refusal -- the residue is now
  `leave` over `abbruch` over the loop shim `wiederRest`, the loop
  continuation KEPT -- peels the `abbruch` layer, leaves the loop, closes
  the empty block and returns, logging exactly that `7`.
-/
import Grammatik.RufAdaequatRufG

namespace Gabbro.Grammatik

/-- The loop body: `if !false { leave }` (the refusal `pruefung`). -/
def svBody : Block adD (vertragVon adD adFn) true [] [] [] :=
  .pruefung .falsch (.leave rfl) .nil

/-- `retry 1 until false { svBody }` with an empty overflow block. -/
def svRetry : Stmt adD (vertragVon adD adFn) false [] [] [] :=
  .retry 1 .falsch svBody .nil

/-- The statement after the loop. -/
def svRet : Endblock adD (vertragVon adD adFn) false [] [] :=
  .ret (.wert adSieben) List.Perm.nil

/-- The body: the loop, then `return 7`. -/
def svRumpf : Endblock adD (vertragVon adD adFn) false [] [] :=
  .cons svRetry svRet

def svP : Programm adD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | true => svRumpf
    | false => adCallerRumpf

/-- Every thread: the witness frame above the (non-waiting) caller. -/
def svFaden : RufFadenG adD :=
  ⟨[adCaller], ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], [], Env.nil, .ende svRumpf⟩⟩,
    [], []⟩

def svM : RufMaschineG adD := ⟨adSp0, fun _ => svFaden, [], adSp0.welt []⟩

/-- The sequential semantics leaves the loop by the `else` branch's
    `leave` and returns `7`. -/
theorem sv_exec : ∃ (σ' : World adD) (v : ErgVal adD (vertragVon adD adFn).erg),
    execEnd adO 0 keinRuf svRumpf (svM.weltVon 0) Env.nil = .zurueck σ' v ∧
    (show Zahl 0 100 from v).n = 7 :=
  ⟨_, _, rfl, rfl⟩

/-- Is the residue of a frame a bare `leave` end block? -/
def istEndeLeave {V : Vertrag D} :
    (Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) → Bool
  | ⟨_, _, _, _, .ende (.leave _)⟩ => true
  | _ => false

/-- **The old target was a dead end.** No rule of G fires on a head
    `.ende (.leave h)` -- what the `else` step produced before 2026-09-13. -/
theorem ende_leave_steht {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (h : true = true)
    (hR : (M.faeden f).kopf.rest =
      ⟨true, Γ, Λ, ρ, .ende (.leave h : Endblock D (vertragVon D (M.faeden f).kopf.f) true Γ Λ)⟩) :
    ¬ RufSchrittG P O passes M f M' := by
  intro hs
  have hk : istEndeLeave (M.faeden f).kopf.rest = true := by rw [hR]; rfl
  clear hR
  cases hs <;> simp_all [istEndeLeave]

/-- The pre-repair state: the frame reduced to the bare `leave`. -/
def svAltM : RufMaschineG adD :=
  ⟨adSp0, fun _ => ⟨[adCaller], ⟨adFn, Env.nil, adSp0.welt [],
    ⟨true, [], [], Env.nil, .ende (.leave rfl)⟩⟩, [], []⟩, [], adSp0.welt []⟩

/-- **Witness for `ende_leave_steht`**: the premise holds on the state the
    old `else` step reached on this fixture, and thread 0 has no step
    there -- it can never log the `7` the sequential semantics returns. -/
theorem ende_leave_steht_zeuge : ∀ M' : RufMaschineG adD, ¬ RufSchrittG svP adO 0 svAltM 0 M' :=
  fun _ => ende_leave_steht (M := svAltM) rfl rfl

/-- **Witness for the `else`-`leave` repair.** The machine runs the
    fixture to the loop exit inside the `else` branch with the loop
    continuation kept (`M4`, head `leave` over `abbruch` over the loop
    shim), and on to the return, logging the value `7` the sequential
    semantics returns. -/
theorem sonst_leave_zeuge :
    ∃ (M4 M' : RufMaschineG adD) (σ' : World adD) (v : ErgVal adD (adD.erg adFn)),
      RufLaufG svP adO 0 0 svM M4 ∧
      (∃ sp lg, M4.faeden 0 = ⟨[adCaller], ⟨adFn, Env.nil, adSp0.welt [],
        ⟨true, [], [], Env.nil, .dann (.cons (.leave rfl) .nil)
          (.abbruch (.wiederRest 0 .falsch svBody .nil (.dann .nil (.ende svRet))))⟩⟩, sp, lg⟩) ∧
      RufLaufG svP adO 0 0 M4 M' ∧
      M'.faeden 0 = ⟨[], adCaller, σ'.spur,
        [RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) σ']⟩ ∧
      (show Zahl 0 100 from v).n = 7 ∧
      ∃ σ'' : World adD,
        execEnd adO 0 keinRuf svRumpf (svM.weltVon 0) Env.nil = .zurueck σ'' v := by
  have h0 : svM.faeden 0 = svFaden := rfl
  -- unfold the `retry` in end position
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := svP) (O := adO) (passes := 0) h0 svRetry svRet
    .nil rfl rfl
  have e1 := hZ1.1
  try dsimp only at e1
  obtain ⟨M2, s2, hZ2⟩ := w_dannRetry (P := svP) (O := adO) (passes := 0) e1 1 .falsch svBody
    .nil .nil (.ende svRet) .nil rfl
  have e2 := hZ2.1
  try dsimp only at e2
  -- the bound is false: one pass of the body
  obtain ⟨M3, s3, hZ3⟩ := w_wiederSchritt (P := svP) (O := adO) (passes := 0) e2 0 .falsch svBody
    .nil (.dann .nil (.ende svRet)) .nil rfl rfl (fun _ h => absurd h List.not_mem_nil)
  have e3 := hZ3.1
  try dsimp only at e3
  -- the refusal fails: its `else` block runs in block position over `abbruch`
  obtain ⟨M4, s4, hZ4⟩ := w_pruefFalsch (P := svP) (O := adO) (passes := 0) e3 .falsch
    (.leave rfl) .nil (.wiederRest 0 .falsch svBody .nil (.dann .nil (.ende svRet))) .nil rfl rfl
    (fun _ h => absurd h List.not_mem_nil)
  have e4 := hZ4.1
  try dsimp only at e4
  -- the `leave` reaches the loop shim
  obtain ⟨M5, s5, hZ5⟩ := w_peelAbbruch (P := svP) (O := adO) (passes := 0) e4 true .nil
    (.wiederRest 0 .falsch svBody .nil (.dann .nil (.ende svRet))) .nil rfl
  have e5 := hZ5.1
  try dsimp only at e5
  obtain ⟨M6, s6, hZ6⟩ := w_abbWieder (P := svP) (O := adO) (passes := 0) e5 true 0 .falsch
    svBody .nil (.dann .nil (.ende svRet)) .nil .nil rfl (fun _ h => absurd h List.not_mem_nil)
  have e6 := hZ6.1
  try dsimp only at e6
  obtain ⟨M7, s7, hZ7⟩ := w_dannLeer (P := svP) (O := adO) (passes := 0) e6 (.ende svRet) .nil rfl
  have e7 := hZ7.1
  try dsimp only at e7
  -- the statement after the loop: `return 7`
  obtain ⟨M8, s8, hG8⟩ := w_rueckP (P := svP) (O := adO) (passes := 0) e7 _ _ rfl
    (PopArt.wie rfl) (.wert adSieben) List.Perm.nil _ rfl (fun _ h => absurd h List.not_mem_nil)
  refine ⟨M4, M8, _, _,
    RufLaufG.schritt s1 (RufLaufG.schritt s2 (RufLaufG.schritt s3 (RufLaufG.einzeln s4))),
    ⟨_, _, e4⟩, RufLaufG.schritt s5 (RufLaufG.schritt s6 (RufLaufG.schritt s7
      (RufLaufG.einzeln s8))), hG8.1, rfl, _, rfl⟩

/-! ## CUTS:

  What is proved: on a non-degenerate fixture (a `retry` loop whose body
  leaves through the `else` branch of a refusal, and a `return 7` after the
  loop), G keeps the loop continuation under the `else` branch (`M4`) and
  returns the value the sequential semantics returns (`sonst_leave_zeuge`,
  `sv_exec`); the pre-repair target `.ende (.leave _)` has no step
  (`ende_leave_steht`).

  What is NOT covered: the general agreement for `else` branches INSIDE a
  loop. The adequacy fragments (`BlockG`/`BlockR` in RufAdaequatG/
  RufAdaequatRufG and the converse) admit the `else` forms only at loop
  level `false` (`narrow_inv … l = false`), where no `leave`/`next` can
  occur; the repair is certified there by the carried adequacy theorems
  and inside loops by this witness only. -/

#print axioms Gabbro.Grammatik.sv_exec
#print axioms Gabbro.Grammatik.ende_leave_steht
#print axioms Gabbro.Grammatik.ende_leave_steht_zeuge
#print axioms Gabbro.Grammatik.sonst_leave_zeuge

end Gabbro.Grammatik
