module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Longer than every local name, including names introduced by fold expansion. -/
def returnCallBinder (ctx : UCtx) : String :=
  String.ofList (List.replicate ((ctx.names.map String.length).foldr max 0 + 1) '#')

private theorem name_length_le (names : List String) (name : String) (member : name ∈ names) :
    name.length ≤ (names.map String.length).foldr max 0 := by
  induction names with
  | nil => cases member
  | cons head rest ih =>
    change name.length ≤ max head.length ((rest.map String.length).foldr max 0)
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem returnCallBinder_fresh (ctx : UCtx) : returnCallBinder ctx ∉ ctx.names := by
  intro member
  have bound := name_length_le ctx.names (returnCallBinder ctx) member
  have length : (returnCallBinder ctx).length =
      (ctx.names.map String.length).foldr max 0 + 1 := by
    simp only [returnCallBinder, String.length_ofList, List.length_replicate]
  rw [length] at bound
  omega

/-- Keep every successful direct return unchanged. A remaining call of a declared
    function uses the existing checked binder, then returns its actual bound value.
    The binder retains the callee's result type and all argument/channel checks. -/
def expandReturnCall (ctx : UCtx) (heads : List UFnKopf) (ending : Option SEnde) :
    Except String (List UStmt × UCtx × Option SEnde) :=
  match uEnde ctx ending with
  | .ok _ => .ok ([], ctx, ending)
  | .error _ =>
    match ending with
    | some (.ret (some call@(.call name _))) =>
      if heads.any (fun head => strEq head.name name) then do
        let fresh := returnCallBinder ctx
        let (statement, after) ← uBindWert ctx ctx.tabs heads false fresh none call
        pure ([statement], foldBindingContext ctx after statement,
          some (.ret (some (.variable fresh))))
      else .ok ([], ctx, ending)
    | _ => .ok ([], ctx, ending)

/-- Existing inverse certificates supply this equality from their actual end reader;
    the ANF step adds no hypothesis to the source roundtrip theorem. -/
theorem expandReturnCall_of_ok (ctx : UCtx) (heads : List UFnKopf) (ending : Option SEnde)
    (result : URet) (success : uEnde ctx ending = .ok result) :
    expandReturnCall ctx heads ending = .ok ([], ctx, ending) := by
  simp only [expandReturnCall, success]

end Gabbro.Grammatik.Parser.Uebersetze
