module
public import Grammatik.Parser.Elab.UebersetzeAllg.TableCapabilities
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- Successful source space resolution names an actual entry in the same declaration list. -/
theorem uDataSpace_sound (spaces : List String) (name : String) (index : Nat)
    (accepted : uDataSpace spaces name = .ok index) : spaces[index]? = some name := by
  unfold uDataSpace at accepted
  split at accepted
  · rename_i found number lookup
    cases accepted
    have member := List.mem_of_find?_eq_some lookup
    have named := List.find?_some lookup
    have same : found = name := strEq_klingt named
    subst found
    exact List.mem_zipIdx_iff_getElem?.mp member
  · cases accepted

/-- Named normal and nonzero spaces keep their exact registered positions; unknown or absent
    normal spaces are refused. These are witnesses, not an executed measurement. -/
theorem uDataSpace_registered_zeuge :
    uDataSpace ["normal", "custom"] "normal" = .ok 0 ∧
    uDataSpace ["normal", "custom"] "custom" = .ok 1 ∧
    uDataSpace ["normal", "custom"] "unknown" = .error "unknown data space: unknown" ∧
    uDataSpace [] "normal" = .error "unknown data space: normal" := ⟨rfl, rfl, rfl, rfl⟩

/-- Successful sequencing retains every accepted source parameter row. -/
private theorem parameterRows_origin {α β : Type} (produce : α → Except String β)
    {sources : List α} {rows : List β} (accepted : uSeq (sources.map produce) = .ok rows) :
    ∀ row ∈ rows, ∃ source ∈ sources, produce source = .ok row := by
  induction sources generalizing rows with
  | nil =>
    cases accepted
    simp
  | cons source sources ih =>
    cases first : produce source with
    | error error => simp [List.map_cons, uSeq, first] at accepted
    | ok row =>
      cases rest : uSeq (sources.map produce) with
      | error error => simp [List.map_cons, uSeq, first, rest] at accepted
      | ok tail =>
        have same : row :: tail = rows := by
          simpa only [List.map_cons, first, uSeq, rest, Except.ok.injEq] using accepted
        subst rows
        intro output member
        rcases List.mem_cons.mp member with same | member
        · subst output; exact ⟨source, List.mem_cons_self .., first⟩
        · obtain ⟨original, member, produced⟩ := ih rest output member
          exact ⟨original, List.mem_cons_of_mem _ member, produced⟩

/-- The function-head projection keeps every row in order, including its exact pointer type. -/
private theorem parameterRows_coherent (rows : List (String × Ty × UParamArt))
    (coherent : ∀ row ∈ rows, ∀ cap : DataCapTy,
      row.2.2 = .ptr cap → row.2.1 = .ptr cap) :
    ∀ (j : Nat) (cap : DataCapTy),
      (rows.map (fun row : String × Ty × UParamArt => row.2.2))[j]? = some (.ptr cap) →
      (((rows.map (fun row : String × Ty × UParamArt => row.1)).zip
        (rows.map (fun row : String × Ty × UParamArt => row.2.1)))[j]?).map
          (fun row : String × Ty => row.2) = some (Ty.ptr cap) := by
  revert coherent
  induction rows with
  | nil => intro coherent j cap kind; simp at kind
  | cons row rows ih =>
    intro coherent j cap kind
    cases j with
    | zero =>
      have exactType := coherent row (List.mem_cons_self ..) cap (by simpa using kind)
      simpa only [List.map_cons, List.zip_cons_cons, List.getElem?_cons_zero,
        Option.map_some] using congrArg some exactType
    | succ j =>
      exact ih (fun row member => coherent row (List.mem_cons_of_mem _ member)) j cap
        (by simpa using kind)

variable (consts : List (String × Int)) (alias : List (String × (Int × Int)))
    (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (whys : List UWhy)
    (sums : List USum) (devs zeiger : List String) (zb : Nat) (spaces : List String)
    (named : List (String × Ty)) (eigner : List String)

private theorem producedRows_coherent {sources : List (String × STyp)}
    {rows : List (String × Ty × UParamArt)}
    (accepted : uSeq (sources.map (uParam alias tabs sums whys zeiger zb spaces named eigner)) =
      .ok rows) :
    ∀ (j : Nat) (cap : DataCapTy),
      (rows.map (fun row : String × Ty × UParamArt => row.2.2))[j]? = some (.ptr cap) →
      (((rows.map (fun row : String × Ty × UParamArt => row.1)).zip
        (rows.map (fun row : String × Ty × UParamArt => row.2.1)))[j]?).map
          (fun row : String × Ty => row.2) = some (Ty.ptr cap) := by
  apply parameterRows_coherent rows
  intro row member cap kind
  obtain ⟨source, _, produced⟩ := parameterRows_origin _ accepted row member
  exact uParam_pointer_coherent alias tabs sums whys zeiger zb spaces named eigner produced cap kind

/-- A successful canonical head producer retains pointer kinds and types at the same position. -/
theorem elabKopf_pointer_coherent {sig : FnSig} {kopf : UFnKopf} {writes : List String}
    (accepted : elabKopf consts alias tabs locks globs whys sums sig devs zeiger zb spaces named eigner =
      .ok (kopf, writes)) :
    ∀ (j : Nat) (cap : DataCapTy), kopf.kinds[j]? = some (.ptr cap) →
      ((kopf.names.zip kopf.types)[j]?).map
        (fun row : String × Ty => row.2) = some (Ty.ptr cap) := by
  rcases sig with ⟨art, name, params, res, fehler, klauseln, generics⟩
  unfold elabKopf at accepted
  split at accepted
  · cases accepted
  · dsimp only at accepted
    split at accepted
    · cases accepted
    · cases measure : uMeasureClause alias klauseln with
      | error error => simp [measure] at accepted
      | ok decreases =>
        cases clauses : uOhneKlauselForm klauseln with
        | error error => simp [measure, clauses] at accepted
        | ok unit =>
          cases parameters : uSeq ((uOhneGriffe devs params).map
              (uParam alias tabs sums whys zeiger zb spaces named eigner)) with
          | error error => simp [measure, clauses, parameters] at accepted
          | ok rows =>
            simp only [measure, clauses, parameters] at accepted
            have coherent := producedRows_coherent alias tabs whys sums zeiger zb spaces
              named eigner parameters
            cases heldResult : uGehalten locks klauseln with
            | error message => simp [heldResult] at accepted
            | ok held =>
              simp only [heldResult] at accepted
              -- Split the original reason-result dispatcher as a whole.
              split at accepted
              · cases accepted
              ·
                try dsimp only at accepted
                split at accepted
                · cases accepted
                · -- The complete effect result is opaque as well. Only the result
                  -- form below selects record updates, all preserving the rows.
                  try dsimp only at accepted
                  split at accepted
                  · cases accepted; exact coherent
                  · cases accepted; exact coherent
                  · cases accepted; exact coherent
                  · -- An optional index result checks the actual table lookup.
                    split at accepted
                    all_goals cases accepted
                    all_goals exact coherent
                  · -- A named result checks sums, then reasons, then its value type.
                    split at accepted
                    · split at accepted
                      all_goals cases accepted
                      all_goals exact coherent
                    · split at accepted
                      · split at accepted
                        all_goals cases accepted
                        all_goals exact coherent
                      · -- Split only the error/int/other result of uTypIn;
                        -- never descend into its type checker or a returned type.
                        split at accepted
                        all_goals cases accepted
                        all_goals exact coherent
                  · -- Arrays, strings and other surface forms each have exactly
                    -- one opaque value-type or range check at this point.
                    split at accepted
                    all_goals split at accepted
                    all_goals cases accepted
                    all_goals exact coherent

/-- A successful source function satisfies the actual pointer gate; no well-typedness premise
    is added at its consumers. The canonical producer supplies both metadata equalities. -/
theorem elabUFunktion_checkedPointerParam
    (koepfe : List UFnKopf) (sig : FnSig) (body : SAnw) (annahmen : List String)
    (regs : List UReg) (zustaende : List UZustand)
    (specs : List (String × List String × SExpr)) (arrKonst : List (String × USide))
    (specTypen : List (String × List STyp))
    (valueScope : UTypeScope) {fn : UFn}
    (accepted : elabUFunktion consts alias tabs locks globs koepfe sig body annahmen whys sums
      devs regs zustaende zeiger zb specs arrKonst spaces valueScope eigner specTypen = .ok fn)
    (j : Nat) (cap : DataCapTy) (kind : fn.kinds[j]? = some (.ptr cap)) :
    ∃ certificate, checkedPointerParam fn j cap = .ok certificate := by
  unfold elabUFunktion at accepted
  split at accepted
  · cases accepted
  · rename_i kopf writes head
    have coherent := elabKopf_pointer_coherent consts alias tabs locks globs whys sums devs zeiger
      zb spaces valueScope.types eigner head
    cases measure : uMeasureClause alias sig.klauseln with
    | error message =>
      simp only [measure] at accepted
      try dsimp only at accepted
      split at accepted <;> cases accepted
    | ok decreases =>
      simp only [measure] at accepted
      try dsimp only at accepted
      split at accepted
      · cases accepted
      · cases accepted
        exact checkedPointerParam_complete _ j cap kind (coherent j cap kind)

end Gabbro.Grammatik.Parser.UebersetzeAllg
