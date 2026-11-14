module
public import Bruecke.Anweisung.Zweig.Lesen
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

/-- A terminal conditional has no continuation or implicit empty return. Its arms use
    the ordinary scoped reader, including the shared allocation history. -/
theorem stmtsBodyZ_ifEnde_some {k : Nat} {fn : UFn} {ns : BodyNames} {cnd : UEns}
    {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.ifEnde cnd :: ss) r = some bs) :
    ∃ ce t e rest1 used1 used2, r = .keins ∧ condZ u fn ns cnd = some ce ∧
      seqZ u k fn ns ss = some (t, .ifElse :: rest1, used1) ∧
      seqZ u k fn (ns.resume used1) rest1 = some (e, [.blkEnd], used2) ∧
      bs = [.ite ce t e] := by
  cases r <;> try { simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody,
    Option.map_none, reduceCtorEq] at h }
  case keins =>
    simp only [stmtsBodyZ] at h
    cases hce : condZ u fn ns cnd with
    | none => simp only [hce, bind, Option.bind_none] at h; cases h
    | some ce =>
      simp only [hce, bind, Option.bind_some] at h
      cases ht : seqZ u k fn ns ss with
      | none => simp only [ht, bind, Option.bind_none] at h; cases h
      | some pair =>
        obtain ⟨t, ending, used1⟩ := pair
        simp only [ht, bind, Option.bind_some] at h
        cases ending with
        | nil => cases h
        | cons marker rest1 =>
          cases marker <;> try { cases h }
          case ifElse =>
            cases he : seqZ u k fn (ns.resume used1) rest1 with
            | none => simp only [he, bind, Option.bind_none] at h; cases h
            | some pair =>
              obtain ⟨e, closing, used2⟩ := pair
              simp only [he, bind, Option.bind_some] at h
              cases closing with
              | nil => cases h
              | cons marker tail =>
                cases marker <;> try { cases h }
                case blkEnd =>
                  cases tail with
                  | cons st tail => cases h
                  | nil =>
                    simp only [pure, Option.some.injEq] at h
                    cases h
                    exact ⟨ce, t, e, rest1, used1, used2, rfl,
                      (by first | exact hce | rfl | simp_all),
                      (by first | exact ht | rfl | simp_all),
                      (by first | exact he | rfl | simp_all), rfl⟩

/-- The canonical whole-function terminal branch is lowered as two explicit endings. -/
theorem lowBodyF_ifEnde_ok {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {cnd : UEns} {ss : List UStmt}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.ifEnde cnd :: ss) .keins = .ok b) :
    ∃ (cv : Expr (declOf u) Γ Λ .bool)
      (t e : Endblock (declOf u) (verOf u c) false Γ Λ) rest1,
      lowEns u Γ Λ fn none cnd = .ok cv ∧
      lowEndL (l := false) u c Γ fn blockFuel Λ [] ss = .ok (t, .ifElse :: rest1) ∧
      lowEndL (l := false) u c Γ fn blockFuel Λ [] rest1 = .ok (e, [.blkEnd]) ∧
      b = .ite cv t e := by
  simp only [lowBodyF] at h
  cases hc : lowEns u Γ Λ fn none cnd with
  | error e => simp only [hc] at h; cases h
  | ok cv =>
    simp only [hc] at h
    cases ht : lowEndL (l := false) u c Γ fn blockFuel Λ [] ss with
    | error e => simp only [ht] at h; cases h
    | ok pair =>
      obtain ⟨t, ending⟩ := pair
      simp only [ht] at h
      cases ending with
      | nil => cases h
      | cons marker rest1 =>
        cases marker <;> try { cases h }
        case ifElse =>
          cases he : lowEndL (l := false) u c Γ fn blockFuel Λ [] rest1 with
          | error e => simp only [he] at h; cases h
          | ok pair =>
            obtain ⟨e, closing⟩ := pair
            simp only [he] at h
            cases closing with
            | nil => cases h
            | cons marker tail =>
              cases marker <;> try { cases h }
              case blkEnd =>
                cases tail with
                | cons st tail => cases h
                | nil =>
                  cases h
                  exact ⟨cv, t, e, rest1,
                    (by first | exact hc | rfl | simp_all),
                    (by first | exact ht | rfl | simp_all),
                    (by first | exact he | rfl | simp_all), rfl⟩

/-- Ending translations stop at the same markers as the nested block reader. -/
def EndMarker : List UStmt → Prop
  | .ifElse :: _ | .blkEnd :: _ => True
  | _ => False

theorem seqZ_marker_some {k : Nat} {fn : UFn} {ns : BodyNames}
    {ss rest : List UStmt} {bs : List Gabbro.Body.Stmt} {used : List String}
    (hm : EndMarker ss) (h : seqZ u k fn ns ss = some (bs, rest, used)) :
    bs = [] ∧ rest = ss ∧ used = ns.used := by
  cases k with
  | zero => cases h
  | succ k =>
    cases ss with
    | nil => cases hm
    | cons st ss =>
      cases st <;> first
        | (simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at h
           exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
        | cases hm

end Gabbro.Bruecke
