module
public import Bruecke.Anweisung.Match.Lesen
public import Bruecke.Anweisung.Zweig.Vorrat
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem reasonArmsZ_succ {k n offset : Nat} {fn : UFn} {ns : BodyNames}
    {ss tail : List UStmt} {arms : List (String × List Gabbro.Body.Stmt)} {used : List String}
    (h : reasonArmsZ u k fn (n + 1) offset ns ss = some (arms, tail, used)) :
    ∃ body remaining allocated, seqZ u k fn ns ss = some (body, remaining, allocated) ∧
      ((n = 0 ∧ arms = [(caseLabel offset, body)] ∧ remaining = tail ∧ allocated = used) ∨
       ∃ m rest restArms, n = m + 1 ∧ remaining = .ifElse :: rest ∧
         reasonArmsZ u k fn (m + 1) (offset + 1) (ns.resume allocated) rest =
           some (restArms, tail, used) ∧ arms = (caseLabel offset, body) :: restArms) := by
  rw [reasonArmsZ] at h
  cases hb : seqZ u k fn ns ss with
  | none => simp only [hb, bind, Option.bind_none] at h <;> cases h
  | some out =>
    obtain ⟨body, remaining, allocated⟩ := out
    simp only [hb, bind, Option.bind_some] at h
    refine ⟨body, remaining, allocated, (by first | exact hb | rfl), ?_⟩
    cases n with
    | zero =>
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      exact .inl ⟨rfl, h.1.symm, h.2.1, h.2.2⟩
    | succ m =>
      cases remaining with
      | nil => cases h
      | cons marker rest =>
        cases marker <;> try { cases h }
        case ifElse =>
          cases ha : reasonArmsZ u k fn (m + 1) (offset + 1) (ns.resume allocated) rest with
          | none => simp only [ha, bind, Option.bind_none] at h <;> cases h
          | some out =>
            obtain ⟨restArms, tail', used'⟩ := out
            simp only [ha, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .inr ⟨m, rest, restArms, rfl, rfl, ha, rfl⟩

theorem stmtsBodyZ_reason_some {k : Nat} {fn : UFn} {ns : BodyNames} {x : String}
    {ss : List UStmt} {r : URet} {bs : List Gabbro.Body.Stmt}
    (h : stmtsBodyZ u (k + 1) fn ns (.matchWhyBeg x :: ss) r = some bs) :
    ∃ count e arms tail allocated ys, reasonSubject fn ns x = some (count, e) ∧
      reasonArmsZ u k fn count 0 ns ss = some (arms, .blkEnd :: tail, allocated) ∧
      stmtsBodyZ u k fn (ns.resume allocated) tail r = some ys ∧ bs = .onReason e arms :: ys := by
  simp only [stmtsBodyZ] at h
  cases he : reasonSubject fn ns x with
  | none => simp only [he, bind, Option.bind_none] at h <;> cases h
  | some pair =>
    obtain ⟨count, e⟩ := pair
    simp only [he, bind, Option.bind_some] at h
    cases ha : reasonArmsZ u k fn count 0 ns ss with
    | none => simp only [ha, bind, Option.bind_none] at h <;> cases h
    | some out =>
      obtain ⟨arms, ending, allocated⟩ := out
      simp only [ha, bind, Option.bind_some] at h
      cases ending with
      | nil => cases h
      | cons marker tail =>
        cases marker <;> try { cases h }
        case blkEnd =>
          cases hy : stmtsBodyZ u k fn (ns.resume allocated) tail r with
          | none => simp only [hy, bind, Option.bind_none] at h <;> cases h
          | some ys =>
            simp only [hy, bind, Option.bind_some, pure, Option.some.injEq] at h
            exact ⟨count, e, arms, tail, allocated, ys,
              (by first | exact he | rfl), ha, hy, h.symm⟩

/-- The subject carries the actual canonical position and exact reason count. -/
theorem reasonSubject_some {fn : UFn} {ns : BodyNames} {x : String} {count : Nat}
    {e : Gabbro.Body.Expr} (h : reasonSubject fn ns x = some (count, e)) :
    ∃ id, valueParamTy fn x = some (.why count) ∧ ns.lookup fn x = some id ∧ e = .name id := by
  simp only [reasonSubject, bind, Option.bind] at h
  cases ht : valueParamTy fn x with
  | none => simp only [ht] at h <;> cases h
  | some ty =>
    simp only [ht] at h
    cases ty <;> try { cases h }
    case why n =>
      cases hi : ns.lookup fn x with
      | none => simp only [hi] at h <;> cases h
      | some id =>
        simp only [hi, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨id, (by first | exact ht | rfl), (by first | exact hi | rfl), rfl⟩

theorem reasonArmsZ_used (k : Nat) (fn : UFn) : ∀ count offset ns ss arms tail used,
    reasonArmsZ u k fn count offset ns ss = some (arms, tail, used) →
      ∀ x ∈ ns.used, x ∈ used
  | 0, _, _, _, _, _, _, h => by cases h; exact fun _ hx => hx
  | count + 1, offset, ns, ss, arms, tail, used, h => by
    obtain ⟨body, remaining, allocated, hb, hc⟩ := reasonArmsZ_succ h
    have hUsed := seqZ_used k fn ns ss body remaining allocated hb
    rcases hc with ⟨_, _, _, rfl⟩ | ⟨m, rest, restArms, rfl, _, hr, _⟩
    · exact hUsed
    · exact fun x hx => reasonArmsZ_used k fn (m + 1) (offset + 1) (ns.resume allocated)
        rest restArms tail used hr x (hUsed x hx)

end Gabbro.Bruecke
