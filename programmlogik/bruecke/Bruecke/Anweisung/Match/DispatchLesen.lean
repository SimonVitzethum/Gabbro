module
public import Bruecke.Anweisung.Match.Lesen
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

theorem readReasonArms_succ
    {read : BodyNames → List UStmt → Option (List Gabbro.Body.Stmt × List UStmt × List String)}
    {n offset : Nat} {ns : BodyNames}
    {ss tail : List UStmt} {arms : List (String × List Gabbro.Body.Stmt)} {used : List String}
    (h : readReasonArms read (n + 1) offset ns ss = some (arms, tail, used)) :
    ∃ body remaining allocated, read ns ss = some (body, remaining, allocated) ∧
      ((n = 0 ∧ arms = [(caseLabel offset, body)] ∧ remaining = tail ∧ allocated = used) ∨
       ∃ m rest restArms, n = m + 1 ∧ remaining = .ifElse :: rest ∧
         readReasonArms read (m + 1) (offset + 1) (ns.resume allocated) rest =
           some (restArms, tail, used) ∧ arms = (caseLabel offset, body) :: restArms) := by
  rw [readReasonArms] at h
  cases hb : read ns ss with
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
          cases ha : readReasonArms read (m + 1) (offset + 1) (ns.resume allocated) rest with
          | none => simp only [ha, bind, Option.bind_none] at h <;> cases h
          | some out =>
            obtain ⟨restArms, tail', used'⟩ := out
            simp only [ha, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .inr ⟨m, rest, restArms, rfl, rfl, ha, rfl⟩

theorem reasonArmsZ_succ {k n offset : Nat} {fn : UFn} {ns : BodyNames}
    {ss tail : List UStmt} {arms : List (String × List Gabbro.Body.Stmt)} {used : List String}
    (h : reasonArmsZ u k fn (n + 1) offset ns ss = some (arms, tail, used)) :
    ∃ body remaining allocated, seqZ u k fn ns ss = some (body, remaining, allocated) ∧
      ((n = 0 ∧ arms = [(caseLabel offset, body)] ∧ remaining = tail ∧ allocated = used) ∨
       ∃ m rest restArms, n = m + 1 ∧ remaining = .ifElse :: rest ∧
         reasonArmsZ u k fn (m + 1) (offset + 1) (ns.resume allocated) rest =
           some (restArms, tail, used) ∧ arms = (caseLabel offset, body) :: restArms) :=
  readReasonArms_succ h

/-- A finite dispatch preserves every identifier retained by its block reader. -/
theorem readReasonArms_used
    {read : BodyNames → List UStmt → Option (List Gabbro.Body.Stmt × List UStmt × List String)}
    (hread : ∀ ns ss bs tail used, read ns ss = some (bs, tail, used) →
      ∀ x ∈ ns.used, x ∈ used) :
    ∀ count offset ns ss arms tail used,
      readReasonArms read count offset ns ss = some (arms, tail, used) →
        ∀ x ∈ ns.used, x ∈ used
  | 0, _, _, _, _, _, _, h => by cases h; exact fun _ hx => hx
  | count + 1, offset, ns, ss, arms, tail, used, h => by
    obtain ⟨body, remaining, allocated, hb, hc⟩ := readReasonArms_succ h
    have hUsed := hread ns ss body remaining allocated hb
    rcases hc with ⟨_, _, _, rfl⟩ | ⟨m, rest, restArms, rfl, _, hr, _⟩
    · exact hUsed
    · exact fun x hx => readReasonArms_used hread (m + 1) (offset + 1) (ns.resume allocated)
        rest restArms tail used hr x (hUsed x hx)

theorem seqZ_reason_some {k : Nat} {fn : UFn} {ns : BodyNames} {x : String}
    {ss tailZ : List UStmt} {used : List String} {bs : List Gabbro.Body.Stmt}
    (h : seqZ u (k + 1) fn ns (.matchWhyBeg x :: ss) = some (bs, tailZ, used)) :
    ∃ count e arms tail allocated ys, reasonSubject fn ns x = some (count, e) ∧
      reasonArmsZ u k fn count 0 ns ss = some (arms, .blkEnd :: tail, allocated) ∧
      seqZ u k fn (ns.resume allocated) tail = some (ys, tailZ, used) ∧ bs = .onReason e arms :: ys := by
  change (do
    let (count, e) ← reasonSubject fn ns x
    let (arms, .blkEnd :: tail, allocated) ← reasonArmsZ u k fn count 0 ns ss | none
    let p ← seqZ u k fn (ns.resume allocated) tail
    pure (.onReason e arms :: p.1, p.2.1, p.2.2)) = some (bs, tailZ, used) at h
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
          cases hy : seqZ u k fn (ns.resume allocated) tail with
          | none => simp only [hy, bind, Option.bind_none] at h <;> cases h
          | some out =>
            obtain ⟨ys, tail', used'⟩ := out
            simp only [hy, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨count, e, arms, tail, allocated, ys,
              (by first | exact he | rfl), ha, hy, rfl⟩

theorem seqZ_tag_some {k sidx : Nat} {fn : UFn} {ns : BodyNames} {x : String} {binders : List String}
    {ss tailZ : List UStmt} {used : List String} {bs : List Gabbro.Body.Stmt}
    (h : seqZ u (k + 1) fn ns (.matchTagBeg sidx x binders :: ss) = some (bs, tailZ, used)) :
    ∃ cs e arms tail allocated ys, sidx < u.sums.length ∧ tagSubject fn ns x = some (cs, e) ∧
      reasonArmsZ u k fn cs.length 0 ns ss = some (arms, .blkEnd :: tail, allocated) ∧
      seqZ u k fn (ns.resume allocated) tail = some (ys, tailZ, used) ∧ bs = .onTag e (tagArms arms) :: ys := by
  by_cases hn : sidx < u.sums.length
  · change (if sidx < u.sums.length then (do
      let (cs, e) ← tagSubject fn ns x
      let (arms, .blkEnd :: tail, allocated) ← reasonArmsZ u k fn cs.length 0 ns ss | none
      let p ← seqZ u k fn (ns.resume allocated) tail
      pure (.onTag e (tagArms arms) :: p.1, p.2.1, p.2.2)) else none) = some (bs, tailZ, used) at h
    rw [if_pos hn] at h
    cases he : tagSubject fn ns x with
    | none => simp only [he, bind, Option.bind_none] at h; cases h
    | some pair =>
      obtain ⟨cs, e⟩ := pair
      simp only [he, bind, Option.bind_some] at h
      cases ha : reasonArmsZ u k fn cs.length 0 ns ss with
      | none => simp only [ha, bind, Option.bind_none] at h; cases h
      | some out =>
        obtain ⟨arms, ending, allocated⟩ := out
        simp only [ha, bind, Option.bind_some] at h
        cases ending with
        | nil => cases h
        | cons marker tail =>
          cases marker <;> try { cases h }
          case blkEnd =>
            cases hy : seqZ u k fn (ns.resume allocated) tail with
            | none => simp only [hy, bind, Option.bind_none] at h; cases h
            | some out =>
              obtain ⟨ys, tail', used'⟩ := out
              simp only [hy, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨cs, e, arms, tail, allocated, ys, hn,
                (by first | exact he | rfl), ha, hy, rfl⟩
  · simp only [seqZ, hn, ↓reduceIte] at h; cases h

end Gabbro.Bruecke
