module
public import Bruecke.Anweisung.Schleife.Lesen
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

theorem lowStruct_loop_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ Λ' : List (Res (declOf u))} {x tab : String} {ss tail : List UStmt}
    {st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowStructL (l := loopMode) u c Γ fn (n + 1) Λ [] (.loopBeg x tab .tru) ss =
      .ok (⟨Λ', st⟩, tail)) :
    ∃ t, ∃ (body : Block (declOf u) (verOf u c) true (.index ((declOf u).count t) :: Γ) Λ Λ),
      tabIdx u.tabs tab = .ok t ∧
      lowSeqL (l := true) u c (.index ((declOf u).count t) :: Γ)
        (fn.mitIndex x t.val ((declOf u).count t)) n Λ [] ss = .ok (⟨Λ, body⟩, .blkEnd :: tail) ∧
      Λ' = Λ ∧ HEq st (Stmt.traverse (l := loopMode) t Expr.tru body) := by
  rw [lowStructL_succ] at h
  simp only [lowStructStep] at h
  cases ht : tabIdx u.tabs tab with
  | error e => simp only [ht, Except.bind] at h <;> cases h
  | ok t =>
    simp only [ht, Except.bind, lowEns, lowStufe_seq] at h
    split at h
    · cases h
    · rename_i out body rest hb
      split at h
      · rename_i heq
        subst out
        cases h
        exact ⟨t, body, (by first | exact ht | rfl), hb, rfl, HEq.rfl⟩
      · cases h
    · cases h

theorem lowSeq_loop_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {x tab : String} {ss rest : List UStmt}
    {p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ [] (.loopBeg x tab .tru :: ss) = .ok (p, rest)) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ₁) (tail : List UStmt)
      (q : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ₁ Λ'),
      lowStructL (l := loopMode) u c Γ fn n Λ [] (.loopBeg x tab .tru) ss = .ok (⟨Λ₁, st⟩, tail) ∧
      lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail = .ok (q, rest) ∧ p = ⟨q.1, .cons st q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_struct, lowStufe_seq] at h
  cases hs : lowStructL (l := loopMode) u c Γ fn n Λ [] (.loopBeg x tab .tru) ss with
  | error e => simp only [hs, Except.bind] at h <;> cases h
  | ok pair =>
    obtain ⟨⟨Λ₁, st⟩, tail⟩ := pair
    simp only [hs, Except.bind] at h
    cases hq : lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail with
    | error e => simp only [hq, Except.bind] at h <;> cases h
    | ok pair =>
      obtain ⟨q, rest'⟩ := pair
      simp only [hq, Except.bind] at h
      cases h
      exact ⟨Λ₁, st, tail, q, (by first | exact hs | rfl), hq, rfl⟩

theorem lowBodyF_loop_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x tab : String} {ss : List UStmt} {r : URet}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.loopBeg x tab .tru :: ss) r = .ok b0) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁) (tail : List UStmt)
      (rest : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL (l := false) u c Γ fn blockFuel Λ [] (.loopBeg x tab .tru) ss = .ok (⟨Λ₁, st⟩, tail) ∧
      lowBodyF u c Γ fn n Λ₁ tail r = .ok rest ∧ b0 = .cons st rest := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i Λ₁ st tail hs
    split at h
    · cases h
    · rename_i rest hr
      cases h
      exact ⟨Λ₁, st, tail, rest, hs, hr, rfl⟩

/-- The finite write fragment consumes exactly its first closing marker. -/
theorem loopWrites_rest {loopMode : Bool} : ∀ n k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
    {Λ Λ' : List (Res (declOf u))} (block : Block (declOf u) (verOf u c) loopMode Γ Λ Λ')
    (tail tailZ : List UStmt) (bs : List Gabbro.Body.Stmt) (used : List String),
    loopWritesB ss = true →
    lowSeqL (l := loopMode) u c Γ fn n Λ [] ss = .ok (⟨Λ', block⟩, .blkEnd :: tail) →
    seqZ u k ft ns ss = some (bs, .blkEnd :: tailZ, used) → tail = tailZ ∧ tail <:+ ss
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ + 1, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | _ + 1, _ + 1, [], _, _, _, _, _, _, _, _, _, _, _, hg, _, _ => by cases hg
  | n + 1, k + 1, st :: ss, Γ, fn, ft, ns, Λ, Λ', block, tail, tailZ, bs, used, hg, hG, hB => by
    cases st
    case blkEnd =>
      rw [lowSeq_blkEnd] at hG
      cases hG
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨_, heq, _⟩ := hB
      cases heq
      exact ⟨rfl, List.suffix_cons _ _⟩
    case assign | assignTab | assignGlob | setVar | setVarB =>
      obtain ⟨b, ft', ns', ys, hb, hy, _⟩ := seqZ_schritt_some hB (by exact True.intro)
      obtain ⟨_, hft, hns⟩ := schrittB_einzeln_sicht (Sicht.refl ft) hb (by exact True.intro)
      subst ft'
      subst ns'
      obtain ⟨Λ₁, gs, q, _, hq, _⟩ := lowSeq_einzeln_ok hG (by exact True.intro)
      have ih := loopWrites_rest n k ss fn ft ns q.2 tail tailZ ys used hg hq hy
      exact ⟨ih.1, ih.2.trans (List.suffix_cons _ _)⟩
    all_goals cases hg

end Gabbro.Bruecke
