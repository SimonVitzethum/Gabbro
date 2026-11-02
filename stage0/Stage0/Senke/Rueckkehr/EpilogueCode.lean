/- One normal-return epilogue: ensures, then the owed predicates in declaration order. -/
module
public import Stage0.Senke.Ausdruck.Old.Code
public import Stage0.Senke.Stopp
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- The same read phase as `rufAt`, including every owed carrier's guards. -/
def owedWorld (P : Programm D) (f : D.Fn) (σ : World D) : World D :=
  (D.invs.filter (schuldet f)).foldl
    (fun σ i => σ.lese (invSicht D i) (P.invariante i).orte) σ

def owedFailure (P : Programm D) (f : D.Fn) (σ : World D) : Option D.Inv :=
  D.invs.find? (fun i => schuldet f i && !wahr? (eval σ (P.invariante i) σ .nil))

/-- Zero denotes successful restoration; reasons never enter this normal-return phase. -/
def returnFault (P : Programm D) (f : D.Fn) (σ0 σ : World D)
    (ρ : Env D (D.params f)) (v : ErgVal D (D.erg f)) : Nat :=
  let post := σ.lese (vertragVon D f).ende (P.ensures f).orte
  if wahr? (eval σ0 (P.ensures f) post (ergEnv (D.erg f) v ρ)) = false then 102
  else if (owedFailure P f (owedWorld P f post)).isSome then 103 else 0

/-- Predicates share one scratch suffix; their result never overlaps the saved return value. -/
def lowInvs (L : Lay D) (P : Programm D) (f : D.Fn) (d : Nat) :
    List D.Inv → Option (List II × Nat)
  | [] => some ([], d + 8)
  | i :: rest =>
    if schuldet f i then do
      let predicate ← lowE L (P.invariante i) d
      let tail ← lowInvs L P f d rest
      pure (predicate.1 ++ (guardC d 103 d ++ tail.1), max predicate.2 tail.2)
    else lowInvs L P f d rest

/-- The shared stop request always has eight scratch words, including an empty suffix. -/
theorem lowInvs_scratch (L : Lay D) (P : Programm D) (f : D.Fn) (d : Nat) :
    ∀ is code top, lowInvs L P f d is = some (code, top) → d + 8 ≤ top := by
  intro is
  induction is with
  | nil => intro code top h; simp [lowInvs] at h; omega
  | cons i is ih =>
    intro code top h
    simp only [lowInvs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨_, _⟩, _, ⟨cc, tt⟩, ht, _, rfl⟩ := h
      have := ih cc tt ht
      omega
    · exact ih code top h

/-- The whole checked epilogue is passed through every block to its normal returns. -/
def lowPost (L : Lay D) (layout : FrameLayout) (P : Programm D) (f : D.Fn)
    (d : Nat) : Option (List II × Nat) := do
  let post ← lowEns L layout (P.ensures f) d
  let invariants ← lowInvs L P f d D.invs
  pure (post.1 ++ (guardC d 102 d ++ invariants.1), max post.2 invariants.2)

end Gabbro.Stage0.Senke
