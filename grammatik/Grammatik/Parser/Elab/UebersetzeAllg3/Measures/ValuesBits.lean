module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Values
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- A bitwise and that lowers keeps an empty footprint. -/
theorem band_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x y s : LowSide u Γ Λ}
    (hx : x.term.orte = []) (hy : y.term.orte = [])
    (h : LowSide.and x y = .ok s) : s.term.orte = [] := by
  unfold LowSide.and at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h0' : 0 ≤ y.range.1
    · rw [dif_pos h0'] at h
      cases h
      change x.term.orte ++ y.term.orte = []
      rw [hx, hy]; rfl
    · rw [dif_neg h0'] at h
      cases h
  · rw [dif_neg h0] at h
    cases h

/-- A lowered bitwise and denotes the source `&&&` on naturals, over either entry world. -/
theorem band_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x y s : LowSide u Γ Λ}
    (h : LowSide.and x y = .ok s) (a b : SExpr)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n)
    (dy : SourceValue fn constants env b (eval entry y.term state env).n) :
    SourceValue fn constants env (.bin "&" a b) (eval entry s.term state env).n := by
  unfold LowSide.and at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h0' : 0 ≤ y.range.1
    · rw [dif_pos h0'] at h
      cases h
      exact SourceValue.band dx dy
    · rw [dif_neg h0'] at h
      cases h
  · rw [dif_neg h0] at h
    cases h

/-- A bitwise or that lowers keeps an empty footprint. -/
theorem bor_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x y s : LowSide u Γ Λ}
    (hx : x.term.orte = []) (hy : y.term.orte = [])
    (h : LowSide.or x y = .ok s) : s.term.orte = [] := by
  unfold LowSide.or at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h0' : 0 ≤ y.range.1
    · rw [dif_pos h0'] at h
      by_cases hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
      · rw [dif_pos hw1] at h
        by_cases hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
        · rw [dif_pos hw2] at h
          cases h
          change x.term.orte ++ y.term.orte = []
          rw [hx, hy]; rfl
        · rw [dif_neg hw2] at h
          cases h
      · rw [dif_neg hw1] at h
        cases h
    · rw [dif_neg h0'] at h
      cases h
  · rw [dif_neg h0] at h
    cases h

/-- A lowered bitwise or denotes the source `|||` on naturals. -/
theorem bor_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x y s : LowSide u Γ Λ}
    (h : LowSide.or x y = .ok s) (a b : SExpr)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n)
    (dy : SourceValue fn constants env b (eval entry y.term state env).n) :
    SourceValue fn constants env (.bin "|" a b) (eval entry s.term state env).n := by
  unfold LowSide.or at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h0' : 0 ≤ y.range.1
    · rw [dif_pos h0'] at h
      by_cases hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
      · rw [dif_pos hw1] at h
        by_cases hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
        · rw [dif_pos hw2] at h
          cases h
          exact SourceValue.bor dx dy
        · rw [dif_neg hw2] at h
          cases h
      · rw [dif_neg hw1] at h
        cases h
    · rw [dif_neg h0'] at h
      cases h
  · rw [dif_neg h0] at h
    cases h

/-- A bitwise xor that lowers keeps an empty footprint. -/
theorem bxor_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x y s : LowSide u Γ Λ}
    (hx : x.term.orte = []) (hy : y.term.orte = [])
    (h : LowSide.xoder x y = .ok s) : s.term.orte = [] := by
  unfold LowSide.xoder at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h0' : 0 ≤ y.range.1
    · rw [dif_pos h0'] at h
      by_cases hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
      · rw [dif_pos hw1] at h
        by_cases hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
        · rw [dif_pos hw2] at h
          cases h
          change x.term.orte ++ y.term.orte = []
          rw [hx, hy]; rfl
        · rw [dif_neg hw2] at h
          cases h
      · rw [dif_neg hw1] at h
        cases h
    · rw [dif_neg h0'] at h
      cases h
  · rw [dif_neg h0] at h
    cases h

/-- A lowered bitwise xor denotes the source `^^^` on naturals. -/
theorem bxor_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x y s : LowSide u Γ Λ}
    (h : LowSide.xoder x y = .ok s) (a b : SExpr)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n)
    (dy : SourceValue fn constants env b (eval entry y.term state env).n) :
    SourceValue fn constants env (.bin "^" a b) (eval entry s.term state env).n := by
  unfold LowSide.xoder at h
  by_cases h0 : 0 ≤ x.range.1
  · rw [dif_pos h0] at h
    by_cases h0' : 0 ≤ y.range.1
    · rw [dif_pos h0'] at h
      by_cases hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
      · rw [dif_pos hw1] at h
        by_cases hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2)
        · rw [dif_pos hw2] at h
          cases h
          exact SourceValue.bxor dx dy
        · rw [dif_neg hw2] at h
          cases h
      · rw [dif_neg hw1] at h
        cases h
    · rw [dif_neg h0'] at h
      cases h
  · rw [dif_neg h0] at h
    cases h

/-- A shift left that lowers keeps an empty footprint. -/
theorem links_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x y s : LowSide u Γ Λ}
    (hx : x.term.orte = []) (hy : y.term.orte = [])
    (h : LowSide.links x y = .ok s) : s.term.orte = [] := by
  unfold LowSide.links at h
  by_cases hbig : 4096 < y.range.2
  · rw [if_pos hbig] at h
    cases h
  · rw [if_neg hbig] at h
    by_cases h0 : 0 ≤ x.range.1
    · rw [dif_pos h0] at h
      by_cases h0' : 0 ≤ y.range.1
      · rw [dif_pos h0'] at h
        by_cases hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range
        · rw [dif_pos hw1] at h
          by_cases hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int)
          · rw [dif_pos hw2] at h
            cases h
            change x.term.orte ++ y.term.orte = []
            rw [hx, hy]; rfl
          · rw [dif_neg hw2] at h
            cases h
        · rw [dif_neg hw1] at h
          cases h
      · rw [dif_neg h0'] at h
        cases h
    · rw [dif_neg h0] at h
      cases h

/-- A lowered shift left denotes the source `x * 2 ^ y`. -/
theorem links_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x y s : LowSide u Γ Λ}
    (h : LowSide.links x y = .ok s) (a b : SExpr)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n)
    (dy : SourceValue fn constants env b (eval entry y.term state env).n) :
    SourceValue fn constants env (.bin "<<" a b) (eval entry s.term state env).n := by
  unfold LowSide.links at h
  by_cases hbig : 4096 < y.range.2
  · rw [if_pos hbig] at h
    cases h
  · rw [if_neg hbig] at h
    by_cases h0 : 0 ≤ x.range.1
    · rw [dif_pos h0] at h
      by_cases h0' : 0 ≤ y.range.1
      · rw [dif_pos h0'] at h
        by_cases hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range
        · rw [dif_pos hw1] at h
          by_cases hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int)
          · rw [dif_pos hw2] at h
            cases h
            exact SourceValue.shl dx dy
          · rw [dif_neg hw2] at h
            cases h
        · rw [dif_neg hw1] at h
          cases h
      · rw [dif_neg h0'] at h
        cases h
    · rw [dif_neg h0] at h
      cases h

/-- A shift right that lowers keeps an empty footprint. -/
theorem rechts_orte {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {x y s : LowSide u Γ Λ}
    (hx : x.term.orte = []) (hy : y.term.orte = [])
    (h : LowSide.rechts x y = .ok s) : s.term.orte = [] := by
  unfold LowSide.rechts at h
  by_cases hbig : 4096 < y.range.2
  · rw [if_pos hbig] at h
    cases h
  · rw [if_neg hbig] at h
    by_cases h0 : 0 ≤ x.range.1
    · rw [dif_pos h0] at h
      by_cases h0' : 0 ≤ y.range.1
      · rw [dif_pos h0'] at h
        by_cases hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range
        · rw [dif_pos hw1] at h
          by_cases hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int)
          · rw [dif_pos hw2] at h
            cases h
            change x.term.orte ++ y.term.orte = []
            rw [hx, hy]; rfl
          · rw [dif_neg hw2] at h
            cases h
        · rw [dif_neg hw1] at h
          cases h
      · rw [dif_neg h0'] at h
        cases h
    · rw [dif_neg h0] at h
      cases h

/-- A lowered shift right denotes the source `x / 2 ^ y`. -/
theorem rechts_denotes {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {constants : List (String × Int)} {x y s : LowSide u Γ Λ}
    (h : LowSide.rechts x y = .ok s) (a b : SExpr)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ)
    (dx : SourceValue fn constants env a (eval entry x.term state env).n)
    (dy : SourceValue fn constants env b (eval entry y.term state env).n) :
    SourceValue fn constants env (.bin ">>" a b) (eval entry s.term state env).n := by
  unfold LowSide.rechts at h
  by_cases hbig : 4096 < y.range.2
  · rw [if_pos hbig] at h
    cases h
  · rw [if_neg hbig] at h
    by_cases h0 : 0 ≤ x.range.1
    · rw [dif_pos h0] at h
      by_cases h0' : 0 ≤ y.range.1
      · rw [dif_pos h0'] at h
        by_cases hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range
        · rw [dif_pos hw1] at h
          by_cases hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int)
          · rw [dif_pos hw2] at h
            cases h
            exact SourceValue.shr dx dy
          · rw [dif_neg hw2] at h
            cases h
        · rw [dif_neg hw1] at h
          cases h
      · rw [dif_neg h0'] at h
        cases h
    · rw [dif_neg h0] at h
      cases h

end Gabbro.Grammatik.Parser.Measures
