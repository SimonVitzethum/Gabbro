module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik
variable {D : Deklaration}

/-- `schreibBytes t` with a positive count records a write event for `t`.
    Split on `n`: at `n = 0` the byte list is empty (length `0`), so the
    fold is the identity and the head case below needs `n = m+1`, where the
    byte list has length `m+1 > 0` and the definitional unfold exposes the
    first `schreibSlot` write. -/
theorem schreibBytes_neu (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t : D.Tab} {f : D.Feld t} {hf : D.typ t f = .int 0 255} {n : Nat}
    {lo hi : Int}
    {i : Expr D Γ Λ (.int lo hi)} {hlo : 0 ≤ lo} {hhi : hi + n ≤ D.count t}
    {e : Expr D Γ Λ (.int 0 (256 ^ n - 1))}
    {hw : V.schreibt t = true} {hL : darf D t Λ}
    (hn : 0 < n)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (.putBytes t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt
      = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    ∃ ev ∈ neu, ev.traeger = some (Sum.inl t) := by
  -- Name the entry world, index, value, and byte list.
  have hlen : (zahlZuBytes n (eval (σ.lese Λ (i.orte ++ e.orte)) e
      (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length = n :=
    zahlZuBytes_length n _
  -- Split on `n`: `n = 0` contradicts `hn`; at `n = m+1` unfold one step.
  cases hn' : n with
  | zero => omega
  | succ m =>
      -- Abbreviate the value whose bytes are written.
      have hz : (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n =
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n := rfl
      -- The byte list is `b0 :: bs` for some head and tail.
      obtain ⟨b0, bs, hbs⟩ : ∃ b0 bs, zahlZuBytes (m + 1)
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n = b0 :: bs := by
        cases hbl : zahlZuBytes (m + 1)
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n with
        | nil =>
            have hlen2 := zahlZuBytes_length (m + 1)
              (eval (σ.lese Λ (i.orte ++ e.orte)) e
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n
            rw [hbl] at hlen2
            simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false] at hlen2
        | cons b0 bs => exact ⟨b0, bs, rfl⟩
      clear hz
      -- Rewrite `n` to `m+1` everywhere it matters.
      have hnEq : n = m + 1 := by omega
      subst hnEq
      -- Abbreviate the entry world and index for readability.
      have hσL : σ.lese Λ (i.orte ++ e.orte) =
          σ.lese Λ (i.orte ++ e.orte) := rfl
      clear hσL
      have hfold₂ : (σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f hf Λ
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n
          (zahlZuBytes (m + 1)
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n) =
          (((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
            (cast (congrArg (Wert D) hf).symm
              (b0 : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ
            ((eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs) := by
        rw [hbs]
        rfl
      -- `hstep` fires the same statement (after `subst`, `n = m+1`
      -- definitionally); unfold its fold the same way and conclude.
      have hrfl : (execStmt O passes keinRuf
          ((.putBytes t f hf (m + 1) i hlo hhi e hw hL :
            Stmt D V l Γ Λ Λ)) σ ρ).welt =
          Ausgang.welt (D := D) (V := V) (l := l) (Γ := Γ) (Ausgang.ok
            ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f hf Λ
              (eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n
              (zahlZuBytes (m + 1)
                (eval (σ.lese Λ (i.orte ++ e.orte)) e
                  (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) ρ) := rfl
      have hstepFold : (execStmt O passes keinRuf
            ((.putBytes t f hf (m + 1) i hlo hhi e hw hL :
              Stmt D V l Γ Λ Λ)) σ ρ).welt =
            some ((((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
              (eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
              (cast (congrArg (Wert D) hf).symm
                (b0 : Wert D (.int 0 255)))).schreibBytes
              t f hf Λ
              ((eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs)) := by
          rw [hrfl, Ausgang.welt, hfold₂]
      -- Now `hstep` and `hstepFold` agree; extract the outcome world.
      have hσ' : σ' = (((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
            (cast (congrArg (Wert D) hf).symm
              (b0 : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ
            ((eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs) :=
          Option.some_inj.mp (hstep.symm.trans hstepFold)
        -- The head write event sits in the tail fold spur by the suffix lemma.
      have hmem0 : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈
            ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
              (eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
              (cast (congrArg (Wert D) hf).symm
                (b0 : Wert D (.int 0 255)))).spur :=
          List.mem_cons_self
      obtain ⟨preTail, hpreTail⟩ := schreibBytes_spur_suffix
          ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
            (cast (congrArg (Wert D) hf).symm
              (b0 : Wert D (.int 0 255))))
          t f hf Λ _ bs
      have hmemFold : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ σ'.spur := by
          rw [hσ']
          rw [hpreTail]
          exact List.mem_append_right _ hmem0
        -- Cancel the common `lese` suffix: `neu` is the fold prefix.
      have hspur₀ : (σ.lese Λ (i.orte ++ e.orte)).spur =
            ((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := rfl
      obtain ⟨pre, hpre⟩ := schreibBytes_spur_suffix
          (σ.lese Λ (i.orte ++ e.orte)) t f hf Λ
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n
          (zahlZuBytes (m + 1)
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n)
      have hσspur : σ'.spur = pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
          -- `hσ'` unfolds the outcome to the tail fold; `hpre` states the
          -- whole fold spur. Rewrite the goal through both equations.
          rw [hσ']
          rw [← hfold₂]
          exact hpre
      -- Cancel the common suffix: `neu` is the fold prefix plus reads.
      have hcancel : neu = pre ++ ((i.orte ++ e.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) := by
        have hassoc : (pre ++ ((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt)) ++ σ.spur =
            pre ++ (((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur) :=
          List.append_assoc _ _ _
        have hfull₂ : neu ++ σ.spur =
            (pre ++ ((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt)) ++ σ.spur := by
          rw [hassoc, ← hspur₀, ← hσspur]; exact hneu.symm
        exact List.append_cancel_right hfull₂
      -- Split the head event over `pre ++ reads ++ old`.
      have hevσ₂ : Ereignis.zugriff t true Λ
          (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ neu ++ σ.spur := by
        rw [← hneu]; exact hmemFold
      rw [hcancel] at hevσ₂
      have hsplit : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ pre ∨
          Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈
            ((i.orte ++ e.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ∨
          Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ σ.spur := by
        have hmem : Ereignis.zugriff t true Λ
              (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ pre ++
            (((i.orte ++ e.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur) := by
          rw [← List.append_assoc]; exact hevσ₂
        rw [List.mem_append, List.mem_append] at hmem
        exact hmem
      rcases hsplit with hmemPre | hmemRead | hmemOld
      · refine ⟨Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_, rfl⟩
        rw [hcancel]
        exact List.mem_append_left _ hmemPre
      · obtain ⟨o, ho, hcon⟩ := List.mem_map.mp hmemRead
        cases o with
        | inl t2 =>
            simp only at hcon
            have hflag := congrArg (ereignisSchreibt (D := D)) hcon
            simp only [ereignisSchreibt] at hflag
            exact absurd hflag (by simp only [Option.some.injEq, Bool.false_eq_true, not_false_eq_true])
        | inr g' =>
            simp only at hcon
            exact absurd hcon (by simp only [reduceCtorEq, not_false_eq_true])
      · -- Old: the head write coincides with an old event. Reuse the
        -- `hmemFold`-in-`pre` argument: the head is in the tail fold spur,
        -- whose `preTail` part injects into `pre` by suffix cancellation.
        -- `hmemFold` was proved from `hpreTail`; `hpre` covers the whole
        -- fold. The head is in `pre` iff the tail split puts it there --
        -- but we are in the old case. Close by noting `hevσ₂` already
        -- split this way: contradiction is impossible, so use `hmemPre`
        -- from re-splitting `hmemFold` through `hpre` (not `hpreTail`).
        have hHeadPre : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ pre := by
          have hmem : Ereignis.zugriff t true Λ
              (σ.lese Λ (i.orte ++ e.orte)).haelt ∈
              pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
            rw [← hσspur]; exact hmemFold
          rw [hspur₀] at hmem
          rw [List.mem_append] at hmem
          rcases hmem with hG | hH
          · exact hG
          · rw [List.mem_append] at hH
            rcases hH with hI | hJ
            · obtain ⟨o, ho, hcon⟩ := List.mem_map.mp hI
              cases o with
              | inl t2 =>
                  simp only at hcon
                  have hflag := congrArg (ereignisSchreibt (D := D)) hcon
                  simp only [ereignisSchreibt] at hflag
                  exact absurd hflag (by simp only [Option.some.injEq, Bool.false_eq_true, not_false_eq_true])
              | inr g' =>
                  simp only at hcon
                  exact absurd hcon (by simp only [reduceCtorEq, not_false_eq_true])
            · -- Old again at the `hpre` level: iterate once more via
              -- `hpreTail` -- the tail fold spur is strictly shorter, so
              -- one unroll reaches `preTail` or the head world. The head
              -- world spur is `[head] ++ lese`, so membership there is the
              -- head itself or a read (closed above) or older (same shape,
              -- one level down). Since the byte list is finite, this
              -- terminates -- but Lean needs the induction. Instead observe
              -- `hmemFold` came from `hpreTail`'s RIGHT disjunct already
              -- (`hmem0`), i.e. the head IS in the head-world spur, hence
              -- in `preTail`'s base -- no. Direct: `hmem0` IS the head in
              -- the head spur; `hpreTail` puts the tail fold spur over it.
              -- The whole fold spur `hpre` extends the same base, so the
              -- head is at a FIXED position in `pre`: it is `pre`'s suffix
              -- element. Positional: `pre = preTail ++ [head]`.
              have hpos : pre = preTail ++ [Ereignis.zugriff t true Λ
                  (σ.lese Λ (i.orte ++ e.orte)).haelt] := by
                -- `hpreTail` extends the head spur `[head] ++ lese-spur`;
                -- `hpre` extends the same `lese-spur` through the whole fold
                -- (equal by `hfold₂`). Chain them and cancel the suffix.
                have hchain : preTail ++ ([Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
                    (σ.lese Λ (i.orte ++ e.orte)).spur) =
                    pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
                  have e1 : (((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
                      (eval (σ.lese Λ (i.orte ++ e.orte)) i
                        (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
                      (cast (congrArg (Wert D) hf).symm
                        (b0 : Wert D (.int 0 255)))).schreibBytes
                      t f hf Λ
                      ((eval (σ.lese Λ (i.orte ++ e.orte)) i
                        (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs).spur =
                      preTail ++ ([Ereignis.zugriff t true Λ
                        (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
                        (σ.lese Λ (i.orte ++ e.orte)).spur) := by
                    rw [hpreTail]
                    rfl
                  rw [← e1, ← hfold₂]
                  exact hpre
                have hchain2 : preTail ++ ([Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
                    (σ.lese Λ (i.orte ++ e.orte)).spur) =
                    pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur :=
                  hchain
                have hchain3 : (preTail ++ [Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt]) ++
                    (σ.lese Λ (i.orte ++ e.orte)).spur =
                    pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
                  rw [List.append_assoc]
                  exact hchain2
                have hpos2 : preTail ++ [Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt] = pre :=
                  List.append_cancel_right hchain3
                exact hpos2.symm
              rw [hpos]
              exact List.mem_append_right _ List.mem_cons_self
        refine ⟨Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_, rfl⟩
        rw [hcancel]
        exact List.mem_append_left _ hHeadPre


end Gabbro.Grammatik.EZD
