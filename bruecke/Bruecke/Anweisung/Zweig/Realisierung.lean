module
public import Bruecke.Anweisung.Zweig.Rahmen
public import Bruecke.Anweisung.Lokal.Rahmen
@[expose] public section

/-!
# Callee discovery in structured bodies

The reader lemmas find each translated call in the flat source body and resolve its target.
The carried realization in `Kette/` uses them to discharge the rank-decreasing callee duties.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Every call finds its callee -/

theorem callee_of_schrittB {fn fn' : UFn} {ns ns' : BodyNames} {g : String}
    {args : List UArg} {b : Gabbro.Body.Stmt}
    (hs : schrittB u fn ns (.call g args) = some (b, fn', ns')) :
    ∃ gf, fnSuch u g = some gf := by
  obtain ⟨hb, _, _⟩ := schrittB_stmt hs (fun _ _ _ h => by cases h)
    (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
  obtain ⟨raw, hb, _⟩ := namedStmt_some hb
  simp only [stmtBody] at hb
  split at hb
  · rename_i gf es hgf _
    exact ⟨gf, hgf⟩
  · cases hb

theorem mem_tail_of_ne {a b : UStmt} {l : List UStmt} (h : a ∈ b :: l) (hne : a ≠ b) : a ∈ l := by
  rcases List.mem_cons.mp h with h' | h'
  · exact absurd h' hne
  · exact h'

/-- A call the block reader reads finds its callee, or it lies in what is left. -/
theorem seqZ_callee : ∀ (k : Nat) (fn : UFn) (ns : BodyNames) (ss : List UStmt) (t : List Gabbro.Body.Stmt)
    (rest : List UStmt) (used : List String), seqZ u k fn ns ss = some (t, rest, used) → ∀ (g : String) (args : List UArg),
      UStmt.call g args ∈ ss → (∃ gf, fnSuch u g = some gf) ∨ UStmt.call g args ∈ rest
  | 0, _, _, _, _, _, _, h, _, _, _ => by simp only [seqZ, reduceCtorEq] at h
  | k + 1, _, _, [], _, _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | k + 1, fn, ns, s0 :: ss, t, rest, used, h, g, args, hm => by
      cases s0
      case blkEnd | ifElse =>
        simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact .inr hm
      case ifBeg cnd | ifEnde cnd =>
        obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, _, hT, hE, hY, _⟩ :=
          seqZ_wenn_some (cnd := cnd) h (by first | exact .inl rfl | exact .inr rfl)
        have hm' := mem_tail_of_ne hm (by intro h'; cases h')
        rcases seqZ_callee k fn ns ss tt _ used1 hT g args hm' with hf | hm1
        · exact .inl hf
        · rcases seqZ_callee k fn (ns.resume used1) r1 te _ used2 hE g args (mem_tail_of_ne hm1 (by intro h'; cases h'))
            with hf | hm2
          · exact .inl hf
          · exact seqZ_callee k fn (ns.resume used2) r2 ys rest used hY g args (mem_tail_of_ne hm2 (by intro h'; cases h'))
      case ret r0 =>
        obtain ⟨b, ys, _, hY, _⟩ := seqZ_ret_some h
        exact seqZ_callee k fn ns ss ys rest used hY g args (mem_tail_of_ne hm (by intro h'; cases h'))
      case call g' args' =>
        obtain ⟨b, fn', ns', ys, hs, hY, _⟩ := seqZ_schritt_some h (by exact True.intro)
        rcases List.mem_cons.mp hm with h' | h'
        · cases h'
          exact .inl (callee_of_schrittB hs)
        · exact seqZ_callee k fn' ns' ss ys rest used hY g args h'
      case bind | bindMut | setVar | assign | assignTab | assignGlob =>
        obtain ⟨b, fn', ns', ys, hs, hY, _⟩ := seqZ_schritt_some h (by exact True.intro)
        exact seqZ_callee k fn' ns' ss ys rest used hY g args (mem_tail_of_ne hm (by intro h'; cases h'))
      all_goals exact absurd h (by simp only [seqZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

/-- A call of a body the body reader reads finds its callee. -/
theorem stmtsBodyZ_callee (r : URet) : ∀ (k : Nat) (fn : UFn) (ns : BodyNames) (ss : List UStmt)
    (bs : List Gabbro.Body.Stmt), stmtsBodyZ u k fn ns ss r = some bs →
    ∀ (g : String) (args : List UArg), UStmt.call g args ∈ ss → ∃ gf, fnSuch u g = some gf
  | 0, _, _, _, _, h, _, _, _ => by simp only [stmtsBodyZ, reduceCtorEq] at h
  | k + 1, _, _, [], _, _, _, _, hm => absurd hm List.not_mem_nil
  | k + 1, fn, ns, s0 :: ss, bs, h, g, args, hm => by
      cases s0
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', used1, used2, _, hT, hE, hY, _⟩ := stmtsBodyZ_ifBeg_some h
        have hm' := mem_tail_of_ne hm (by intro h'; cases h')
        rcases seqZ_callee k fn ns ss tt _ used1 hT g args hm' with hf | hm1
        · exact hf
        · rcases seqZ_callee k fn (ns.resume used1) r1 te _ used2 hE g args (mem_tail_of_ne hm1 (by intro h'; cases h'))
            with hf | hm2
          · exact hf
          · exact stmtsBodyZ_callee r k fn (ns.resume used2) r2 bs' hY g args
              (mem_tail_of_ne hm2 (by intro h'; cases h'))
      case call g' args' =>
        obtain ⟨b, fn', ns', bs', hs, hY, _⟩ := stmtsBodyZ_schritt_some h (by exact True.intro)
        rcases List.mem_cons.mp hm with h' | h'
        · cases h'
          exact callee_of_schrittB hs
        · exact stmtsBodyZ_callee r k fn' ns' ss bs' hY g args h'
      case bind | bindMut | setVar | assign | assignTab | assignGlob =>
        obtain ⟨b, fn', ns', bs', hs, hY, _⟩ := stmtsBodyZ_schritt_some h (by exact True.intro)
        exact stmtsBodyZ_callee r k fn' ns' ss bs' hY g args (mem_tail_of_ne hm (by intro h'; cases h'))
      all_goals exact absurd h (by simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

theorem callee_gefundenZ {f : UFn} {body : List Gabbro.Body.Stmt} (h : zuBodyZ u f = some body)
    (g : String) (args : List UArg) (hm : UStmt.call g args ∈ f.body) :
    ∃ gf, fnSuch u g = some gf :=
  stmtsBodyZ_callee f.ret _ f (BodyNames.start f) f.body body h g args hm

end Gabbro.Bruecke
