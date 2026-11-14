module
public import Bruecke.Anweisung.Zweig.Rahmen
public import Bruecke.Anweisung.Lokal.Rahmen
public import Bruecke.Anweisung.Ruf.Lesen
public import Bruecke.Anweisung.Bereich.Lesen
public import Bruecke.Anweisung.Schleife.Lesen
public import Bruecke.Anweisung.Match.ReasonLesen
public import Bruecke.Anweisung.Match.TagLesen
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
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
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

theorem callee_of_bindCall {fn fn' : UFn} {ns ns' : BodyNames} {x g : String}
    {args : List UArg} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns (.bindCall x g args) = some (b, fn', ns')) :
    ∃ gf, fnSuch u g = some gf := by
  obtain ⟨ty, hr, _, _⟩ := schrittB_bindCall h
  obtain ⟨gf, _, _, _, hgf, _⟩ := namedResult_some hr
  exact ⟨gf, hgf⟩

theorem endBodyZ_callee : ∀ k fn ns ss bs tail,
    endBodyZ u k fn ns ss = some (bs, tail) → ∀ g args,
    CallsIn ss g args → (∃ gf, fnSuch u g = some gf) ∨ CallsIn tail g args
  | 0, _, _, _, _, _, h, _, _, _ => by cases h
  | _ + 1, _, _, [], _, _, h, _, _, _ => by cases h
  | k + 1, fn, ns, st :: ss, bs, tail, h, g, args, hm => by
    rcases endBodyZ_cases h with ⟨r, b, rfl, _, _, rfl⟩ | ⟨b, ys, hl, hs, hy, _⟩
    · exact .inr (CallsIn.tail (by rfl) hm)
    · rcases CallsIn.head_or_tail hm with hc | hc
      · cases st
        case call cn as =>
          cases hc
          exact .inl (callee_of_schrittB hs)
        case bindCall x cn as =>
          cases hc
          exact .inl (callee_of_bindCall hs)
        all_goals first | cases hc | cases hl
      · exact endBodyZ_callee k fn ns ss ys tail hy g args hc

/-- A call the block reader reads finds its callee, or it lies in what is left. -/
theorem seqZ_callee : ∀ (k : Nat) (fn : UFn) (ns : BodyNames) (ss : List UStmt) (t : List Gabbro.Body.Stmt)
    (rest : List UStmt) (used : List String), seqZ u k fn ns ss = some (t, rest, used) → ∀ (g : String) (args : List UArg),
      CallsIn ss g args → (∃ gf, fnSuch u g = some gf) ∨ CallsIn rest g args
  | 0, _, _, _, _, _, _, h, _, _, _ => by simp only [seqZ, reduceCtorEq] at h
  | k + 1, _, _, [], _, _, _, _, _, _, hm => by obtain ⟨st, hm, _⟩ := hm; cases hm
  | k + 1, fn, ns, s0 :: ss, t, rest, used, h, g, args, hm => by
      cases s0
      case blkEnd | ifElse =>
        simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact .inr hm
      case ifBeg cnd | ifEnde cnd =>
        obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, _, hT, hE, hY, _⟩ :=
          seqZ_wenn_some (cnd := cnd) h (by first | exact .inl rfl | exact .inr rfl)
        have hm' := CallsIn.tail (by rfl) hm
        rcases seqZ_callee k fn ns ss tt _ used1 hT g args hm' with hf | hm1
        · exact .inl hf
        · rcases seqZ_callee k fn (ns.resume used1) r1 te _ used2 hE g args (CallsIn.tail (by rfl) hm1)
            with hf | hm2
          · exact .inl hf
          · exact seqZ_callee k fn (ns.resume used2) r2 ys rest used hY g args (CallsIn.tail (by rfl) hm2)
      case ret r0 =>
        obtain ⟨b, ys, _, hY, _⟩ := seqZ_ret_some h
        exact seqZ_callee k fn ns ss ys rest used hY g args (CallsIn.tail (by rfl) hm)
      case narrowBeg x lo hi =>
        obtain ⟨e, err, tail, ys, _, hE, hY, _⟩ := seqZ_narrow_some h
        rcases endBodyZ_callee k fn ns ss err _ hE g args (CallsIn.tail (by rfl) hm) with hf | hc
        · exact .inl hf
        · exact seqZ_callee k (fn.mitBindung x (lo, hi)) (ns.push x) tail ys rest used hY g args
            (CallsIn.tail (by rfl) hc)
      case loopBeg x tab inv =>
        obtain ⟨rfl, hg, t, body, tail, allocated, ys, _, hB, hY, _⟩ := seqZ_loop_some h
        have ht := loopWrites_calls k _ _ ss body tail allocated hg hB g args (CallsIn.tail (by rfl) hm)
        exact seqZ_callee k fn (ns.resume allocated) tail ys rest used hY g args ht
      case call g' args' | bindCall x g' args' =>
        obtain ⟨b, fn', ns', ys, hs, hY, _⟩ := seqZ_schritt_some h (by exact True.intro)
        rcases CallsIn.head_or_tail hm with h' | h'
        · cases h'
          first | exact .inl (callee_of_schrittB hs) | exact .inl (callee_of_bindCall hs)
        · exact seqZ_callee k fn' ns' ss ys rest used hY g args h'
      case bind | bindMut | bindB | setVar | setVarB | assign | assignTab | assignGlob =>
        obtain ⟨b, fn', ns', ys, hs, hY, _⟩ := seqZ_schritt_some h (by exact True.intro)
        exact seqZ_callee k fn' ns' ss ys rest used hY g args (CallsIn.tail (by rfl) hm)
      all_goals exact absurd h (by simp only [seqZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

theorem reasonArmsZ_callee (k : Nat) (fn : UFn) : ∀ count offset ns ss bs tail used,
    reasonArmsZ u k fn count offset ns ss = some (bs, tail, used) → ∀ g args,
    CallsIn ss g args → (∃ gf, fnSuch u g = some gf) ∨ CallsIn tail g args
  | 0, _, _, _, _, _, _, h, g, args, hm => by
    cases h
    exact .inr hm
  | count + 1, offset, ns, ss, bs, tail, used, h, g, args, hm => by
    obtain ⟨body, remaining, allocated, hb, hc⟩ := reasonArmsZ_succ h
    rcases seqZ_callee k fn ns ss body remaining allocated hb g args hm with hf | hm
    · exact .inl hf
    · rcases hc with ⟨_, _, rfl, _⟩ | ⟨m, rest, restArms, rfl, rfl, hr, _⟩
      · exact .inr hm
      · exact reasonArmsZ_callee k fn (m + 1) (offset + 1) (ns.resume allocated) rest
          restArms tail used hr g args (CallsIn.tail (by rfl) hm)

/-- A call of a body the body reader reads finds its callee. -/
theorem stmtsBodyZ_callee (r : URet) : ∀ (k : Nat) (fn : UFn) (ns : BodyNames) (ss : List UStmt)
    (bs : List Gabbro.Body.Stmt), stmtsBodyZ u k fn ns ss r = some bs →
    ∀ (g : String) (args : List UArg), CallsIn ss g args → ∃ gf, fnSuch u g = some gf
  | 0, _, _, _, _, h, _, _, _ => by simp only [stmtsBodyZ, reduceCtorEq] at h
  | k + 1, _, _, [], _, _, _, _, hm => by obtain ⟨st, hm, _⟩ := hm; cases hm
  | k + 1, fn, ns, s0 :: ss, bs, h, g, args, hm => by
      cases s0
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', used1, used2, _, hT, hE, hY, _⟩ := stmtsBodyZ_ifBeg_some h
        have hm' := CallsIn.tail (by rfl) hm
        rcases seqZ_callee k fn ns ss tt _ used1 hT g args hm' with hf | hm1
        · exact hf
        · rcases seqZ_callee k fn (ns.resume used1) r1 te _ used2 hE g args (CallsIn.tail (by rfl) hm1)
            with hf | hm2
          · exact hf
          · exact stmtsBodyZ_callee r k fn (ns.resume used2) r2 bs' hY g args
              (CallsIn.tail (by rfl) hm2)
      case call g' args' | bindCall x g' args' =>
        obtain ⟨b, fn', ns', bs', hs, hY, _⟩ := stmtsBodyZ_schritt_some h (by exact True.intro)
        rcases CallsIn.head_or_tail hm with h' | h'
        · cases h'
          first | exact callee_of_schrittB hs | exact callee_of_bindCall hs
        · exact stmtsBodyZ_callee r k fn' ns' ss bs' hY g args h'
      case matchTagBeg sidx x binders =>
        obtain ⟨cs, e, arms, tail, allocated, ys, hn, he, ha, hy, _⟩ := stmtsBodyZ_tag_some h
        rcases reasonArmsZ_callee k fn cs.length 0 ns ss arms (.blkEnd :: tail) allocated ha
          g args (CallsIn.tail (by rfl) hm) with hf | hm
        · exact hf
        · exact stmtsBodyZ_callee r k fn (ns.resume allocated) tail ys hy g args (CallsIn.tail (by rfl) hm)
      case matchWhyBeg x =>
        obtain ⟨count, e, arms, tail, allocated, ys, he, ha, hy, _⟩ := stmtsBodyZ_reason_some h
        rcases reasonArmsZ_callee k fn count 0 ns ss arms (.blkEnd :: tail) allocated ha
          g args (CallsIn.tail (by rfl) hm) with hf | hm
        · exact hf
        · exact stmtsBodyZ_callee r k fn (ns.resume allocated) tail ys hy g args (CallsIn.tail (by rfl) hm)
      case matchBeg num v x =>
        obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, _, hp, ha, hy, _⟩ := stmtsBodyZ_option_some h
        have hm' := CallsIn.tail (by rfl) hm
        rcases seqZ_callee k _ (ns.push x) ss pb _ used1 hp g args hm' with hf | hc
        · exact hf
        · rcases seqZ_callee k fn (ns.resume used1) r1 ab _ used2 ha g args
            (CallsIn.tail (by rfl) hc) with hf | hc
          · exact hf
          · exact stmtsBodyZ_callee r k fn (ns.resume used2) r2 ys hy g args
              (CallsIn.tail (by rfl) hc)
      case narrowBeg x lo hi =>
        obtain ⟨e, err, tail, ys, _, hE, hY, _⟩ := stmtsBodyZ_narrow_some h
        rcases endBodyZ_callee k fn ns ss err _ hE g args (CallsIn.tail (by rfl) hm) with hf | hc
        · exact hf
        · exact stmtsBodyZ_callee r k (fn.mitBindung x (lo, hi)) (ns.push x) tail ys hY g args
            (CallsIn.tail (by rfl) hc)
      case loopBeg x tab inv =>
        obtain ⟨rfl, hg, t, body, tail, allocated, ys, _, hB, hY, _⟩ := stmtsBodyZ_loop_some h
        have ht := loopWrites_calls k _ _ ss body tail allocated hg hB g args (CallsIn.tail (by rfl) hm)
        exact stmtsBodyZ_callee r k fn (ns.resume allocated) tail ys hY g args ht
      case bindW x d v =>
        obtain ⟨id, fields, e, ys, rfl, he, hys, _⟩ := stmtsBodyZ_bindRecord_some h
        exact stmtsBodyZ_callee r k (fn.mitWert x (.prod id fields)) (ns.push x) ss ys hys g args
          (CallsIn.tail (by rfl) hm)
      case bind | bindMut | bindB | setVar | setVarB | assign | assignTab | assignGlob =>
        obtain ⟨b, fn', ns', bs', hs, hY, _⟩ := stmtsBodyZ_schritt_some h (by exact True.intro)
        exact stmtsBodyZ_callee r k fn' ns' ss bs' hY g args (CallsIn.tail (by rfl) hm)
      all_goals exact absurd h (by simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

theorem callee_gefundenZ {f : UFn} {body : List Gabbro.Body.Stmt} (h : zuBodyZ u f = some body)
    (g : String) (args : List UArg) (hm : CallsIn f.body g args) :
    ∃ gf, fnSuch u g = some gf :=
  stmtsBodyZ_callee f.ret _ f (BodyNames.start f) f.body body h g args hm

end Gabbro.Bruecke
