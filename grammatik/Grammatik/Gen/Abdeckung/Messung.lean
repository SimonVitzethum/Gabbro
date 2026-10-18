/-
  File:      Grammatik/Gen/Abdeckung/Messung.lean
  Subject:   The MEASUREMENT of the generator: for one declaration of the family and one size, every skeleton of that
             exact size is classified by the ten components of the checker's Bool (`komp`): valid, refused only by
             component `c`, refused by two or more. The members each class contains are counted per member
             (`Zaehl`), with the least size at which each occurs, so the coverage of the register by valid programs and,
             separately, by single-fault refusals is COMPUTED from the generated sets, not counted by hand.

             The programs are the skeletons of `hautT` (contracts true), under the maximal lock family and a list of
             declared starts. Refusals that one change makes (a start added, a handler flag set, a lock family that
             protects a carrier its lock does not guard) are derived from valid programs (`mutanten`).
-/
import Std.Data.HashMap
import Grammatik.Gen.Abdeckung.Erklaerung

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- A count with the number of programs that contain each member and the least size at which it occurs. -/
structure Zaehl where
  n : Nat := 0
  m : Std.HashMap String Nat := {}
  kl : Std.HashMap String Nat := {}

/-- The sorted list without repetitions. -/
def dedupStr (xs : List String) : List String :=
  (xs.toArray.qsort (· < ·)).toList.foldr (fun a acc => match acc with | b :: _ => if a == b then acc else a :: acc | [] => [a]) []

/-- Count one more program of size `k` with the given members. -/
def Zaehl.add (c : Zaehl) (k : Nat) (ms : List String) : Zaehl :=
  let ms := dedupStr ms
  { n := c.n + 1, m := ms.foldl (fun m s => m.insert s (m.getD s 0 + 1)) c.m,
    kl := ms.foldl (fun m s => m.insert s (Nat.min (m.getD s k) k)) c.kl }

/-- Add two counts. -/
def Zaehl.plus (a b : Zaehl) : Zaehl :=
  { n := a.n + b.n, m := b.m.fold (fun m s k => m.insert s (m.getD s 0 + k)) a.m,
    kl := b.kl.fold (fun m s k => m.insert s (Nat.min (m.getD s k) k)) a.kl }

/-- Count members by name (the members of a declaration): once each. -/
def Zaehl.nenne (c : Zaehl) (k : Nat) (ms : List String) : Zaehl :=
  let ms := dedupStr ms
  { c with m := ms.foldl (fun m s => m.insert s (m.getD s 0 + 1)) c.m,
           kl := ms.foldl (fun m s => m.insert s (Nat.min (m.getD s k) k)) c.kl }

/-- **The classification of the skeletons of one size.** -/
structure Klasse where
  alle : Nat := 0
  gueltig : Zaehl := {}
  nur : Array Zaehl := Array.replicate 10 {}
  mehr : Nat := 0

def Klasse.plus (a b : Klasse) : Klasse :=
  { alle := a.alle + b.alle, gueltig := a.gueltig.plus b.gueltig,
    nur := (List.range 10).toArray.map fun c => (a.nur.getD c {}).plus (b.nur.getD c {}), mehr := a.mehr + b.mehr }

/-- The components of a program under the lock family `S`, the lists `fs ls cs` and the starts `ws`, as ten Bools. -/
def kompListe {D : Deklaration} [Aufz D] [Zahlen] (P : Programm D) (S : SperrInv D) (fs : List D.Fn)
    (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : List Bool :=
  (List.finRange 10).map (komp P S fs ls cs ws)

/-- `NurAn c` as a Bool. -/
def nurAnB {D : Deklaration} [Aufz D] [Zahlen] (c : Fin 10) (P : Programm D) (S : SperrInv D) (fs : List D.Fn)
    (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) : Bool :=
  (komp P S fs ls cs ws c == false) &&
    (List.finRange 10).all fun c' => c' == c || komp P S fs ls cs ws c' == true

theorem nurAnB_iff {D : Deklaration} [Aufz D] [Zahlen] (c : Fin 10) (P : Programm D) (S : SperrInv D) (fs : List D.Fn)
    (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn) :
    nurAnB c P S fs ls cs ws = true ↔ NurAn c P S fs ls cs ws := by
  unfold nurAnB NurAn
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, List.mem_finRange, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c' hc => by
      rcases h2 c' with h | h
      · exact absurd h hc
      · exact h⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c' => by
      by_cases hc : c' = c
      · exact Or.inl hc
      · exact Or.inr (h2 c' hc)⟩

/-- Classify one program of size `k`: the label of the one component that refuses it, if exactly one does. -/
def Klasse.einordnen (kl : Klasse) (k : Nat) (komps : List Bool) (ms : List String) : Klasse :=
  let falsch := (List.range 10).filter fun c => komps.getD c true == false
  match falsch with
  | [] => { kl with alle := kl.alle + 1, gueltig := kl.gueltig.add k ms }
  | [c] => { kl with alle := kl.alle + 1, nur := kl.nur.modify c (·.add k ms) }
  | _ => { kl with alle := kl.alle + 1, mehr := kl.mehr + 1 }

/-- **The tables of the bodies** of the declaration of `z` (bodies of size at most `nb`; the filter keeps the bodies
    that must pass components 3 and 8). Built once, read at every size. -/
def Spez.tabellen (z : Spez) (nb : Nat) (p3 p8 : Bool) :
    List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))) :=
  letI : Zahlen := z.zahlen
  rumpfTab (okFuer p3 p8 (List.finRange z.fns.length)) nb

/-- The tables of the bodies filtered by the components that must pass (3 and 8): the bodies that fail are dropped. -/
def Spez.filtere (z : Spez) (p3 p8 : Bool)
    (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f)))) :
    List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))) :=
  letI : Zahlen := z.zahlen
  let ok := okFuer p3 p8 (List.finRange z.fns.length)
  tbls.map fun t => ⟨t.1, t.2.map fun b => b.filter (ok t.1)⟩

/-- **Classify every skeleton of exact size `k`** under the maximal lock family and the starts `ws`. -/
def Spez.klassiere (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f)))) (k : Nat)
    (ws : List z.deklaration.Fn) : Klasse :=
  letI : Zahlen := z.zahlen
  let fs := List.finRange z.fns.length
  let ls := List.finRange z.locks.length
  let cs := z.traegerListe
  let S := z.sperreMax
  (hautT tbls k).foldl (fun acc h => acc.einordnen k (kompListe h.programm S fs ls cs ws) (hautM h)) {}

/-! ## The one-change refusals -/

/-- A lock family that protects a carrier its lock does not guard (the first such pair), if there is one. -/
def Spez.schlechteSperre (z : Spez) : Option (SperrInv z.deklaration) :=
  match z.locks.length with
  | 0 => none
  | _ =>
    match (List.finRange z.locks.length).flatMap (fun L => z.traegerListe.filterMap fun c =>
        if decide (L ∈ waechterVon c) then none else some (L, c)) with
    | [] => none
    | (L, c) :: _ => some { orte := fun L' => if L' = L then [c] else [], inv := fun _ _ => true }

/-- **Refused by ONE change from a valid program.** Every program of exact size `k` that is valid under the maximal
    lock family and the starts `ws` is changed in one place: a function is added to the starts (a function that holds
    a lock or has reasons cannot be a root; a root declared twice is a pool; two roots may race), the handler flag
    of a function is set (the handler may take a lock that does not mask interrupts), the lock family protects a
    carrier its lock does not guard. The class of every changed program by the components, with the members. -/
def Spez.mutanten (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f)))) (k : Nat)
    (ws : List z.deklaration.Fn) : Nat × Klasse :=
  letI : Zahlen := z.zahlen
  let fs : List z.deklaration.Fn := List.finRange z.fns.length
  let ls : List z.deklaration.Lock := List.finRange z.locks.length
  let cs := z.traegerListe
  let S := z.sperreMax
  (hautT tbls k).foldl
    (fun (acc : Nat × Klasse) h =>
      if AkzeptiertX h.programm S fs ls cs ws then
        let aendern : List (Haut z.deklaration × SperrInv z.deklaration × List z.deklaration.Fn) :=
          (fs.map fun w => (h, S, ws ++ [w])) ++
          (fs.map fun f => ({ h with unterbricht := fun g => decide (g = f) || h.unterbricht g }, S, ws)) ++
          (z.schlechteSperre.toList.map fun S' => (h, S', ws))
        (acc.1 + 1, aendern.foldl (fun kl c =>
          kl.einordnen k (kompListe c.1.programm c.2.1 fs ls cs c.2.2) (hautM c.1)) acc.2)
      else acc) (0, {})

/-! ## Programs with every contract -/

/-- **The valid programs of exact size `k` with every contract** (bodies of size at most `nb`, contracts and invariants
    of size at most `nc`): the count, the programs that are valid under the starts `ws`, and the members of those. -/
def Spez.mitVertraegen (z : Spez) (nb nc k : Nat) (ws : List z.deklaration.Fn) : Nat × Zaehl :=
  letI : Zahlen := z.zahlen
  let fs := List.finRange z.fns.length
  let ls := List.finRange z.locks.length
  let cs := z.traegerListe
  let S := z.sperreMax
  (progS nb nc k).foldl (fun (acc : Nat × Zaehl) P =>
    if AkzeptiertX P S fs ls cs ws then (acc.1 + 1, acc.2.add k (progM P)) else (acc.1 + 1, acc.2)) (0, {})

end Gabbro.Grammatik.Gen
