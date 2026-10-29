/-
  File:      stage0/Stage0/Senke/Welt/Anordnung.lean
  Subject:   The world layout of an elaborated program (`layU u tor b`): from byte `b` every global one word, then every
             column of every table, its elements one word each, one after the other (`layU_in`).
-/
import Grammatik.Parser.Elab.UebersetzeAllg
import Stage0.Senke.Welt.WeltAt
import Stage0.Senke.BildSatz

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

set_option linter.unusedSectionVars false

variable [Kern]

/-- The bytes of one column. -/
def colSz (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Nat :=
  8 * ((declOf u).count t).toNat

/-- The bytes of one table: its columns. -/
def tabSz (u : UProg) (t : Fin u.tabs.length) : Nat :=
  ((List.finRange (fieldCount u t)).map (colSz u t)).sum

/-- The bytes of all tables. -/
def tabsSz (u : UProg) : Nat := ((List.finRange u.tabs.length).map (tabSz u)).sum

def layU (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) : Lay (declOf u) where
  ga g := b + 8 * g.val
  col t f := b + 8 * u.globs.length + (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum +
    (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum
  lo := b
  hi := b + 8 * u.globs.length + tabsSz u
  tor := tor
  byte t := (List.finRange (fieldCount u t)).find? (fun f => decide ((declOf u).typ t f = .int 0 255))
  lk L := b + 8 * u.globs.length + tabsSz u + 24 * L.val
  sye := b + 8 * u.globs.length + tabsSz u + 24 * u.locks.length

/-- The words of the locks after the tables, three each. -/
theorem layU_sync (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) : LaySync (layU u tor b) := by
  refine ⟨fun Lk => ?_, fun Lk Lk' hne => ?_⟩
  · have := Lk.isLt; simp only [layU]; omega
  · have : Lk.val ≠ Lk'.val := fun h => hne (Fin.ext h)
    simp only [layU]; omega

/-- A part of a sum and the next summand lie inside the sum. -/
theorem take_sum_add (xs : List Nat) (i : Nat) (hi : i < xs.length) : (xs.take i).sum + xs[i] ≤ xs.sum := by
  have h := List.take_append_drop (i + 1) xs
  have e : (xs.take (i + 1)).sum = (xs.take i).sum + xs[i] := by
    rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem hi]; simp
  have : (xs.take (i + 1)).sum ≤ xs.sum := by
    conv => rhs; rw [← h]
    rw [List.sum_append]; omega
  omega

theorem colSz_ge (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Nat)
    (hk : (k : Int) < (declOf u).count t) : 8 * k + 8 ≤ colSz u t f := by
  unfold colSz
  have hk' : k < ((declOf u).count t).toNat := by omega
  omega

theorem col_le (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) :
    (layU u tor b).col t f + colSz u t f ≤ (layU u tor b).hi := by
  simp only [layU, tabsSz]
  have h1 := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val (by simp)
  have h2 := take_sum_add ((List.finRange u.tabs.length).map (tabSz u)) t.val (by simp)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta] at h1 h2
  have : (((List.finRange (fieldCount u t)).map (colSz u t))).sum = tabSz u t := rfl
  omega

/-- The layout keeps every element and every global inside the world, once the world ends below `2^31`. -/
theorem layU_in (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) (h : (layU u tor b).hi < 2 ^ 31) : LayIn (layU u tor b) := by
  refine ⟨fun t f k hk => ?_, fun g => ?_, h⟩
  · have h1 := colSz_ge u t f k hk
    have h2 := col_le u tor b t f
    simp only [Lay.elem]
    constructor
    · simp only [layU]; omega
    · omega
  · have := g.isLt
    simp only [layU, tabsSz]
    omega

/-! ## No two cells share a word -/

theorem take_sum_mono : (xs : List Nat) → (i j : Nat) → i ≤ j → (xs.take i).sum ≤ (xs.take j).sum
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | _ :: _, _ + 1, 0, h => by omega
  | x :: xs, i + 1, j + 1, h => by
    simp only [List.take_succ_cons, List.sum_cons]
    have := take_sum_mono xs i j (by omega)
    omega

theorem take_sum_lt (xs : List Nat) (i j : Nat) (hij : i < j) (hi : i < xs.length) :
    (xs.take i).sum + xs[i] ≤ (xs.take j).sum := by
  have e : (xs.take (i + 1)).sum = (xs.take i).sum + xs[i] := by
    rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem hi]; simp
  have := take_sum_mono xs (i + 1) j hij
  omega

/-- A number in the stretch of summand `i` and in the stretch of summand `j`: `i = j`. -/
theorem stretch_eq (xs : List Nat) (i j x : Nat) (hi : i < xs.length) (hj : j < xs.length)
    (h1 : (xs.take i).sum ≤ x) (h2 : x < (xs.take i).sum + xs[i])
    (h3 : (xs.take j).sum ≤ x) (h4 : x < (xs.take j).sum + xs[j]) : i = j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := take_sum_lt xs i j h hi; omega
  · exact h
  · have := take_sum_lt xs j i h hj; omega

theorem sum_mul8 : (xs : List Nat) → (∀ x ∈ xs, x % 8 = 0) → xs.sum % 8 = 0
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.sum_cons]
    have := h x (by simp)
    have := sum_mul8 xs (fun y hy => h y (by simp [hy]))
    omega

theorem take_mul8 (xs : List Nat) (h : ∀ x ∈ xs, x % 8 = 0) (i : Nat) : (xs.take i).sum % 8 = 0 :=
  sum_mul8 _ (fun x hx => h x (List.mem_of_mem_take hx))

theorem tabSz_mul8 (u : UProg) (t : Fin u.tabs.length) : tabSz u t % 8 = 0 :=
  sum_mul8 _ (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨f, _, rfl⟩ := hx
    simp only [colSz]; omega)

/-- The offset of element `k` of column `f` inside its table lies in the table. -/
theorem in_tab (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Nat)
    (hk : (k : Int) < (declOf u).count t) :
    (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum + 8 * k < tabSz u t := by
  have h1 := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val (by simp)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta] at h1
  have := colSz_ge u t f k hk
  have e : (((List.finRange (fieldCount u t)).map (colSz u t))).sum = tabSz u t := rfl
  omega

theorem layU_dis (u : UProg) (tor : (declOf u).Ax → Option TorB) (b : Nat) : LayDis (layU u tor b) := by
  refine ⟨fun c c' hc hc' he => ?_, fun c hc => ?_⟩
  · cases c with
    | glob g =>
      cases c' with
      | glob g' =>
        simp only [Zelle.adr, layU] at he
        congr 1; exact Fin.ext (by omega)
      | elem t' f' k' =>
        exfalso
        have := g.isLt
        simp only [Zelle.adr, Lay.elem, layU] at he
        omega
    | elem t f k =>
      cases c' with
      | glob g' =>
        exfalso
        have := g'.isLt
        simp only [Zelle.adr, Lay.elem, layU] at he
        omega
      | elem t' f' k' =>
        simp only [Zelle.da] at hc hc'
        simp only [Zelle.adr, Lay.elem, layU] at he
        have it := in_tab u t f k hc
        have it' := in_tab u t' f' k' hc'
        have gx : ∀ (s : Fin u.tabs.length),
            ((List.finRange u.tabs.length).map (tabSz u))[s.val]'(by simp) = tabSz u s := fun s => by simp
        have lx : ∀ (s : Fin u.tabs.length), s.val < ((List.finRange u.tabs.length).map (tabSz u)).length :=
          fun s => by simp
        have htt : t.val = t'.val := stretch_eq _ t.val t'.val
          ((((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum +
            (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum + 8 * k)
          (lx t) (lx t') (by omega) (by rw [gx t]; omega) (by omega) (by rw [gx t']; omega)
        have ht : t = t' := Fin.ext htt
        subst ht
        have gy : ∀ (s : Fin (fieldCount u t)),
            ((List.finRange (fieldCount u t)).map (colSz u t))[s.val]'(by simp) = colSz u t s := fun s => by simp
        have ly : ∀ (s : Fin (fieldCount u t)), s.val < ((List.finRange (fieldCount u t)).map (colSz u t)).length :=
          fun s => by simp
        have c1 := colSz_ge u t f k hc
        have c2 := colSz_ge u t f' k' hc'
        have hff : f.val = f'.val := stretch_eq _ f.val f'.val
          ((((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum + 8 * k)
          (ly f) (ly f') (by omega) (by rw [gy f]; omega) (by omega) (by rw [gy f']; omega)
        have hf : f = f' := Fin.ext hff
        subst hf
        have : k = k' := by omega
        subst this
        rfl
  · cases c with
    | glob g => simp only [Zelle.adr, layU]; omega
    | elem t f k =>
      simp only [Zelle.adr, Lay.elem, layU]
      have h1 := take_mul8 ((List.finRange u.tabs.length).map (tabSz u)) (fun x hx => by
        simp only [List.mem_map] at hx; obtain ⟨s, _, rfl⟩ := hx; exact tabSz_mul8 u s) t.val
      have h2 := take_mul8 ((List.finRange (fieldCount u t)).map (colSz u t)) (fun x hx => by
        simp only [List.mem_map] at hx; obtain ⟨s, _, rfl⟩ := hx; simp only [colSz]; omega) f.val
      omega

/-- **The program theorem for an elaborated program** (`stage0 --ir`): the image of `bild` with the world laid out
    by `layU`, under the named assumption at the gates (`TorOK`); what is left is that the image's memory holds the start
    world. -/
theorem bild_ok_u [CloneOK] {u : UProg} {P : Programm (declOf u)} {O : Orakel (declOf u)} {passes : Nat}
    {fs : List (declOf u).Fn} {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {roots : List (declOf u).Fn} {Ks : Nat} {b : Bild (declOf u)}
    {tor : (declOf u).Ax → Option TorB} (hb : bild P (layU u tor) fs pos name main roots Ks = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (σ : World (declOf u))
    (ρ : Env (declOf u) ((declOf u).params main)) (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O passes b.depth main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = 231 ∧ EncErg ((declOf u).erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (hwCode h)
    | _ => False := by
  have h := bild_ok (O := O) (passes := passes) hb hfs (fun x h => layU_in u tor x h) (fun x => layU_dis u tor x)
    (fun x => by simp only [layU]; omega) (fun x => layU_sync u tor x) hm σ ρ hWa hT hV
  generalize rufAt P O passes b.depth main σ ρ = o at h ⊢
  cases o <;> exact h

/-- **The thread of root `j`** of an elaborated program, on its own stack. -/
theorem bild_wurzel_ok_u {u : UProg} {P : Programm (declOf u)} {O : Orakel (declOf u)} {passes : Nat}
    {fs : List (declOf u).Fn} {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {roots : List (declOf u).Fn} {Ks : Nat} {b : Bild (declOf u)}
    {tor : (declOf u).Ax → Option TorB} (hb : bild P (layU u tor) fs pos name main roots Ks = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (j : Nat)
    (hj : j < roots.length) (σ : World (declOf u)) (ρ : Env (declOf u) ((declOf u).params roots[j]))
    (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O passes b.depth roots[j] σ ρ with
    | .ok _ _ => ∃ t' m' q, Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  have h := bild_wurzel_ok (O := O) (passes := passes) hb hfs (fun x h => layU_in u tor x h)
    (fun x => layU_dis u tor x) (fun x => by simp only [layU]; omega) (fun x => layU_sync u tor x) hm j hj σ ρ hWa hT hV
  generalize rufAt P O passes b.depth roots[j] σ ρ = o at h ⊢
  cases o <;> exact h

end Gabbro.Stage0.Senke
