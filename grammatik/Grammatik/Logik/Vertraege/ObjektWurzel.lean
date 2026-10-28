/-
  File:      Grammatik/Logik/Vertraege/ObjektWurzel.lean
  Subject:   **ROOTS AND OBJECTS** -- the soundness bridge for the checker rule `R014`
             (`m3.rs::getrennte_wurzeln`, sentence `m3.zeiger_wurzel`) at the level the
             object layer (`Objekte.lean`, `ObjektRahmen.lean`) can state.

  THE PROVENANCE, AS THE CHECKER COMPUTES IT (`dokumente/A1-OWN-PAPER.md` section 5). A
  pointer name in a body has a provenance `Herkunft`:
    * `param i`   -- the caller's own pointer parameter `i` (its own root);
    * `frisch n`  -- the answer of a call that takes no pointer argument (a fresh object;
                     the checker names it `#v` after its `let`);
    * `umsicht h` -- the answer of a re-view (a call taking a pointer and answering one),
                     whose pointer argument had provenance `h`: it BORROWS (section 4);
    * `vereint h h'` -- the union: a re-view over two pointer arguments, or a name bound
                     twice (the walk over `let`s is flat);
    * `unbekannt` -- anything else (a field, an index, a static, an unresolved call).
  Its roots (`Herkunft.wurzeln`) are the paper's: a re-view has its argument's roots, a
  union both, and `unbekannt` counts as EVERY root ("`unknown` counts as a root equal to
  every other root"). `R014` at a call is `R014Rein`: two positions with a writable side
  have disjoint roots.

  WHAT A PROVENANCE MEANS (`Bedeutet`), under the model's allocation discipline:
  parameter `i` names `pObj i`, fresh answer `n` names `fObj n`, a re-view names the
  object of its argument (`umsicht_behaelt`, ObjektRahmen.lean: a theorem of the model),
  a union one of the two, and `unbekannt` any object.

  WHAT IS PROVED. **`r014_objGetrennt`**: roots pairwise disjoint at a call implies
  `ObjGetrennt` of the argument-to-object map, under four NAMED hypotheses and nothing
  else:
    * `ParamVerschieden` -- the caller's own parameters with a writable side name distinct
      objects. This IS the inherited precondition S-2: inside a unit it is what
      `r014_objGetrennt` concludes one frame up; at a function entered from outside it is
      the BOUNDARY ASSUMPTION `R015` names. It is a hypothesis here, never discharged.
    * `FrischNeu` -- fresh answers are new objects: distinct from each other and from every
      parameter's object. For answers of the model's allocator it is a theorem
      (`frischNeu_aus_arena`, over `ArenaDyn.freiAlloc`); for the answer of a FOREIGN function
      with no pointer argument it is the binding's contract (user logic, not checked here).
    * `RechteOk` -- a writable parameter is handed a writable root (the checker's `R002`/
      `R003`: no `w` without the right).
    * `HerkunftTreu` -- every argument names an object its provenance denotes: a re-view
      keeps its argument's object (in the model: `umsicht_behaelt`; for a foreign re-view:
      the binding's contract), a fresh answer is its fresh object. The correctness of the
      checker's walk over `let`s is part of it and is NOT formalised over G syntax.
  `r014_ruf_rahmen` composes it with `obj_ruf_rahmen`: an `R014`-clean call into a body that
  keeps the object discipline leaves every read-only parameter's object unchanged.

  WHAT THE CHECKER DOES DIFFERENTLY (a finding, measured): `getrennte_wurzeln` gives a name
  it cannot trace NO root and skips every pair with it (`let (Some(wa), Some(wb)) = … else
  { continue }`), and gives a re-view whose pointer argument has no root a FRESH root. The
  paper rule counts it as every root. `rust_lesart_luecke` proves the Rust reading unsound
  in the model: under all four hypotheses, an untraced name and a parameter are "separated"
  while naming ONE object. Measured on the binary of 2026-10-17: a re-view through a
  function pointer (`let w = v.s(k); aendern(k, w);`) passes with 0 errors.
-/
import Grammatik.Logik.Vertraege.ObjektRahmen
import Grammatik.Bausteine.Arena.ArenaDyn

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Provenance and roots -/

/-- A root: one of the caller's pointer parameters, or one fresh answer. -/
inductive Wurzel where
  | param (i : Nat)
  | frisch (n : Nat)
  deriving DecidableEq

/-- The provenance of a pointer name, as the checker computes it. -/
inductive Herkunft where
  | param (i : Nat)
  | frisch (n : Nat)
  | umsicht (h : Herkunft)
  | vereint (h h' : Herkunft)
  | unbekannt

/-- **The roots of a provenance** (the paper's rule): a re-view borrows its argument's roots,
    a union has both, and an untraced name counts as every root. -/
def Herkunft.wurzeln : Herkunft → Wurzel → Prop
  | .param i, r => r = .param i
  | .frisch n, r => r = .frisch n
  | .umsicht h, r => h.wurzeln r
  | .vereint h h', r => h.wurzeln r ∨ h'.wurzeln r
  | .unbekannt, _ => True

/-- Every provenance has a root. -/
theorem Herkunft.wurzeln_nichtleer : ∀ h : Herkunft, ∃ r, h.wurzeln r
  | .param i => ⟨.param i, rfl⟩
  | .frisch n => ⟨.frisch n, rfl⟩
  | .umsicht h => h.wurzeln_nichtleer
  | .vereint h _ => let ⟨r, hr⟩ := h.wurzeln_nichtleer; ⟨r, .inl hr⟩
  | .unbekannt => ⟨.param 0, trivial⟩

/-- Two provenances with disjoint roots. -/
def WurzelGetrennt (h h' : Herkunft) : Prop := ∀ r, ¬ (h.wurzeln r ∧ h'.wurzeln r)

/-- **`R014` at a call**: every two argument positions with a writable side have disjoint
    roots. Two positions holding the SAME name have the same provenance and are never
    disjoint, so `R004`/`R007` ("the same place") are the special case. -/
def R014Rein {n : Nat} (w : Fin n → Bool) (a : Fin n → Herkunft) : Prop :=
  ∀ k l, k ≠ l → (w k || w l) = true → WurzelGetrennt (a k) (a l)

/-! ## 2. What a provenance means -/

/-- The object of a root: a parameter's object, or a fresh answer's. -/
def wurzelObj (pObj fObj : Nat → Obj D) : Wurzel → Obj D
  | .param i => pObj i
  | .frisch n => fObj n

/-- **What a provenance denotes**: the objects a name with that provenance can point at. A
    re-view denotes its argument's object (`umsicht_behaelt`). -/
def Bedeutet (pObj fObj : Nat → Obj D) : Herkunft → Obj D → Prop
  | .param i, o => o = pObj i
  | .frisch n, o => o = fObj n
  | .umsicht h, o => Bedeutet pObj fObj h o
  | .vereint h h', o => Bedeutet pObj fObj h o ∨ Bedeutet pObj fObj h' o
  | .unbekannt, _ => True

/-- A denoted object is the object of one of its roots -- or the provenance has every root. -/
theorem bedeutet_wurzel (pObj fObj : Nat → Obj D) :
    ∀ (h : Herkunft) (o : Obj D), Bedeutet pObj fObj h o →
      (∃ r, h.wurzeln r ∧ wurzelObj pObj fObj r = o) ∨ (∀ r, h.wurzeln r)
  | .param i, o, hb => .inl ⟨.param i, rfl, hb.symm⟩
  | .frisch n, o, hb => .inl ⟨.frisch n, rfl, hb.symm⟩
  | .umsicht h, o, hb => bedeutet_wurzel pObj fObj h o hb
  | .vereint h h', o, hb => by
      rcases hb with hb | hb
      · rcases bedeutet_wurzel pObj fObj h o hb with ⟨r, hr, ho⟩ | ha
        · exact .inl ⟨r, .inl hr, ho⟩
        · exact .inr fun r => .inl (ha r)
      · rcases bedeutet_wurzel pObj fObj h' o hb with ⟨r, hr, ho⟩ | ha
        · exact .inl ⟨r, .inr hr, ho⟩
        · exact .inr fun r => .inr (ha r)
  | .unbekannt, _, _ => .inr fun _ => trivial

/-! ## 3. The four named hypotheses -/

/-- **S-2, the inherited precondition** (at a function entered from outside: the boundary
    assumption `R015`): the caller's own parameters with a writable side name distinct
    objects. `wp i`: parameter `i` is writable or `own`. -/
def ParamVerschieden (wp : Nat → Bool) (pObj : Nat → Obj D) : Prop :=
  ∀ i j, i ≠ j → (wp i || wp j) = true → pObj i ≠ pObj j

/-- **The allocation discipline**: fresh answers are new objects -- pairwise distinct and
    distinct from every parameter's object. -/
def FrischNeu (pObj fObj : Nat → Obj D) : Prop :=
  (∀ n m, n ≠ m → fObj n ≠ fObj m) ∧ (∀ n i, fObj n ≠ pObj i)

/-- **The provenance is faithful** (the fourth premise, the denotation): every argument
    names an object its provenance denotes. For a re-view whose body is in the model it is
    the theorem `umsicht_behaelt`; for a FOREIGN re-view (an `extern fn (ptr A) -> ptr B`) and
    a foreign fresh answer it is the binding's contract; for the walk over `let`s it is the
    correctness of the checker's provenance computation, which is not formalised over G
    syntax here. -/
def HerkunftTreu {n : Nat} (pObj fObj : Nat → Obj D) (a : Fin n → Herkunft)
    (ao : Fin n → Option (Obj D)) : Prop :=
  ∀ k o, ao k = some o → Bedeutet pObj fObj (a k) o

/-- **The right of a root**: every parameter root of `h` is a writable parameter. -/
def RechteOk (wp : Nat → Bool) (h : Herkunft) : Prop := ∀ i, h.wurzeln (.param i) → wp i = true

theorem wurzelObj_inj {wp : Nat → Bool} {pObj fObj : Nat → Obj D} (hS : ParamVerschieden wp pObj)
    (hF : FrischNeu pObj fObj) {r r' : Wurzel} (hrr : r ≠ r')
    (hw : ∀ i j, r = .param i → r' = .param j → (wp i || wp j) = true) :
    wurzelObj pObj fObj r ≠ wurzelObj pObj fObj r' := by
  cases r with
  | param i =>
      cases r' with
      | param j =>
          exact hS i j (fun h => hrr (by rw [h])) (hw i j rfl rfl)
      | frisch m => exact fun h => hF.2 m i h.symm
  | frisch n =>
      cases r' with
      | param j => exact hF.2 n j
      | frisch m => exact hF.1 n m (fun h => hrr (by rw [h]))

/-! ## 4. THE BRIDGE: distinct roots give distinct objects -/

/-- **Two names with disjoint roots name two objects** -- one of them writable-rooted (`hR`),
    under S-2 and the allocation discipline. -/
theorem wurzel_getrennt_obj {wp : Nat → Bool} {pObj fObj : Nat → Obj D}
    (hS : ParamVerschieden wp pObj) (hF : FrischNeu pObj fObj) {h h' : Herkunft}
    (hG : WurzelGetrennt h h') (hR : RechteOk wp h) {o o' : Obj D}
    (hb : Bedeutet pObj fObj h o) (hb' : Bedeutet pObj fObj h' o') : o ≠ o' := by
  rcases bedeutet_wurzel pObj fObj h o hb with ⟨r, hr, ho⟩ | ha
  · rcases bedeutet_wurzel pObj fObj h' o' hb' with ⟨r', hr', ho'⟩ | ha'
    · have hrr : r ≠ r' := fun e => hG r ⟨hr, e ▸ hr'⟩
      rw [← ho, ← ho']
      refine wurzelObj_inj hS hF hrr ?_
      intro i j hi _
      subst hi
      simp only [hR i hr, Bool.true_or]
    · exact absurd ⟨hr, ha' r⟩ (hG r)
  · obtain ⟨r', hr'⟩ := h'.wurzeln_nichtleer
    exact absurd ⟨ha r', hr'⟩ (hG r')

/-- **THE SOUNDNESS BRIDGE FOR `R014`.** At a call whose argument positions are
    `R014`-clean (`R014Rein`), whose writable positions are handed writable roots
    (`RechteOk`), and whose arguments name the objects their provenance denotes
    (`HerkunftTreu` -- a re-view keeps the object, `umsicht_behaelt`), the argument-to-object
    map is `ObjGetrennt` -- under S-2 / `R015` (`ParamVerschieden`) and the allocation
    discipline (`FrischNeu`). All four premises are named; none is discharged here. -/
theorem r014_objGetrennt {n : Nat} (w : Fin n → Bool) (a : Fin n → Herkunft)
    (ao : Fin n → Option (Obj D)) (wp : Nat → Bool) (pObj fObj : Nat → Obj D)
    (hS : ParamVerschieden wp pObj) (hF : FrischNeu pObj fObj)
    (hB : HerkunftTreu pObj fObj a ao)
    (hRe : ∀ k, w k = true → RechteOk wp (a k)) (h014 : R014Rein w a) :
    ObjGetrenntL w ao := by
  intro k l hkl hz
  cases hk : ao k with
  | none => exact .inl rfl
  | some o =>
      right
      intro e
      have hl : ao l = some o := e.symm
      have hG := h014 k l hkl hz
      cases hwk : w k
      · have hwl : w l = true := by rw [hwk] at hz; simpa using hz
        have hG' : WurzelGetrennt (a l) (a k) := fun r h => hG r ⟨h.2, h.1⟩
        exact wurzel_getrennt_obj hS hF hG' (hRe l hwl) (hB l o hl) (hB k o hk) rfl
      · exact wurzel_getrennt_obj hS hF hG (hRe k hwk) (hB k o hk) (hB l o hl) rfl

/-- **`R014` at the model's call.** An `R014`-clean call (under the four named hypotheses)
    into a body that keeps the object discipline: every run leaves every field of the
    object of every read-only object parameter as it was. -/
theorem r014_ruf_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : TreuO O)
    (objs : D.Fn → List (ObjPar D)) (hP : ProgObjOk objs P) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) (σ' : World D)
    (h : (rufAt P O passes fuel f σ ρ).welt = some σ')
    (a : Fin (objs f).length → Herkunft) (wp : Nat → Bool) (pObj fObj : Nat → Obj D)
    (hS : ParamVerschieden wp pObj) (hF : FrischNeu pObj fObj)
    (hB : HerkunftTreu pObj fObj a (objVon (objs f) ρ))
    (hRe : ∀ k, rwVon (objs f) k = true → RechteOk wp (a k)) (h014 : R014Rein (rwVon (objs f)) a)
    (i : Fin (objs f).length) (hi : ((objs f).get i).rw = false)
    {o : Obj D} (ho : objVon (objs f) ρ i = some o) :
    ∀ fld : D.Feld o.tab, σ'.slots o.tab o.nr fld = σ.slots o.tab o.nr fld :=
  obj_ruf_rahmen P O passes fuel hO objs hP f σ ρ σ' h
    (r014_objGetrennt _ a _ wp pObj fObj hS hF hB hRe h014) i hi ho

/-! ## 5. The allocation discipline, for the model's allocator -/

namespace ArenaDyn

/-- A slot is live: allocated (below the high-water mark) and not on the free list. -/
def FreiZustand.lebt (F : FreiZustand) (i : Nat) : Prop := i < F.belegt ∧ i ∉ F.frei

/-- **A fresh slot is not a live one.** -/
theorem freiAlloc_neu (F : FreiZustand) (i : Nat) (hi : F.lebt i) : (freiAlloc F).1 ≠ i := by
  obtain ⟨belegt, frei, hfrei⟩ := F
  cases frei with
  | nil => simp only [freiAlloc]; exact fun h => by have := hi.1; simp only at this; omega
  | cons j rest =>
      simp only [freiAlloc]
      intro h; subst h
      exact hi.2 List.mem_cons_self

/-- A live slot stays live through an allocation. -/
theorem freiAlloc_bleibt (F : FreiZustand) (i : Nat) (hi : F.lebt i) : (freiAlloc F).2.lebt i := by
  obtain ⟨belegt, frei, hfrei⟩ := F
  cases frei with
  | nil => exact ⟨by simp only [freiAlloc]; have := hi.1; simp only at this; omega, by simp only [freiAlloc, List.not_mem_nil, not_false_eq_true]⟩
  | cons j rest =>
      refine ⟨hi.1, ?_⟩
      simp only [freiAlloc]
      exact fun h => hi.2 (List.mem_cons_of_mem _ h)

/-- The fresh slot is live afterwards (on a duplicate-free free list). -/
theorem freiAlloc_lebt (F : FreiZustand) (hnd : F.frei.Nodup) : (freiAlloc F).2.lebt (freiAlloc F).1 := by
  obtain ⟨belegt, frei, hfrei⟩ := F
  cases frei with
  | nil => exact ⟨by simp only [freiAlloc, Nat.lt_add_one], by simp only [freiAlloc, List.not_mem_nil, not_false_eq_true]⟩
  | cons j rest =>
      refine ⟨hfrei j List.mem_cons_self, ?_⟩
      simp only [freiAlloc]
      exact (List.nodup_cons.mp hnd).1

theorem freiAlloc_nodup (F : FreiZustand) (hnd : F.frei.Nodup) : (freiAlloc F).2.frei.Nodup := by
  obtain ⟨belegt, frei, hfrei⟩ := F
  cases frei with
  | nil => simp only [freiAlloc, List.nodup_nil]
  | cons j rest => simp only [freiAlloc]; exact (List.nodup_cons.mp hnd).2

/-- `free` keeps the free list duplicate-free (it refuses a slot already on it). -/
theorem freiFree_nodup (F : FreiZustand) (hnd : F.frei.Nodup) (i : Nat) (G : FreiZustand)
    (hg : freiFree F i = some G) : G.frei.Nodup := by
  unfold freiFree at hg
  split at hg
  · rename_i h
    cases hg
    exact List.nodup_cons.mpr ⟨h.2, hnd⟩
  · cases hg

/-- The `n`-th answer of a run of allocations from `F` (nothing freed in between). -/
def allocStrom : FreiZustand → Nat → Nat
  | F, 0 => (freiAlloc F).1
  | F, n + 1 => allocStrom (freiAlloc F).2 n

/-- No answer of the run is a slot that was live before it. -/
theorem allocStrom_neu : ∀ (n : Nat) (F : FreiZustand), F.frei.Nodup →
    ∀ i, F.lebt i → allocStrom F n ≠ i
  | 0, F, _, i, hi => freiAlloc_neu F i hi
  | n + 1, F, hnd, i, hi =>
      allocStrom_neu n (freiAlloc F).2 (freiAlloc_nodup F hnd) i (freiAlloc_bleibt F i hi)

/-- **Fresh answers are new objects**: two different answers of the run are two slots. -/
theorem allocStrom_inj : ∀ (n m : Nat) (F : FreiZustand), F.frei.Nodup → n ≠ m →
    allocStrom F n ≠ allocStrom F m
  | 0, 0, _, _, h => absurd rfl h
  | 0, m + 1, F, hnd, _ => fun e =>
      allocStrom_neu m (freiAlloc F).2 (freiAlloc_nodup F hnd) _ (freiAlloc_lebt F hnd) e.symm
  | n + 1, 0, F, hnd, _ => fun e =>
      allocStrom_neu n (freiAlloc F).2 (freiAlloc_nodup F hnd) _ (freiAlloc_lebt F hnd) e
  | n + 1, m + 1, F, hnd, h =>
      allocStrom_inj n m (freiAlloc F).2 (freiAlloc_nodup F hnd) (fun e => h (by rw [e]))

end ArenaDyn

/-- **`FrischNeu` from the allocator**, for parameters and fresh answers in one table `t`:
    if every parameter's object is a live slot of the allocator state `F` and the fresh
    answers are the run of allocations from `F`, the allocation discipline holds. -/
theorem frischNeu_aus_arena (t : D.Tab) (F : ArenaDyn.FreiZustand) (hnd : F.frei.Nodup)
    (pNr : Nat → Nat) (hp : ∀ i, F.lebt (pNr i)) :
    FrischNeu (fun i => (⟨t, pNr i⟩ : Obj D)) (fun n => ⟨t, ArenaDyn.allocStrom F n⟩) := by
  refine ⟨?_, ?_⟩
  · intro n m hnm e
    simp only [Obj.mk.injEq, true_and] at e
    exact ArenaDyn.allocStrom_inj n m F hnd hnm (by exact_mod_cast e)
  · intro n i e
    simp only [Obj.mk.injEq, true_and] at e
    exact ArenaDyn.allocStrom_neu n F hnd (pNr i) (hp i) (by exact_mod_cast e)

/-! ## 6. The checker's own reading: untraced names are skipped -/

/-- **The roots as `getrennte_wurzeln` computes them**: an untraced name has NO root (the pair
    is then skipped), and a re-view whose argument has no root is a fresh object `#v`. -/
def Herkunft.wurzelnR : Herkunft → Wurzel → Prop
  | .param i, r => r = .param i
  | .frisch n, r => r = .frisch n
  | .umsicht h, r => h.wurzelnR r
  | .vereint h h', r => h.wurzelnR r ∨ h'.wurzelnR r
  | .unbekannt, _ => False

/-- **The finding, in the model**: under ALL four named hypotheses (`RechteOk` holds with every
    parameter writable, `HerkunftTreu` is the two `Bedeutet` conjuncts), the checker's reading
    calls an untraced name and a parameter separated (no common root) while both name ONE
    object -- so the bridge `r014_objGetrennt` does NOT hold for the reading the Rust code
    implements; it holds for the paper's (`Herkunft.wurzeln`). -/
theorem rust_lesart_luecke (o : Obj D) :
    let pObj : Nat → Obj D := fun i => ⟨o.tab, o.nr + i⟩
    let fObj : Nat → Obj D := fun n => ⟨o.tab, o.nr - 1 - n⟩
    ParamVerschieden (fun _ => true) pObj ∧ FrischNeu pObj fObj ∧
      (∀ r, ¬ ((Herkunft.unbekannt).wurzelnR r ∧ (Herkunft.param 0).wurzelnR r)) ∧
      Bedeutet pObj fObj .unbekannt o ∧ Bedeutet pObj fObj (.param 0) o ∧
      ¬ WurzelGetrennt .unbekannt (.param 0) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_, trivial, ?_, ?_⟩
  · intro i j hij _ e
    simp only [Obj.mk.injEq, true_and] at e
    omega
  · intro n m hnm e
    simp only [Obj.mk.injEq, true_and] at e
    omega
  · intro n i e
    simp only [Obj.mk.injEq, true_and] at e
    omega
  · intro r h; exact h.1
  · show o = ⟨o.tab, o.nr + (0 : Nat)⟩
    exact Obj.ext' rfl (by simp only [Int.cast_ofNat_Int, Int.add_zero])
  · intro h; exact h (.param 0) ⟨trivial, rfl⟩

#print axioms Gabbro.Grammatik.wurzel_getrennt_obj
#print axioms Gabbro.Grammatik.r014_objGetrennt
#print axioms Gabbro.Grammatik.r014_ruf_rahmen
#print axioms Gabbro.Grammatik.ArenaDyn.allocStrom_inj
#print axioms Gabbro.Grammatik.frischNeu_aus_arena
#print axioms Gabbro.Grammatik.rust_lesart_luecke

end Gabbro.Grammatik
