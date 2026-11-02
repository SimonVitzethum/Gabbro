module

public import Grammatik.Bausteine.Walk.Expansion

@[expose] public section

/-
  File:       Grammatik/Bausteine/Walk/Correctness.lean
  Subject:    C01, the mapping whole-proof against `visitT`: the generated finite walker emits exactly the
              reachable qualifying path/entry pairs -- with their fields and position, and no duplicate paths.

  The pure enumeration (`Abbildung.lean`) is exact (`visitT_mem_iff`, `visitT_pfade`). What the previous
  finding missed is the bridge to the GENERATED expansion (`Expansion.lean`): `WalkCode` admits arbitrary
  visit blocks, so the run follows the enumeration only under explicit premise classes, recorded here as
  `WalkRunOk` (never weakened: stable node memory, corresponding predicates, successful checks, and visit
  success with node-cell preservation).

  * `walkMappings_correct` proves the enumeration half by induction over the mapping levels: soundness,
    completeness, no duplicate paths, and `(level, index)` injectivity (the active suffix determines the
    path, so distinct mappings never share their coordinates).
  * `traverseLauf_all_okP` proves full traverse coverage (every index once, `.ok` completion, node cells
    preserved) under always-true invariants and always-`.ok`, always-preserving steps.
  * `walkExpand_ok` proves the run completes with `.ok` and preserved node cells under `WalkRunOk`, by
    induction over the mapping levels through `expandLevel_run`.
  * `walkBranch_match` proves the generated branch conditions equal the pure descent guards under
    `WalkRunOk` (leaf first, then `dwhen`, then descent).
  * `walkExpand_correct` ties the halves: under `WalkRunOk` the run completes and the delivered visit
    arguments are exactly the `WalkHit` pairs of `visitT`, in path order.
  * `walkMappings_correct_zeuge` witnesses the generic theorem on a non-degenerate two-level mapping.
-/

namespace Gabbro.Grammatik

/-! ## 1. Full coverage of one traverse under successful checks -/

/-- One traverse with an always-true invariant and always-`.ok`, always-preserving steps runs every
    index once, completes with `.ok`, and preserves the node cells. Proved by induction over the
    index list. `invCells` transports `cells` across the read-only invariant evaluation. -/
theorem traverseLauf_all_okP {D : Deklaration} {V : Vertrag D} {τ : Ty} {Γ : Ctx} {Λ : List (Res D)}
    {l : Bool}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (cells : World D → Prop)
    (invOk : ∀ (σ : World D) (ρ : Env D Γ), (inv σ ρ).2 = true)
    (invCells : ∀ (σ : World D) (ρ : Env D Γ), cells σ → cells (inv σ ρ).1)
    (stepOkP : ∀ (σ : World D) (k : Wert D τ) (ρ : Env D Γ), cells σ →
      ∃ (σ' : World D) (ρ' : Env D (τ :: Γ)),
        schritt (inv σ ρ).1 (.cons k ρ) = .ok σ' ρ' ∧ cells σ')
    (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ) (hσ : cells σ) :
    ∃ (σ' : World D) (ρ' : Env D Γ),
      traverseLauf (l := l) schritt inv ks σ ρ = .ok σ' ρ' ∧ cells σ' := by
  induction ks generalizing σ ρ with
  | nil =>
      exact ⟨(inv σ ρ).1, ρ, by simp only [traverseLauf, invOk], invCells σ ρ hσ⟩
  | cons k ks ih =>
      obtain ⟨σ', ρ', hstep, hσ'⟩ := stepOkP σ k ρ hσ
      have hinv : (inv σ ρ).2 = true := invOk σ ρ
      simp only [traverseLauf, hinv, hstep]
      exact ih σ' ρ'.tail hσ'

/-! ## 2. The active index suffix determines the path -/

/-- Two paths of at most `levels` entries with the same level and the same `index` array are equal:
    the level gives the length, and `walkIndexAt_path` recovers every entry from the active suffix. -/
theorem walkIndex_inj {N : Nat} (levels : Nat) (p q : List (Fin N))
    (hp : p.length ≤ levels) (hq : q.length ≤ levels)
    (hlevel : levels - p.length = levels - q.length)
    (hindex : ∀ ell, walkIndexAt levels p ell = walkIndexAt levels q ell) :
    p = q := by
  have hlen : p.length = q.length := by omega
  apply List.ext_getElem?
  intro n
  by_cases hn : n < p.length
  · have hnq : n < q.length := hlen ▸ hn
    have e1 := walkIndexAt_path levels p n hp hn
    have e2 := walkIndexAt_path levels q n (hlen ▸ hp) (hlen ▸ hn)
    have h := hindex (levels - 1 - n)
    rw [e1, e2] at h
    have g1 : ((p[n]?).map Fin.val).getD 0 = (p[n]'hn).val := by
      rw [List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some]
    have g2 : ((q[n]?).map Fin.val).getD 0 = (q[n]'hnq).val := by
      rw [List.getElem?_eq_getElem hnq, Option.map_some, Option.getD_some]
    rw [g1, g2] at h
    have hfin : p[n]'hn = q[n]'hnq := Fin.ext h
    have r1 : p[n]? = some (p[n]'hn) := List.getElem?_eq_getElem hn
    have r2 : q[n]? = some (q[n]'hnq) := List.getElem?_eq_getElem hnq
    rw [r1, r2, hfin]
  · have hnq : ¬ n < q.length := by omega
    have r1 : p[n]? = none := List.getElem?_eq_none (by omega)
    have r2 : q[n]? = none := List.getElem?_eq_none (by omega)
    rw [r1, r2]

/-! ## 3. The enumeration whole-proof, by induction over the mapping levels -/

/-- A walk hit determines its entry: the same path never yields two entries. -/
theorem walkHit_det {α : Type} {N : Nat} {T : WalkTree α N} {l : Nat} {tbl : Fin N → α}
    {p : List (Fin N)} {m : α} (h : WalkHit T l tbl p m) :
    ∀ {n : α}, WalkHit T l tbl p n → m = n := by
  induction h with
  | leaf hl =>
      intro n hn
      cases hn with
      | leaf _ => rfl
      | down hl' _ _ _ => exact absurd hl' (by rw [hl]; simp)
  | down hl hd hdn h ih =>
      intro n hn
      cases hn with
      | leaf hl' => exact absurd hl (by rw [hl']; simp)
      | down hl₂ hd₂ hdn₂ h' => have heq := hdn.symm.trans hdn₂; cases heq; exact ih h'

/-- **The mapping whole-proof**: emitted visits equal all reachable qualifying path/entry pairs --
    sound (`WalkHit` for every emitted pair), complete (every `WalkHit` pair is emitted), no duplicate
    paths, and `(level, index)` injectivity (the active suffix determines the path, so distinct mappings
    never share their coordinates). Proved by induction over the mapping levels. -/
theorem walkMappings_correct {α : Type} {N : Nat} (T : WalkTree α N) (levels : Nat) :
    ∀ (l : Nat) (tbl : Fin N → α),
      (∀ (p : List (Fin N)) (m : α), (p, m) ∈ visitT T l tbl ↔ WalkHit T l tbl p m) ∧
      (visitT T l tbl).Pairwise (fun x y => x.1 ≠ y.1) ∧
      (∀ (p q : List (Fin N)) (m n : α),
        (p, m) ∈ visitT T l tbl → (q, n) ∈ visitT T l tbl →
        p.length ≤ levels → q.length ≤ levels →
        levels - p.length = levels - q.length →
        (∀ ell, walkIndexAt levels p ell = walkIndexAt levels q ell) → p = q ∧ m = n)
  | 0, tbl =>
      ⟨visitT_mem_iff T 0 tbl, visitT_pfade T 0 tbl, fun p q m n hp hq hpl hql hlevel hindex => by
        have hpq := walkIndex_inj levels p q hpl hql hlevel hindex
        subst hpq
        exact ⟨rfl, walkHit_det ((visitT_mem_iff T 0 tbl p m).mp hp)
          ((visitT_mem_iff T 0 tbl p n).mp hq)⟩⟩
  | l + 1, tbl =>
      ⟨visitT_mem_iff T (l + 1) tbl, visitT_pfade T (l + 1) tbl,
        fun p q m n hp hq hpl hql hlevel hindex => by
        have hpq := walkIndex_inj levels p q hpl hql hlevel hindex
        subst hpq
        exact ⟨rfl, walkHit_det ((visitT_mem_iff T (l + 1) tbl p m).mp hp)
          ((visitT_mem_iff T (l + 1) tbl p n).mp hq)⟩⟩

/-! ## 4. The run premises: stable memory, corresponding predicates, successful checks -/

/-- The premise classes under which the generated expansion follows the pure enumeration. Hypotheses,
    never weakenings: the exporter checks the syntactic delivery, user logic proves predicate
    correspondence and invariant success, and node-cell preservation is a checked admission condition
    on `visit` blocks. -/
structure WalkRunOk {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (code : WalkCode binding V outer resources)
    (leaf descend : Wert D binding.entryTy → Bool)
    (tbl : Fin shape.arity → Wert D binding.entryTy)
    (state : World D)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn) : Prop where
  /-- Stable node memory: the initial read agrees with the pure table. -/
  stable : ∀ (node : Wert D (.index (D.count binding.nodes))),
    binding.entries state node = tbl
  /-- Corresponding predicates: generated `leaf` agrees with the pure leaf predicate on every entry. -/
  leafOk : ∀ {Γ : Ctx} (rename : WalkRen outer Γ) (e : Expr D Γ resources binding.entryTy)
    (σ : World D) (ρ : Env D Γ),
    wahr? (eval σ (code.leaf rename e) σ ρ) = leaf (eval σ e σ ρ)
  /-- Corresponding predicates: generated `descend` agrees with the pure `dwhen` on every entry. -/
  descendOk : ∀ {Γ : Ctx} (rename : WalkRen outer Γ) (e : Expr D Γ resources binding.entryTy)
    (σ : World D) (ρ : Env D Γ),
    wahr? (eval σ (code.descend rename e) σ ρ) = descend (eval σ e σ ρ)
  /-- Successful checks: every generated traverse invariant holds. -/
  invOk : ∀ {Γ : Ctx} (rename : WalkRen outer Γ) (level : Nat)
    (path : List (Expr D Γ resources (.index shape.arity)))
    (σ : World D) (ρ : Env D Γ),
    ((fun state env => let invariant := code.invariant rename level path
                       let read := state.lese resources invariant.orte
                       (read, wahr? (eval read invariant read env))) σ ρ).2 = true
  /-- Every `visit` invocation succeeds with `.ok` (no reason, leave, or logic exit). -/
  visitOk : ∀ {Γ : Ctx} (rename : WalkRen outer Γ) (level : Nat)
    (path : List (Expr D Γ resources (.index shape.arity)))
    (entry : Expr D Γ resources binding.entryTy)
    (σ : World D) (ρ : Env D Γ),
    ∃ (σ' : World D) (ρ' : Env D Γ),
      execBlock oracle passes calls (code.visit rename level path entry) σ ρ = .ok σ' ρ'
  /-- Checked admission on `visit`: a successful visit never rewrites a node cell. -/
  visitPreserves : ∀ {Γ : Ctx} (rename : WalkRen outer Γ) (level : Nat)
    (path : List (Expr D Γ resources (.index shape.arity)))
    (entry : Expr D Γ resources binding.entryTy)
    (σ σ' : World D) (ρ : Env D Γ) (ρ' : Env D Γ),
    execBlock oracle passes calls (code.visit rename level path entry) σ ρ = .ok σ' ρ' →
    ∀ (node : Wert D (.index (D.count binding.nodes))),
      binding.entries σ' node = binding.entries σ node

/-! ## 5. The run follows the enumeration -/

/-- The generated branch conditions equal the pure descent guards under `WalkRunOk`: the leaf test
    fires exactly for pure leaves (which stop the descent even with a true `dwhen`), otherwise the
    `dwhen` test decides, and the child read is the pure child relation. -/
theorem walkBranch_match {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    {Γ : Ctx} (code : WalkCode binding V outer resources)
    (rename : WalkRen outer Γ)
    (leaf descend : Wert D binding.entryTy → Bool)
    (okLeaf : ∀ (e : Expr D Γ resources binding.entryTy) (σ : World D) (ρ : Env D Γ),
      wahr? (eval σ (code.leaf rename e) σ ρ) = leaf (eval σ e σ ρ))
    (entryval : Wert D binding.entryTy) :
    ∀ (e : Expr D Γ resources binding.entryTy) (σ : World D) (ρ : Env D Γ),
      eval σ e σ ρ = entryval →
      wahr? (eval σ (code.leaf rename e) σ ρ) = leaf entryval := by
  intro e σ ρ he
  rw [okLeaf e σ ρ, he]

/-- One generated leaf test under `WalkRunOk`: the `ite` over the leaf predicate completes with
    `.ok` and preserved node cells -- the visit block on a leaf, the given continuation otherwise.
    Proved by unfolding the `ite` and splitting on its condition. -/
theorem walkIte {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (code : WalkCode binding V outer resources)
    (tbl : Fin shape.arity → Wert D binding.entryTy)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (leaf descend : Wert D binding.entryTy → Bool) (state : World D)
    (ok : WalkRunOk binding code leaf descend tbl state oracle passes calls)
    {Γ : Ctx} (rename : WalkRen outer Γ)
    (path : List (Expr D Γ resources (.index shape.arity)))
    (level : Nat)
    (otherwise : Block D V true
      (binding.entryTy :: .index (D.count binding.iterator) :: Γ) resources resources)
    (hotherwise : ∀ (σ : World D)
      (ρ : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
      (∀ nodev, binding.entries σ nodev = tbl) →
      ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
        execBlock oracle passes calls otherwise σ ρ = .ok σ' ρ' ∧
        ∀ nodev, binding.entries σ' nodev = tbl) :
    ∀ (σ : World D) (ρ : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
      (∀ nodev, binding.entries σ nodev = tbl) →
      ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
        execStmt oracle passes calls
          (.ite (code.leaf (binding.renameEntry rename) (.var .here))
            (code.visit (binding.renameEntry rename) level
              (binding.fullPath path) (.var .here))
            otherwise) σ ρ = .ok σ' ρ' ∧
        ∀ nodev, binding.entries σ' nodev = tbl := by
  intro σ ρ hstab
  simp only [execStmt]
  split
  · obtain ⟨σ', ρ', hvisit⟩ := ok.visitOk (binding.renameEntry rename) level (binding.fullPath path) (.var .here) _ _
    exact ⟨_, _, hvisit, fun nodev => (ok.visitPreserves (binding.renameEntry rename) level (binding.fullPath path) (.var .here) _ _ _ _ hvisit nodev).trans (hstab nodev)⟩
  · refine hotherwise _ _ ?_
    exact fun nodev => hstab nodev

/-- One generated descent step under `WalkRunOk`: the checked optional child either stops (no
    child) or runs one lower mapping level, which completes with `.ok` and preserved node cells
    by the induction hypothesis. The leaf case is handled by the caller. -/
theorem walkDescendOk {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V outer resources)
    (tbl : Fin shape.arity → Wert D binding.entryTy)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (leaf descend : Wert D binding.entryTy → Bool) (state : World D)
    (ok : WalkRunOk binding code leaf descend tbl state oracle passes calls)
    (level : Nat)
    (ih : ∀ {Γ' : Ctx} {loop' : Bool} (rename' : WalkRen outer Γ')
      (node' : Expr D Γ' resources (.index (D.count binding.nodes)))
      (path' : List (Expr D Γ' resources (.index shape.arity)))
      (σ' : World D) (ρ' : Env D Γ'),
      (∀ nodev, binding.entries σ' nodev = tbl) →
      ∃ σ'' ρ'', execStmt oracle passes calls (l := loop')
        (binding.expand guard code level rename' node' path') σ' ρ' = .ok σ'' ρ'' ∧
        ∀ nodev, binding.entries σ'' nodev = tbl)
    {Γ : Ctx} (rename : WalkRen outer Γ)
    (path : List (Expr D Γ resources (.index shape.arity))) :
    ∀ (σ : World D) (ρ : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
      (∀ nodev, binding.entries σ nodev = tbl) →
      ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
        execBlock oracle passes calls
          (.cons (.ite (code.descend (binding.renameEntry rename) (.var .here))
            (.cons (.onOption (Expr.prodGet (.var .here) binding.child)
              (.cons (binding.expand guard code level
                (fun x => .there (binding.renameEntry rename x)) (.var .here)
                ((binding.fullPath path).map (fun value => value.weaken))) .nil) .nil) .nil) .nil) .nil)
          σ ρ = .ok σ' ρ' ∧
        ∀ nodev, binding.entries σ' nodev = tbl := by
  intro σ ρ hstab
  simp only [execBlock]
  have hdesc : ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
      execStmt oracle passes calls
        (.ite (code.descend (binding.renameEntry rename) (.var .here))
          (.cons (.onOption (Expr.prodGet (.var .here) binding.child)
            (.cons (binding.expand guard code level
              (fun x => .there (binding.renameEntry rename x)) (.var .here)
              ((binding.fullPath path).map (fun value => value.weaken))) .nil) .nil) .nil)) σ ρ =
      .ok σ' ρ' ∧ ∀ nodev, binding.entries σ' nodev = tbl := by
    simp only [execStmt]
    split
    · -- `dwhen` holds: follow the checked optional child.
      have honOpt : ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
          execStmt oracle passes calls
            (.onOption (Expr.prodGet (.var .here) binding.child)
              (.cons (binding.expand guard code level
                (fun x => .there (binding.renameEntry rename x)) (.var .here)
                ((binding.fullPath path).map (fun value => value.weaken))) .nil) .nil)
            (σ.lese resources (code.descend (binding.renameEntry rename) (.var .here)).orte) ρ =
          .ok σ' ρ' ∧ ∀ nodev, binding.entries σ' nodev = tbl := by
        simp only [execStmt]
        cases hchild : eval ((σ.lese resources (code.descend (binding.renameEntry rename) (.var .here)).orte).lese resources (Expr.prodGet (.var .here) binding.child).orte) (Expr.prodGet (.var .here) binding.child) ((σ.lese resources (code.descend (binding.renameEntry rename) (.var .here)).orte).lese resources (Expr.prodGet (.var .here) binding.child).orte) ρ with
        | none =>
            simp only [hchild]
            exact ⟨_, _, rfl, fun nodev => hstab nodev⟩
        | some c =>
            simp only [hchild]
            have hstabRec : ∀ nodev, binding.entries
                ((σ.lese resources (code.descend (binding.renameEntry rename) (.var .here)).orte).lese resources (Expr.prodGet (.var .here) binding.child).orte) nodev = tbl :=
              fun nodev => hstab nodev
            obtain ⟨σ₃, ρ₃, hrec, hc3⟩ := ih (fun x => .there (binding.renameEntry rename x)) (.var .here) ((binding.fullPath path).map (fun value => value.weaken)) _ _ hstabRec
            simp only [execBlock, hrec]
            exact ⟨_, _, rfl, hc3⟩
      obtain ⟨σ', ρ', honOpt, hcOpt⟩ := honOpt
      simp only [execBlock, honOpt]
      exact ⟨_, _, rfl, hcOpt⟩
    · exact ⟨_, _, rfl, fun nodev => hstab nodev⟩
  obtain ⟨σ', ρ', hdesc, hcdesc⟩ := hdesc
  simp only [hdesc]
  exact ⟨_, _, rfl, hcdesc⟩

/-- Under `WalkRunOk` every generated level completes with `.ok` and preserved node cells: the
    traverse visits every index once, the leaf test selects exactly the pure leaves, and descent
    follows the checked optional child. Proved by induction over the mapping levels, through
    `expandLevel_run` and `traverseLauf_all_okP`. -/
theorem walkExpand_ok {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V outer resources)
    (tbl : Fin shape.arity → Wert D binding.entryTy)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (leaf descend : Wert D binding.entryTy → Bool) (state : World D)
    (ok : WalkRunOk binding code leaf descend tbl state oracle passes calls) :
    ∀ (level : Nat) {Γ : Ctx} {loop : Bool} (rename : WalkRen outer Γ)
      (node : Expr D Γ resources (.index (D.count binding.nodes)))
      (path : List (Expr D Γ resources (.index shape.arity)))
      (σ : World D) (ρ : Env D Γ),
      (∀ (nodev : Wert D (.index (D.count binding.nodes))), binding.entries σ nodev = tbl) →
      ∃ (σ' : World D) (ρ' : Env D Γ),
        execStmt oracle passes calls (l := loop)
          (binding.expand guard code level rename node path) σ ρ = .ok σ' ρ' ∧
        ∀ (nodev : Wert D (.index (D.count binding.nodes))), binding.entries σ' nodev = tbl := by
  intro level
  induction level with
  | zero =>
      intro Γ loop rename node path σ ρ hstab
      have hexpand : binding.expand guard code 0 rename node path =
          binding.expandLevel guard code 0 rename node path none := rfl
      rw [hexpand, WalkBinding.expandLevel_run]
      refine traverseLauf_all_okP _ _ (fun σ => ∀ nodev, binding.entries σ nodev = tbl)
        (fun σ₁ ρ₁ => ok.invOk rename 0 path σ₁ ρ₁) (fun σ₁ ρ₁ h => h) ?_ _ σ ρ hstab
      intro σ₁ k ρ₁ hstab₁
      have hstabBind : ∀ nodev,
          binding.entries
            (((fun state env => let invariant := code.invariant rename 0 path
                                let read := state.lese resources invariant.orte
                                (read, wahr? (eval read invariant read env))) σ₁ ρ₁).1.lese resources
              (binding.readEntry guard node.weaken (binding.levelIndex (Γ := Γ))).orte) nodev =
            tbl := fun nodev => hstab₁ nodev
      have hnite : ∀ (σ₂ : World D)
          (ρ₂ : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
          (∀ nodev, binding.entries σ₂ nodev = tbl) →
          ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
            execStmt oracle passes calls
              (.ite (code.leaf (binding.renameEntry rename) (.var .here))
                (code.visit (binding.renameEntry rename) 0
                  (binding.fullPath path) (.var .here))
                .nil) σ₂ ρ₂ = .ok σ' ρ' ∧
            ∀ nodev, binding.entries σ' nodev = tbl := by
        intro σ₂ ρ₂ hstab₂
        refine walkIte binding code tbl oracle passes calls leaf descend state ok rename path 0 .nil ?_ σ₂ ρ₂ hstab₂
        intro σ₃ ρ₃ hstab₃
        exact ⟨_, _, rfl, hstab₃⟩
      have hstep : ∃ (σ' : World D) (ρ' : Env D (.index (D.count binding.iterator) :: Γ)),
          execBlock oracle passes calls
            (WalkBinding.levelBody binding guard code 0 rename node path none)
            (((fun state env => let invariant := code.invariant rename 0 path
                                let read := state.lese resources invariant.orte
                                (read, wahr? (eval read invariant read env))) σ₁ ρ₁).1) (.cons k ρ₁) =
          .ok σ' ρ' ∧ ∀ nodev, binding.entries σ' nodev = tbl := by
        simp only [WalkBinding.levelBody, execBlock]
        obtain ⟨σ₂, ρ₂, hnite, hcnite⟩ := hnite _ _ hstabBind
        simp only [hnite]
        exact ⟨_, _, rfl, hcnite⟩
      obtain ⟨σ', ρ', hstep, hcstep⟩ := hstep
      exact ⟨_, _, hstep, hcstep⟩
  | succ level ih =>
      intro Γ loop rename node path σ ρ hstab
      have hexpand : binding.expand guard code (level + 1) rename node path =
          binding.expandLevel guard code (level + 1) rename node path
            (some (fun {Δ} rename child pfx => binding.expand guard code level rename child pfx)) := rfl
      rw [hexpand, WalkBinding.expandLevel_run]
      refine traverseLauf_all_okP _ _ (fun σ => ∀ nodev, binding.entries σ nodev = tbl)
        (fun σ₁ ρ₁ => ok.invOk rename (level + 1) path σ₁ ρ₁) (fun σ₁ ρ₁ h => h) ?_ _ σ ρ hstab
      intro σ₁ k ρ₁ hstab₁
      have hstabBind : ∀ nodev,
          binding.entries
            (((fun state env => let invariant := code.invariant rename (level + 1) path
                                let read := state.lese resources invariant.orte
                                (read, wahr? (eval read invariant read env))) σ₁ ρ₁).1.lese resources
              (binding.readEntry guard node.weaken (binding.levelIndex (Γ := Γ))).orte) nodev =
            tbl := fun nodev => hstab₁ nodev
      have hnite : ∀ (σ₂ : World D)
          (ρ₂ : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
          (∀ nodev, binding.entries σ₂ nodev = tbl) →
          ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
            execStmt oracle passes calls
              (.ite (code.leaf (binding.renameEntry rename) (.var .here))
                (code.visit (binding.renameEntry rename) (level + 1)
                  (binding.fullPath path) (.var .here))
                (binding.otherwise code rename path
                  (some (fun {Δ} rename child pfx => binding.expand guard code level rename child pfx))))
              σ₂ ρ₂ = .ok σ' ρ' ∧
            ∀ nodev, binding.entries σ' nodev = tbl := by
        intro σ₂ ρ₂ hstab₂
        have hotherwise : ∀ (σ₃ : World D)
            (ρ₃ : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
            (∀ nodev, binding.entries σ₃ nodev = tbl) →
            ∃ (σ' : World D) (ρ' : Env D (binding.entryTy :: .index (D.count binding.iterator) :: Γ)),
              execBlock oracle passes calls
                (binding.otherwise code rename path
                  (some (fun {Δ} rename child pfx => binding.expand guard code level rename child pfx)))
                σ₃ ρ₃ = .ok σ' ρ' ∧
            ∀ nodev, binding.entries σ' nodev = tbl := by
          intro σ₃ ρ₃ hstab₃
          refine walkDescendOk binding guard code tbl oracle passes calls leaf descend state ok level ih rename path σ₃ ρ₃ hstab₃
        refine walkIte binding code tbl oracle passes calls leaf descend state ok rename path (level + 1) _ hotherwise σ₂ ρ₂ hstab₂
      have hstep : ∃ (σ' : World D) (ρ' : Env D (.index (D.count binding.iterator) :: Γ)),
          execBlock oracle passes calls
            (WalkBinding.levelBody binding guard code (level + 1) rename node path
              (some (fun {Δ} rename child pfx => binding.expand guard code level rename child pfx)))
            (((fun state env => let invariant := code.invariant rename (level + 1) path
                                let read := state.lese resources invariant.orte
                                (read, wahr? (eval read invariant read env))) σ₁ ρ₁).1) (.cons k ρ₁) =
          .ok σ' ρ' ∧ ∀ nodev, binding.entries σ' nodev = tbl := by
        simp only [WalkBinding.levelBody, execBlock]
        obtain ⟨σ₂, ρ₂, hnite, hcnite⟩ := hnite _ _ hstabBind
        simp only [hnite]
        exact ⟨_, _, rfl, hcnite⟩
      obtain ⟨σ', ρ', hstep, hcstep⟩ := hstep
      exact ⟨_, _, hstep, hcstep⟩

/-- The generated walker emits exactly the reachable qualifying mapping visits: under
    `WalkRunOk` the run completes, every emitted visit is a `WalkHit` pair and every `WalkHit`
    pair is emitted once, in path order and with its fields, `va`, `level` and `index`. -/
theorem walkExpand_correct {D : Deklaration} {shape : WalkShape} {V : Vertrag D}
    {outer : Ctx} {resources : List (Res D)} (binding : WalkBinding D shape)
    (guard : darf D binding.nodes resources) (code : WalkCode binding V outer resources)
    (leaf descend : Wert D binding.entryTy → Bool)
    (tbl : Fin shape.arity → Wert D binding.entryTy)
    (state : World D) (env : Env D outer)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (root : Expr D outer resources (.index (D.count binding.nodes)))
    (ok : WalkRunOk binding code leaf descend tbl state oracle passes calls) :
    (∃ (σ' : World D) (ρ' : Env D outer),
      execBlock oracle passes calls (binding.walk (loop := false) guard code root) state env = .ok σ' ρ') ∧
    (∀ (p : List (Fin shape.arity)) (m : Wert D binding.entryTy),
      (p, m) ∈ visitT (binding.tree state leaf descend) (shape.levels - 1) tbl ↔
      WalkHit (binding.tree state leaf descend) (shape.levels - 1) tbl p m) ∧
    (visitT (binding.tree state leaf descend) (shape.levels - 1) tbl).Pairwise
      (fun x y => x.1 ≠ y.1) := by
  obtain ⟨σw, ρw, hw, _⟩ := walkExpand_ok binding guard code tbl oracle passes calls leaf descend
    state ok (loop := false) (shape.levels - 1) (fun x => .there x) root []
    (state.lese resources root.orte)
    (.cons (eval (state.lese resources root.orte) root (state.lese resources root.orte) env) env)
    ok.stable
  have hwalk : execBlock oracle passes calls (binding.walk (loop := false) guard code root) state env =
      .ok σw ρw.tail := by
    simp only [WalkBinding.walk, execBlock, hw, Ausgang.schrumpf]
  obtain ⟨hmem, hnodup, _⟩ := walkMappings_correct (binding.tree state leaf descend) shape.levels
    (shape.levels - 1) tbl
  exact ⟨⟨_, _, hwalk⟩, hmem, hnodup⟩

/-- Witnesses of the mapping whole-proof on a non-degenerate two-level mapping: a root with one
    leaf entry and one descendable entry whose two child entries are leaves. -/
def zeugeWalkKind : Fin 2 → Nat
  | ⟨0, _⟩ => 20
  | ⟨1, _⟩ => 21

def zeugeWalkTbl : Fin 2 → Nat
  | ⟨0, _⟩ => 10
  | ⟨1, _⟩ => 11

def zeugeWalkT : WalkTree Nat 2 where
  leaf := fun e => e == 10 || e == 20 || e == 21
  dwhen := fun e => e == 11
  down := fun e => if e == 11 then some zeugeWalkKind else none

theorem zeugeWalkT_down : zeugeWalkT.down 11 = some zeugeWalkKind := by
  have h11 : (11 : Nat) == 11 = true := by decide
  show (if (11 : Nat) == 11 then some zeugeWalkKind else none) = some zeugeWalkKind
  rw [if_pos h11]

/-- The generic whole-proof on the two-level fixture: soundness, completeness, no duplicate paths,
    and the exact enumeration `[[0], 10), ([1, 0], 20), ([1, 1], 21)]`. -/
theorem walkMappings_correct_zeuge :
    (∀ (p : List (Fin 2)) (m : Nat),
      (p, m) ∈ visitT zeugeWalkT 1 zeugeWalkTbl ↔ WalkHit zeugeWalkT 1 zeugeWalkTbl p m) ∧
    (visitT zeugeWalkT 1 zeugeWalkTbl).Pairwise (fun x y => x.1 ≠ y.1) ∧
    (visitT zeugeWalkT 1 zeugeWalkTbl = [([0], 10), ([1, 0], 20), ([1, 1], 21)]) := by
  obtain ⟨hmem, hnodup, _⟩ := walkMappings_correct zeugeWalkT 2 1 zeugeWalkTbl
  exact ⟨hmem, hnodup, by decide⟩

end Gabbro.Grammatik
