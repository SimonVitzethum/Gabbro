import Grammatik.Bausteine.Arena.Unbounded.GForm

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame)

variable {D : Deklaration} {region : Type} {A : FreiForm D}

/-- Only live payloads are observed. Freed physical bytes may retain old data;
the grant check prevents that data from becoming a language value. -/
def PayloadRepresented (H : Heap region (Wert D (D.typ A.tab A.feld))) (σ : World D) : Prop :=
  Represented H A σ ∧ ∀ i value, H.payload i = some value → σ.slots A.tab i A.feld = value

/-- Lowering a reference to an existing finite G index requires its actual live
grant and the selected realisation's bound. There is no integer-to-reference rule. -/
def physicalIndex {H : Heap region α} {σ : World D} {capacity : Capacity}
    (hv : H.Valid capacity) (hr : Represented H A σ) (frame : Frame) (r : Ref region)
    (ha : H.rights.access frame r.handle) : Wert D (Ty.index (D.count A.tab)) :=
  ⟨r.handle.slot, (Heap.access_bounded hv ha).1,
    by have := (Heap.access_bounded hv ha).2; have := hr.2.2; omega⟩

/-- A real G slot expression returns exactly the abstract allocator's payload. -/
theorem read_execution {H : Heap region (Wert D (D.typ A.tab A.feld))}
    {σ : World D} {capacity : Capacity} (hv : H.Valid capacity)
    (hr : PayloadRepresented (A := A) H σ) (frame : Frame) (r : Ref region)
    {value : Wert D (D.typ A.tab A.feld)} (he : H.read frame r = some value)
    {Γ : Ctx} {Λ : List (Res D)} (guard : darf D A.tab Λ) (ρ : Env D Γ) :
    eval σ (Expr.slot A.tab A.feld (Expr.var .here) guard) σ
      (.cons (physicalIndex hv hr.1 frame r (Heap.read_requires_access he)) ρ) = value := by
  have ha := Heap.read_requires_access he
  have hp : H.payload r.handle.slot = some value := by simpa [Heap.read, ha] using he
  exact hr.2 _ _ hp

section Allocation

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- Materialising a previously evaluated payload uses the ordinary G store;
the two allocator instructions preserve every other payload cell. -/
theorem allocation_payload_frame (A : FreiForm D)
    (x : Var Γ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ',
      execBlock O passes R
        (Block.arenaRumpf (l := l) (Λ' := Λ) A.toArenaForm (.var x) hwT hLT hwG hLG .nil)
        σ (.cons k ρ) = .ok σ' (.cons k ρ) ∧
      ∀ i, σ'.slots A.tab i A.feld = if i = k.n then ρ.get x else σ.slots A.tab i A.feld := by
  refine ⟨_, rfl, ?_⟩
  intro i
  simp only [eval, Block.arenaBump, eval_umTyp, orte_umTyp, Expr.orte,
    World.slots_schreibGlob, World.slots_lese]
  simp only [World.schreibSlot, World.merke, World.storeSlot, Env.get, World.lese, Expr.weaken, Expr.ins,
  Expr.ren, List.nil_append, Var.ins, eval, List.cons_append, ↓reduceDIte]

/-- The existing G allocation actually runs and produces the SAME grant as the
unbounded allocator, whenever this finite realisation has room. This is a
single-request simulation, not the missing whole-program unbounded-heap bridge. -/
theorem fresh_allocation_execution (A : FreiForm D) (H : Heap region α)
    (frame : Frame) (value : α) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hv : H.Valid .unbounded) (hr : Represented H A σ) (hf : A.FreiOk σ)
    (hfree : H.free = []) (hroom : A.stand σ < D.count A.tab) :
    ∃ H' reference σ',
      H.allocate .unbounded true frame value = some (H', reference) ∧
      execBlock O passes R
        (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG failure (.nil)) σ ρ = .ok σ' ρ ∧
      Represented H' A σ' ∧ H'.rights.owns frame reference.handle ∧
      A.FreiOk σ' ∧ A.Fremd σ σ' := by
  obtain ⟨H', reference, ha⟩ := Heap.allocate_exists hv frame value rfl
  let k : Wert D (Ty.index (D.count A.tab)) :=
    ⟨A.stand σ, A.stand_nonneg σ, by omega⟩
  obtain ⟨σ', hexec, hk, hn, hc, hframe⟩ :=
    arenaRumpf_ausfuehren O passes R A v hwT hLT hwG hLG (.nil)
      (σ.lese Λ [Sum.inr A.zaehl]) k ρ
  have hp := Heap.allocate_parts ha
  have hcandidate : (H.candidate : Int) = A.stand σ := by
    simpa [Heap.candidate, hfree] using hr.2.1
  have hledger := ArenaOwnership.State.allocate_agrees hr.1 frame (H.candidate : Int)
    reference.handle hp.2.2.1 (fun i => by
      rw [hcandidate]
      exact A.bump_live_iff hf hk hn hc i)
  have hcount : (H'.extent : Int) = A.stand σ' := by
    have hx := congrArg Heap.extent hp.2.2.2
    have hx' : H'.extent = H.extent + 1 := by
      simpa [Heap.install, Heap.nextExtent, hfree] using hx
    change A.stand σ' = A.stand σ + 1 at hc
    rw [hx', hc]
    have := hr.2.1
    omega
  refine ⟨H', reference, σ', ha, ?_, ⟨hledger, hcount, by rw [hcount]; exact A.stand_le σ'⟩,
    (Heap.allocate_valid hv ha).2.1, (A.lebt_bump hf hk hn hc).1, hframe⟩
  rw [arenaAlloc_unter_schranke O passes R A.toArenaForm v hwT hLT hwG hLG failure (.nil) σ ρ hroom]
  rw [hexec]
  rfl

/-- Fresh payload and all previously live payloads agree with executed G memory.
The source value is evaluated before allocation and passed as an ordinary local. -/
theorem fresh_payload_execution (A : FreiForm D)
    (H : Heap region (Wert D (D.typ A.tab A.feld))) (frame : Frame)
    (x : Var Γ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hv : H.Valid .unbounded) (hr : PayloadRepresented (A := A) H σ) (hf : A.FreiOk σ)
    (hfree : H.free = []) (hroom : A.stand σ < D.count A.tab) :
    ∃ H' reference σ',
      H.allocate .unbounded true frame (ρ.get x) = some (H', reference) ∧
      execBlock O passes R
        (Block.arenaAlloc A.toArenaForm (.var x) hwT hLT hwG hLG failure (.nil)) σ ρ = .ok σ' ρ ∧
      PayloadRepresented (A := A) H' σ' ∧ H'.rights.owns frame reference.handle ∧ A.FreiOk σ' := by
  obtain ⟨H', reference, σ', ha, hg, hrep, hown, hfree', _⟩ :=
    fresh_allocation_execution O passes R A H frame (ρ.get x) (.var x)
      hwT hLT hwG hLG failure σ ρ hv hr.1 hf hfree hroom
  let k : Wert D (Ty.index (D.count A.tab)) :=
    ⟨A.stand σ, A.stand_nonneg σ, by omega⟩
  obtain ⟨σp, hp, hvalues⟩ := allocation_payload_frame O passes R A x hwT hLT hwG hLG
    (σ.lese Λ [Sum.inr A.zaehl]) k ρ
  have hg' := hg
  rw [arenaAlloc_unter_schranke O passes R A.toArenaForm (.var x)
    hwT hLT hwG hLG failure (.nil) σ ρ hroom, hp] at hg'
  have hworld : σp = σ' := by
    change (Ausgang.ok σp ρ : Ausgang V l Γ) = .ok σ' ρ at hg'
    cases hg'; rfl
  refine ⟨H', reference, σ', ha, hg, ⟨hrep, ?_⟩, hown, hfree'⟩
  intro i value hvalue
  have hdata := congrFun (congrArg Heap.payload (Heap.allocate_parts ha).2.2.2) i
  have hcandidate : (H.candidate : Int) = k.n := by
    simpa [Heap.candidate, hfree, k] using hr.1.2.1
  change H'.payload i = (if i = (H.candidate : Int) then some (ρ.get x) else H.payload i) at hdata
  rw [hdata, hcandidate] at hvalue
  rw [← hworld, hvalues]
  by_cases hi : i = k.n
  · simpa [hi] using hvalue
  · simp only [ite_eq_right hi] at hvalue ⊢
    exact hr.2 i value hvalue

end Allocation

end Gabbro.Grammatik.ArenaStorage
