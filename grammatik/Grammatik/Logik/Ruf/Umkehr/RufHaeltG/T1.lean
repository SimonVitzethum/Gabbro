/-
  File:      Grammatik/RufHaeltG.lean
  Subject:   STATIC HOLDINGS ARE HELD on every reachable machine of the
             repaired call machine G (`rufG_haelt_statisch`).

  The repair (`RufMaschineG.lean`, 2026-09-13): the bare `nimmt`/`gibt`
  steps are gone, a start thread holds its signature locks from the start
  machine on, and every step that reads the thread world demands
  `HeldGenau` of the head's static holdings. Here the payoff: on every
  reachable machine, for every thread and EVERY frame on its stack (head and
  suspended), every lock the frame's static holdings name is held by the
  thread (`rufG_haelt_statisch`), in particular every signature lock of the
  frame's function (`rufG_haelt_signatur`). A lock leaves the held set only
  through a release marker the head names (`offen_schrittG`,
  `ZielOrt.lean`).

  The inductive invariant (`HaeltInvG`) has three parts: every frame's
  static holdings are held; along every frame's residue chain each node
  names the frame's signature locks and each release marker `frei L k`
  releases a lock the holdings of `k` do not name (`GRest.kette`); no
  release marker of a frame releases a lock a frame BELOW it names
  (`FreiLinks` -- the lock was taken while that frame was suspended and its
  holdings held, and `dannLocks` demands the lock is not held). Since the
  held-set relaxation (2026-09-13) a suspended caller may hold locks its
  callee does not name, so the old link (`KetteLinks`: a suspended frame
  names nothing beyond the signature locks of the frame above it) is gone.
  Only `GutO` is assumed (the oracle keeps the held locks, for `axiomCall`
  leaves and `bindAxiom`).
-/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The residue chain -/

/-- Every node of a residue's continuation chain names the locks `A` in its
    static holdings; every release marker `frei L k` releases a lock that
    the holdings of `k` do not name. -/
def GRest.kette {V : Vertrag D} (A : List D.Lock) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, Λ, .ende _ => ∀ L ∈ A, Res.held L ∈ Λ
  | _, _, Λ, .dann _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .schrumpf k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, _, @GRest.frei _ _ _ _ Λk L k => Res.held L ∉ Λk ∧ k.kette A
  | _, _, Λ, .trav _ _ _ _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .travRest _ _ _ _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .wieder _ _ _ _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .wiederRest _ _ _ _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .ewig _ _ _ _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .ewigRest _ _ _ _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .wartet _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .wartetSonst _ _ _ k => (∀ L ∈ A, Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, @GRest.abbruch _ _ _ _ _ Λk k =>
      (∀ L ∈ A, Res.held L ∈ Λ) ∧ (∀ L, Res.held L ∈ Λk → Res.held L ∈ Λ) ∧ k.kette A
  | _, _, Λ, .leer => ∀ L ∈ A, Res.held L ∈ Λ

/-- The top node of a chain names `A`. -/
theorem GRest.kette_top {V : Vertrag D} {A : List D.Lock} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ), r.kette A →
      ∀ L ∈ A, Res.held L ∈ Λ
  | _, _, _, .ende _, h => h
  | _, _, _, .dann _ _, h => h.1
  | _, _, _, .schrumpf _, h => h.1
  | _, _, _, .frei _ k, h => fun L hL => List.mem_cons_of_mem _ (GRest.kette_top k h.2 L hL)
  | _, _, _, .trav _ _ _ _ _, h => h.1
  | _, _, _, .travRest _ _ _ _ _, h => h.1
  | _, _, _, .wieder _ _ _ _ _, h => h.1
  | _, _, _, .wiederRest _ _ _ _ _, h => h.1
  | _, _, _, .ewig _ _ _ _ _, h => h.1
  | _, _, _, .ewigRest _ _ _ _ _, h => h.1
  | _, _, _, .wartet _ _, h => h.1
  | _, _, _, .wartetSonst _ _ _ _, h => h.1
  | _, _, _, .abbruch _, h => h.1
  | _, _, _, .leer, h => h

/-- Naming `A` carries along a block (`Block.held_iff`). -/
theorem nennt_block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') {A : List D.Lock} (h : ∀ L ∈ A, Res.held L ∈ Λ) :
    ∀ L ∈ A, Res.held L ∈ Λ' :=
  fun L hL => (Block.held_iff b L).mpr (h L hL)

/-- Naming `A` carries along a statement (`Stmt.held_iff`). -/
theorem nennt_stmt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') {A : List D.Lock} (h : ∀ L ∈ A, Res.held L ∈ Λ) :
    ∀ L ∈ A, Res.held L ∈ Λ' :=
  fun L hL => (Stmt.held_iff s L).mpr (h L hL)

/-- Holdings held carry along a block. -/
theorem heldIn_block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') {o : List D.Lock} (h : HeldIn Λ o) : HeldIn Λ' o :=
  fun L hL => h L ((Block.held_iff b L).mp hL)

/-- Holdings held carry backwards along a block. -/
theorem heldIn_block_rueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') {o : List D.Lock} (h : HeldIn Λ' o) : HeldIn Λ o :=
  fun L hL => h L ((Block.held_iff b L).mpr hL)

/-- Holdings held carry along a statement. -/
theorem heldIn_stmt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') {o : List D.Lock} (h : HeldIn Λ o) : HeldIn Λ' o :=
  fun L hL => h L ((Stmt.held_iff s L).mp hL)

/-! ## 2. The thread invariant

    Since the held-set relaxation (2026-09-13, `RufPasst.hh` is `⊆`), a
    suspended caller may hold locks its callee does not name (the caller's
    extra locks), so the old link "a suspended frame names nothing beyond the
    signature locks of the frame above it" is gone. What replaces it: every
    frame's holdings are held (not only the head's), and a release marker of
    a frame releases no lock that a frame BELOW it names (`FreiLinks`) -- it
    was taken while that frame was suspended and its holdings held, so it
    was not among them (`dannLocks` demands the lock is not held). -/

/-- The locks the release markers of a residue's continuation chain release. -/
def GRest.freis {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → List D.Lock
  | _, _, _, .ende _ => []
  | _, _, _, .dann _ k => k.freis
  | _, _, _, .schrumpf k => k.freis
  | _, _, _, .frei L k => L :: k.freis
  | _, _, _, .trav _ _ _ _ k => k.freis
  | _, _, _, .travRest _ _ _ _ k => k.freis
  | _, _, _, .wieder _ _ _ _ k => k.freis
  | _, _, _, .wiederRest _ _ _ _ k => k.freis
  | _, _, _, .ewig _ _ _ _ k => k.freis
  | _, _, _, .ewigRest _ _ _ _ k => k.freis
  | _, _, _, .wartet _ k => k.freis
  | _, _, _, .wartetSonst _ _ _ k => k.freis
  | _, _, _, .abbruch k => k.freis
  | _, _, _, .leer => []

/-- The chain behind an `else` branch run in block position: the branch
    keeps the held locks of its start, and so does the block its
    continuation stood behind. -/
theorem kette_abbruch {V : Vertrag D} {A : List D.Lock} {l : Bool} {Γ : Ctx}
    {Λ Λs Λ' : List (Res D)} (b : Block D V l Γ Λ Λs) (hA : ∀ L ∈ A, Res.held L ∈ Λ)
    (k : GRest D V l Γ Λ') (hk : k.kette A) (hr : ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ) :
    (GRest.dann b (.abbruch k) : GRest D V l Γ Λ).kette A :=
  ⟨hA, fun L hL => (Block.held_iff b L).mpr (hA L hL),
    fun L hL => (Block.held_iff b L).mpr (hr L hL), hk⟩

/-- The release markers of a frame's residue. -/
def RufRahmenG.freis (F : RufRahmenG D) : List D.Lock := F.rest.2.2.2.2.freis

/-- The release markers of every frame release no lock a frame below it names. -/
def FreiLinks : RufRahmenG D → List (RufRahmenG D) → Prop
  | _, [] => True
  | d, c :: rest => (∀ L ∈ d.freis, ∀ F ∈ c :: rest, Res.held L ∉ F.rest.2.2.1) ∧ FreiLinks c rest

/-- **The thread invariant.** Every frame's static holdings are held; every
    frame's residue chain names the frame's signature locks and releases
    only locks its continuation does not name; no release marker releases a
    lock a frame below names. -/
def HaeltInvG (z : RufFadenG D) : Prop :=
  (∀ F ∈ z.kopf :: z.stapel, HeldIn F.rest.2.2.1 (offen z.spur)) ∧
  (∀ F ∈ z.kopf :: z.stapel, F.rest.2.2.2.2.kette (D.haelt F.f)) ∧
  FreiLinks z.kopf z.stapel

theorem HaeltInvG.alle {z : RufFadenG D} (h : HaeltInvG z) :
    ∀ F ∈ z.kopf :: z.stapel, HeldIn F.rest.2.2.1 (offen z.spur) := h.1

theorem HaeltInvG.kopf {z : RufFadenG D} (h : HaeltInvG z) :
    HeldIn z.kopf.rest.2.2.1 (offen z.spur) := h.1 z.kopf List.mem_cons_self

theorem HaeltInvG.signatur {z : RufFadenG D} (h : HaeltInvG z) :
    ∀ F ∈ z.kopf :: z.stapel, ∀ L ∈ D.haelt F.f, L ∈ offen z.spur :=
  fun F hF L hL => h.alle F hF L (GRest.kette_top _ (h.2.1 F hF) L hL)

/-- Reading the head: the kept residue of a frame with a known rest. -/
theorem kette_von {F : RufRahmenG D} {A : List D.Lock} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D F.f) l Γ Λ}
    (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩) (h : F.rest.2.2.2.2.kette A) : r.kette A := by
  rw [hF] at h
  exact h

theorem heldIn_von {F : RufRahmenG D} {o : List D.Lock} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D F.f) l Γ Λ}
    (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩) (h : HeldIn F.rest.2.2.1 o) : HeldIn Λ o := by
  rw [hF] at h
  exact h

theorem freis_von {F : RufRahmenG D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D F.f) l Γ Λ}
    (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩) : F.freis = r.freis := by
  unfold RufRahmenG.freis
  rw [hF]

theorem freiLinks_kopf {d d' : RufRahmenG D} (e : ∀ L ∈ d'.freis, L ∈ d.freis) :
    ∀ {s : List (RufRahmenG D)}, FreiLinks d s → FreiLinks d' s
  | [], _ => trivial
  | _ :: _, h => ⟨fun L hL => h.1 L (e L hL), h.2⟩

/-- A head-local step: new residue with its chain and held holdings, the
    held locks change only by taking a lock or by releasing a lock of a
    release marker of the head; the stack is kept. -/
theorem haeltInvG_kopf {z : RufFadenG D} (h : HaeltInvG z) {l : Bool} {Γ : Ctx}
    {Λ' : List (Res D)} {ρ' : Env D Γ} {r' : GRest D (vertragVon D z.kopf.f) l Γ Λ'}
    {spur' : List (Ereignis D)}
    (ho : ∀ K, K ∈ offen z.spur → K ∉ z.kopf.freis → K ∈ offen spur')
    (hfr : ∀ L ∈ r'.freis, L ∈ z.kopf.freis ∨ L ∉ offen z.spur)
    (hk : r'.kette (D.haelt z.kopf.f)) (hh : HeldIn Λ' (offen spur')) :
    HaeltInvG ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', r'⟩⟩, spur', z.log⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hh
    · intro K hK
      have hKo := h1 F (List.mem_cons_of_mem _ hF) K hK
      refine ho K hKo (fun hKf => ?_)
      cases hs : z.stapel with
      | nil => rw [hs] at hF; exact absurd hF List.not_mem_nil
      | cons c rest =>
        have := h3
        rw [hs] at this hF
        exact this.1 K hKf F hF hK
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hk
    · exact h2 F (List.mem_cons_of_mem _ hF)
  · cases hs : z.stapel with
    | nil => trivial
    | cons c rest =>
      have h3' := h3
      rw [hs] at h3'
      refine ⟨fun L hL F hF hLF => ?_, h3'.2⟩
      rcases hfr L hL with hL' | hL'
      · exact h3'.1 L hL' F hF hLF
      · exact hL' (h1 F (by rw [hs]; exact List.mem_cons_of_mem _ hF) L hLF)

/-- Reads keep the held locks. -/
theorem offen_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    offen (σ.lese Λ os).spur = offen σ.spur :=
  lese_haelt σ Λ os

theorem offen_schreibGlob (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g)) :
    offen (σ.schreibGlob g Λ v).spur = offen σ.spur := rfl

theorem leave_welt' {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) {l : Bool} (h : l = true) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes R (Stmt.leave (V := V) (Γ := Γ) (Λ := Λ) h) σ ρ =
      Ausgang.leave h σ' ρ') : σ' = σ := by
  simp only [execStmt] at hst
  cases hst
  rfl

theorem next_welt' {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) {l : Bool} (h : l = true) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes R (Stmt.next (V := V) (Γ := Γ) (Λ := Λ) h) σ ρ =
      Ausgang.next h σ' ρ') : σ' = σ := by
  simp only [execStmt] at hst
  cases hst
  rfl

/-- The oracle keeps the held locks (`GutO`, second conjunct). -/
theorem axiom_offen' {O : Orakel D} (hO : GutO O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) (σ₂ : World D) (v : Option (ErgVal D (D.aerg a)))
    (hax : axiomAntwort O a σ ρ = (σ₂, v)) : offen σ₂.spur = offen σ.spur := by
  have e : σ₂ = (O.wirkt a σ ρ).1 := by
    have := congrArg Prod.fst hax
    simp only [axiomAntwort] at this
    exact this.symm
  subst e
  exact (hO a σ ρ).2.1

/-- The same for a FALLIBLE axiom (C-free lane, 2026-09-30): its world is `axiomAntwort`'s. -/
theorem axiomSonst_offen' {O : Orakel D} (hO : GutO O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) (σ₂ : World D) (x : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a)))
    (hax : axiomAntwortSonst O a σ ρ = (σ₂, x)) : offen σ₂.spur = offen σ.spur :=
  axiom_offen' hO a σ ρ σ₂ (axiomAntwort O a σ ρ).2
    (Prod.ext (show (axiomAntwort O a σ ρ).1 = σ₂ from congrArg Prod.fst hax) rfl)

/-- A push: the caller frame goes onto the stack, the callee frame (no
    release marker yet) becomes the head; the held locks are kept. -/

theorem haeltInvG_push {z : RufFadenG D} (h : HaeltInvG z) (caller callee : RufRahmenG D)
    (spur' : List (Ereignis D)) (log' : List (RufEreignisF D))
    (hcf : caller.f = z.kopf.f)
    (hck : caller.rest.2.2.2.2.kette (D.haelt caller.f))
    (hfr : ∀ L ∈ caller.freis, L ∈ z.kopf.freis)
    (hek : callee.rest.2.2.2.2.kette (D.haelt callee.f))
    (hef : callee.freis = [])
    (ho : offen spur' = offen z.spur)
    (hch : HeldIn caller.rest.2.2.1 (offen z.spur))
    (hh : HeldIn callee.rest.2.2.1 (offen spur')) :
    HaeltInvG ⟨caller :: z.stapel, callee, spur', log'⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ⟨fun L hL => by rw [hef] at hL; exact absurd hL List.not_mem_nil,
    freiLinks_kopf hfr h3⟩⟩
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hh
    · rw [ho]
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hch
      · exact h1 F (List.mem_cons_of_mem _ hF)
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hek
    · rcases List.mem_cons.mp hF with rfl | hF
      · exact hck
      · exact h2 F (List.mem_cons_of_mem _ hF)

/-- A pop: the caller frame (possibly with a new residue at the same held
    locks, no new release marker) becomes the head. -/
theorem haeltInvG_pop {z : RufFadenG D} (h : HaeltInvG z) {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (hpop : z.stapel = caller :: rst) (neu : RufRahmenG D)
    (spur' : List (Ereignis D)) (log' : List (RufEreignisF D))
    (hf : neu.f = caller.f)
    (hΛ : ∀ L, Res.held L ∈ neu.rest.2.2.1 → Res.held L ∈ caller.rest.2.2.1)
    (hfr : ∀ L ∈ neu.freis, L ∈ caller.freis)
    (hk : neu.rest.2.2.2.2.kette (D.haelt neu.f))
    (ho : offen spur' = offen z.spur) :
    HaeltInvG ⟨rst, neu, spur', log'⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hpop] at h1 h2 h3
  refine ⟨?_, ?_, freiLinks_kopf hfr h3.2⟩
  · intro F hF
    rw [ho]
    rcases List.mem_cons.mp hF with rfl | hF
    · intro L hL
      exact h1 caller (List.mem_cons_of_mem _ List.mem_cons_self) L (hΛ L hL)
    · exact h1 F (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))
  · intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hk
    · exact h2 F (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF))

theorem haeltInvG_pop_gleich {z : RufFadenG D} (h : HaeltInvG z) {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (hpop : z.stapel = caller :: rst)
    (spur' : List (Ereignis D)) (log' : List (RufEreignisF D))
    (ho : offen spur' = offen z.spur) :
    HaeltInvG ⟨rst, caller, spur', log'⟩ := by
  have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) := by
    have := h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    exact this
  exact haeltInvG_pop h hpop caller spur' log' rfl (fun _ hL => hL) (fun _ hL => hL) hc ho

/-- The callee frame a push creates is well-chained and has no release
    marker. -/
theorem callee_kette (P : Programm D) (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D) :
    (⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩ :
      RufRahmenG D).rest.2.2.2.2.kette (D.haelt g) :=
  fun L hL => (held_anfang _ L).mpr hL

theorem callee_freis (P : Programm D) (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D) :
    (⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩ :
      RufRahmenG D).freis = [] := rfl

/-- The callee's holdings are held: its signature locks are among the
    caller's holdings (`RufPasst.hh`, `⊆`). -/
theorem callee_held {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {Λ : List (Res D)} (hp : RufPasst D V S Λ) {o : List D.Lock} (h : HeldIn Λ o) :
    HeldIn (Signatur.anfang D S) o :=
  fun L hL => h L (hp.hh L ((held_anfang S L).mp hL))

theorem nach_nennt {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    {A : List D.Lock} (h : ∀ L ∈ A, Res.held L ∈ Λ) : ∀ L ∈ A, Res.held L ∈ nachSig D S Λ :=
  fun L hL => (held_nachSig_iff S Λ L).mpr (h L hL)

theorem nach_held {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    {o : List D.Lock} (h : HeldIn Λ o) : HeldIn (nachSig D S Λ) o :=
  fun L hL => h L ((held_nachSig_iff S Λ L).mp hL)

set_option hygiene false in
/-- The held locks of a head-local step: kept (read, leaf, axiom, write). -/
macro "ho_tac" : tactic => `(tactic|
  (intro K hK _
   first
     | exact hK
     | (rw [ho]; exact hK)
     | (rw [hs₁, offen_lese]; exact hK)
     | (rw [hs₂, offen_schreibGlob, hs₁, offen_lese]; exact hK)
     | (rw [axiom_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hK)
     | (rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hK)
     | (rw [hs₁, offen_lese, e]; exact hK)
     | (rw [e]; exact hK)))

set_option hygiene false in
/-- The release markers of the caller at a push: among the head's. -/
macro "fr_push" : tactic => `(tactic|
  (intro L hL
   rw [freis_von hhead]
   simp_all [RufRahmenG.freis, GRest.freis]))

set_option hygiene false in
/-- The release markers of the resumed caller at a pop: among its old ones. -/
macro "fr_pop" : tactic => `(tactic|
  (intro L hL
   first
     | (rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;>
          (rw [freis_von hcaller]; simp_all [RufRahmenG.freis, GRest.freis]))
     | (rw [freis_von hcaller]; simp_all [RufRahmenG.freis, GRest.freis])))

set_option hygiene false in
/-- The release markers of a head-local step: among the old ones. -/
macro "fr_tac" : tactic => `(tactic|
  (intro L hL
   left
   rw [freis_von hhead]
   simp_all [GRest.freis]))

/-! ## 3. Every rule keeps the invariant -/


end Gabbro.Grammatik
