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

  The inductive invariant (`HaeltInvG`) has three parts: the head's static
  holdings are held; along every frame's residue chain each node names the
  frame's signature locks and each release marker `frei L k` releases a lock
  the holdings of `k` do not name (`GRest.kette`); a suspended frame names
  no lock beyond the signature locks of the frame above it (`KetteLinks`,
  from `RufPasst.hh` at the push). Only `GutO` is assumed (the oracle keeps
  the held locks, for `axiomCall` leaves and `bindAxiom`).
-/
import Grammatik.RufMaschineG

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

/-! ## 2. The thread invariant -/

/-- A suspended frame names no lock beyond the signature locks of the frame
    directly above it (`RufPasst.hh` at the push, `nach` keeps the held
    part). -/
def KetteLinks : RufRahmenG D → List (RufRahmenG D) → Prop
  | _, [] => True
  | d, c :: rest => (∀ L, Res.held L ∈ c.rest.2.2.1 → L ∈ D.haelt d.f) ∧ KetteLinks c rest

/-- **The thread invariant.** The head's static holdings are held; every
    frame's residue chain names the frame's signature locks and releases
    only locks its continuation does not name; suspended frames are linked. -/
def HaeltInvG (z : RufFadenG D) : Prop :=
  HeldIn z.kopf.rest.2.2.1 (offen z.spur) ∧
  (∀ F ∈ z.kopf :: z.stapel, F.rest.2.2.2.2.kette (D.haelt F.f)) ∧
  KetteLinks z.kopf z.stapel

theorem ketteLinks_kopf {d d' : RufRahmenG D} (e : d'.f = d.f) :
    ∀ {s : List (RufRahmenG D)}, KetteLinks d s → KetteLinks d' s
  | [], _ => trivial
  | _ :: _, h => ⟨fun L hL => e ▸ h.1 L hL, h.2⟩

/-- Every frame's static holdings are held: down the stack along the links. -/
theorem haeltInvG_alle_aux {o : List D.Lock} :
    ∀ (d : RufRahmenG D) (s : List (RufRahmenG D)), HeldIn d.rest.2.2.1 o →
      (∀ F ∈ d :: s, F.rest.2.2.2.2.kette (D.haelt F.f)) → KetteLinks d s →
      ∀ F ∈ d :: s, HeldIn F.rest.2.2.1 o
  | d, [], hd, _, _, F, hF => by
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hd
      · exact absurd hF List.not_mem_nil
  | d, c :: s, hd, hk, hl, F, hF => by
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hd
      · have hc : HeldIn c.rest.2.2.1 o := fun L hL =>
          hd L (GRest.kette_top _ (hk d List.mem_cons_self) L (hl.1 L hL))
        exact haeltInvG_alle_aux c s hc (fun F' hF' => hk F' (List.mem_cons_of_mem _ hF'))
          hl.2 F hF

theorem HaeltInvG.alle {z : RufFadenG D} (h : HaeltInvG z) :
    ∀ F ∈ z.kopf :: z.stapel, HeldIn F.rest.2.2.1 (offen z.spur) :=
  haeltInvG_alle_aux z.kopf z.stapel h.1 h.2.1 h.2.2

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

/-- A head-local step: new residue with its chain and held holdings; the
    stack and the links are kept. -/
theorem haeltInvG_kopf {z : RufFadenG D} (h : HaeltInvG z) {l : Bool} {Γ : Ctx}
    {Λ' : List (Res D)} {ρ' : Env D Γ} {r' : GRest D (vertragVon D z.kopf.f) l Γ Λ'}
    {spur' : List (Ereignis D)} (hk : r'.kette (D.haelt z.kopf.f)) (hh : HeldIn Λ' (offen spur')) :
    HaeltInvG ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', r'⟩⟩, spur', z.log⟩ := by
  refine ⟨hh, ?_, ketteLinks_kopf (d := z.kopf) (by rfl) h.2.2⟩
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hk
  · exact h.2.1 F (List.mem_cons_of_mem _ hF)

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

/-- A push: the caller frame goes onto the stack, the callee frame becomes
    the head. -/
theorem haeltInvG_push {z : RufFadenG D} (h : HaeltInvG z) (caller callee : RufRahmenG D)
    (spur' : List (Ereignis D)) (log' : List (RufEreignisF D))
    (hcf : caller.f = z.kopf.f)
    (hck : caller.rest.2.2.2.2.kette (D.haelt caller.f))
    (hlink : ∀ L, Res.held L ∈ caller.rest.2.2.1 → L ∈ D.haelt callee.f)
    (hek : callee.rest.2.2.2.2.kette (D.haelt callee.f))
    (hh : HeldIn callee.rest.2.2.1 (offen spur')) :
    HaeltInvG ⟨caller :: z.stapel, callee, spur', log'⟩ := by
  refine ⟨hh, ?_, hlink, ketteLinks_kopf (d := z.kopf) hcf h.2.2⟩
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hek
  · rcases List.mem_cons.mp hF with rfl | hF
    · exact hck
    · exact h.2.1 F (List.mem_cons_of_mem _ hF)

/-- A pop: the caller frame (possibly with a new residue at the same held
    locks) becomes the head. -/
theorem haeltInvG_pop {z : RufFadenG D} (h : HaeltInvG z) {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (hpop : z.stapel = caller :: rst) (neu : RufRahmenG D)
    (spur' : List (Ereignis D)) (log' : List (RufEreignisF D))
    (hf : neu.f = caller.f)
    (hΛ : ∀ L, Res.held L ∈ neu.rest.2.2.1 → Res.held L ∈ caller.rest.2.2.1)
    (hk : neu.rest.2.2.2.2.kette (D.haelt neu.f))
    (ho : offen spur' = offen z.spur) :
    HaeltInvG ⟨rst, neu, spur', log'⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hpop] at h2 h3
  refine ⟨?_, ?_, ketteLinks_kopf (d := caller) hf h3.2⟩
  · intro L hL
    rw [ho]
    exact h1 L (GRest.kette_top _ (h2 z.kopf List.mem_cons_self) L (h3.1 L (hΛ L hL)))
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
  exact haeltInvG_pop h hpop caller spur' log' rfl (fun _ hL => hL) hc ho

/-- The callee frame a push creates is well-chained and its holdings are
    held, by `RufPasst.hh`. -/
theorem callee_kette (P : Programm D) (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D) :
    (⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩ :
      RufRahmenG D).rest.2.2.2.2.kette (D.haelt g) :=
  fun L hL => (held_anfang _ L).mpr hL

theorem callee_held {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {Λ : List (Res D)} (hp : RufPasst D V S Λ) {o : List D.Lock} (h : HeldIn Λ o) :
    HeldIn (Signatur.anfang D S) o :=
  fun L hL => h L ((hp.hh L).mpr ((held_anfang S L).mp hL))

theorem nach_nennt {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    {A : List D.Lock} (h : ∀ L ∈ A, Res.held L ∈ Λ) : ∀ L ∈ A, Res.held L ∈ nachSig D S Λ :=
  fun L hL => (held_nachSig_iff S Λ L).mpr (h L hL)

theorem nach_link {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {Λ : List (Res D)} (hp : RufPasst D V S Λ) : ∀ L, Res.held L ∈ nachSig D S Λ → L ∈ S.haelt :=
  fun L hL => (hp.hh L).mp ((held_nachSig_iff S Λ L).mp hL)

/-! ## 3. Every rule keeps the invariant -/

set_option maxHeartbeats 1000000 in
/-- **Every rule keeps the thread invariant of the acting thread.** -/
theorem rufSchrittG_haeltInv {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (h : HaeltInvG (M.faeden f)) : HaeltInvG (M'.faeden f) := by
  have hk0 := h.2.1 _ List.mem_cons_self
  have hh0 := h.1
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have ho : offen σ'.spur = offen (M.faeden f).spur :=
      (stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon f) ρ hΛ σ'
        (by rw [hstep]; rfl)).2.1
    refine haeltInvG_kopf h (nennt_stmt s hk) ?_
    rw [ho]; exact heldIn_stmt s hh
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl (nach_nennt hk) (nach_link hp)
      (callee_kette P g rho s0) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | rueck caller rst hpop Γ Λ e hperm ρ _ g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    simp only [rufUpdateG_self]
    exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨hk, nennt_stmt s hk⟩ hh
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have ho : offen σ'.spur = offen (M.faeden f).spur :=
      (stmt_gut O passes keinRuf keinRuf_gut hO s (M.weltVon f) ρ hΛ σ'
        (by rw [hstep]; rfl)).2.1
    refine haeltInvG_kopf h ⟨nennt_stmt s hk.1, hk.2⟩ ?_
    rw [ho]; exact heldIn_stmt s hh
  | dannLeer l Γ Λ k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h hk.2 hh
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, nennt_block t hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, nennt_block e hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, nennt_block p hk.1, nennt_block p hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, nennt_block a hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, nennt_block b hk.1, nennt_block b hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, nennt_block b hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, nennt_block b hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk ?_
    rw [hs₁, offen_lese]; exact hh
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk.1 ?_
    rw [hs₁, offen_lese]; exact hh
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk ?_
    rw [hs₁, offen_lese]; exact hh
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk.1 ?_
    rw [hs₁, offen_lese]; exact hh
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨hk.1, nennt_block body hk.1, hk.2⟩ hh
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have hL : Res.held L ∉ Λ := fun hm => hself (hh L hm)
    refine haeltInvG_kopf h ⟨fun K hK => List.mem_cons_of_mem _ (hk.1 K hK), hL, hk⟩ ?_
    intro K hK
    rcases List.mem_cons.mp hK with hK | hK
    · cases hK; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hh K hK)
  | freiGib l Γ Λ L k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk.2 ?_
    intro K hK
    have hKL : K ≠ L := fun e => hk.1 (e ▸ hK)
    exact (List.mem_erase_of_ne hKL).mpr (hh K (List.mem_cons_of_mem _ hK))
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h hk.2 hh
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨hk.1, hk.1, hk.2⟩ hh
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h hk hh
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk.2 ?_
    rw [hs₁, offen_lese]; exact hh
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨hk.1, hk.1, hk.2⟩ hh
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h hk hh
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk.2 ?_
    rw [hs₁, offen_lese]; exact hh
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h hk hh
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨hk.1, hk.1, hk.2⟩ hh
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h hk hh
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (nach_link hp)
      (callee_kette P g rho s0) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    subst hg
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (nach_link hp)
      (callee_kette P g rho s0) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    subst hg
    refine haeltInvG_push h _ _ _ _ rfl (nach_nennt hk) (nach_link hp)
      (callee_kette P g rho s0) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (nach_link hp)
      (callee_kette P g rho s0) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    subst hg
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (nach_link hp)
      (callee_kette P g rho s0) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (nach_link hp)
      (callee_kette P g rho s0) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ _ g hfg rho hrho s0
      hs0 hΛ s1 hs1 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck : (GRest.dann restb (.schrumpf k) :
        GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ hck (by rw [hs1, offen_lese]; rfl)
    intro L hL
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁
      hw neu₁ hneu₁ hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
    refine haeltInvG_kopf h hk.2.2 ?_
    rw [hs₁, offen_lese, e]; exact heldIn_block rest hh
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
    refine haeltInvG_kopf h hk.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
    refine haeltInvG_kopf h hk.2.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
    refine haeltInvG_kopf h hk.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
    refine haeltInvG_kopf h hk.2.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
    refine haeltInvG_kopf h hk.2 ?_
    rw [e]; exact heldIn_block rest hh
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨GRest.kette_top k hk.2.2, hk.2.2⟩
      (heldIn_block b (heldIn_block rest hh))
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨GRest.kette_top k hk.2.2, hk.2.2⟩
      (heldIn_block b (heldIn_block rest hh))
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ (heldIn_block rest hh)
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ (heldIn_block rest hh)
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ ?_
    intro K hK
    have hKL : K ≠ L := fun e => hk.2.1 (e ▸ hK)
    exact (List.mem_erase_of_ne hKL).mpr
      (heldIn_block rest hh K (List.mem_cons_of_mem _ hK))
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ ?_
    intro K hK
    have hKL : K ≠ L := fun e => hk.2.1 (e ▸ hK)
    exact (List.mem_erase_of_ne hKL).mpr
      (heldIn_block rest hh K (List.mem_cons_of_mem _ hK))
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    simp only [rufUpdateG_self]
    exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ _ g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
    simp only [rufUpdateG_self]
    exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck : (GRest.dann restb (.schrumpf k) :
        GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ hck (by rw [hs1, offen_lese]; rfl)
    intro L hL
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck : (GRest.dann restb (.schrumpf k) :
        GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ hck (by rw [hs1, offen_lese]; rfl)
    intro L hL
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
      hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck := (kette_von hcaller hc).1
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ hck rfl
    intro L hL
    rw [hcaller]; exact hL
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck := (kette_von hcaller hc).1
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ hck rfl
    intro L hL
    rw [hcaller]; exact hL
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck := (kette_von hcaller hc).1
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ hck rfl
    intro L hL
    rw [hcaller]; exact hL
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ hh
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk.1 ?_
    rw [hs₁, offen_lese]; exact hh
  | dannAwaits l Γ Λ Λ' g payload hp hL rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₂, offen_schreibGlob, hs₁, offen_lese]; exact hh
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ hh
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h hk.1 ?_
    rw [hs₁, offen_lese]; exact hh
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [axiom_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh

/-- The start machine satisfies the invariant: the start trace holds the
    signature locks, the entry residue names them. -/
theorem haeltInvG_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    HaeltInvG ((RufStartG P sp init).faeden t) := by
  show HaeltInvG (match init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
        Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D))
  cases init t with
  | mk g rho =>
    refine ⟨?_, ?_, trivial⟩
    · intro L hL
      exact (offen_startSpur g L).mpr ((held_anfang _ L).mp hL)
    · intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact fun L hL => (held_anfang _ L).mpr hL
      · exact absurd hF List.not_mem_nil

/-- The invariant holds at every thread of every reachable machine. -/
theorem rufG_haeltInv {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) : ∀ t, HaeltInvG (M.faeden t) := by
  induction h with
  | start => exact haeltInvG_start P sp init
  | schritt M M' g _ hs ih =>
      intro t
      by_cases htg : t = g
      · subst htg
        exact rufSchrittG_haeltInv hO hs (ih t)
      · rw [rufSchrittG_passt_anders P O passes M M' g t htg hs]
        exact ih t

/-- **STATIC HOLDINGS ARE HELD (`rufG_haelt_statisch`).** On every machine
    reachable from the start, for every thread `t` and every frame `F` on
    its stack -- the head and every suspended caller -- every lock the
    frame's static holdings name (`Res.held L ∈ Λ` of its residue) is held
    by `t` (`L ∈ offen` of its trace). The only assumption is `GutO` (the
    oracle keeps the held locks). -/
theorem rufG_haelt_statisch {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (t : Faden) :
    ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, ∀ L : D.Lock,
      Res.held L ∈ F.rest.2.2.1 → L ∈ offen (M.faeden t).spur :=
  (rufG_haeltInv hO sp init h t).alle

/-- **Signature locks are held for the whole life of a frame.** Every
    frame on a reachable stack holds every lock of its function's signature
    (`requires Held(L)`), from entry to return. -/
theorem rufG_haelt_signatur {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (t : Faden) :
    ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, ∀ L ∈ D.haelt F.f,
      L ∈ offen (M.faeden t).spur :=
  (rufG_haeltInv hO sp init h t).signatur

/-! ## CUTS:

  What is proved: on every machine of the repaired G reachable from ANY
  start (any program, oracle with `GutO`, start memory and start
  assignment), every frame on every stack names in its static holdings
  only locks its thread holds (`rufG_haelt_statisch`), in particular its
  function's signature locks (`rufG_haelt_signatur`); the thread invariant
  `HaeltInvG` is kept by every one of the 70 rules
  (`rufSchrittG_haeltInv`).

  What is NOT proved here: exclusivity of held locks across threads needs
  a fact about the start assignment (`StartExklusiv`) and is in
  `ZielOrt.lean` (`exklusivG`); exactness of the head's holdings
  (`HeldGenau`, not only `⊆`) is a premise of the rules, not proved as an
  invariant (it is not needed: every rule that uses it demands it).
-/

#print axioms Gabbro.Grammatik.rufSchrittG_haeltInv
#print axioms Gabbro.Grammatik.rufG_haelt_statisch
#print axioms Gabbro.Grammatik.rufG_haelt_signatur

end Gabbro.Grammatik
