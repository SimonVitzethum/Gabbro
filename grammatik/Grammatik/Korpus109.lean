/-
  File:      Grammatik/Korpus109.lean
  Subject:   THE G PROGRAM OF `beispiele/109-lockfree-entry-roots.gab`, with the
             bodies of the source, and every premise group of the goal theorem on it.

  The source: tables `T`, `U` (count 4, `u32` field `v`), locks `L`, `M`
  (ranks 0/1, disjoint carriers), leaves `write_a`/`write_b` (`requires Held`,
  one slot write of a constant), distributors `distribute_a`/`distribute_b`
  (`locks` around one call), two `entry` items dispatching to the
  distributors. Every form has a G counterpart: index params are
  `Ty.index (count)`, `requires Held` is the signature-held set, `locks`
  blocks and direct calls are `Stmt`, the entry dispatch roots are the
  declared starts, `costs` is ignored form (like `reads`). No annotation is
  dropped: 109 carries no `deadline`/`falsifier`. No lock invariant is
  declared in the source, so the family is trivially true (owed nowhere).
-/
import Grammatik.Zielsatz.Proben

namespace Gabbro.Grammatik

namespace K109

/-- Tables `T` and `U` of the source. -/
inductive KTab where
  | t
  | u
  deriving DecidableEq

/-- Locks `L` (rank 0, protects `T`) and `M` (rank 1, protects `U`). -/
inductive KLock where
  | l
  | m
  deriving DecidableEq

/-- Functions `write_a`, `distribute_a`, `write_b`, `distribute_b`. -/
inductive KFn where
  | writeA
  | distA
  | writeB
  | distB
  deriving DecidableEq

/-- A signature: parameters, result, signature locks, written tables. -/
def kSig (ps : List Ty) (e : Option Ty) (h : List KLock) (ts : List KTab) :
    Signatur KTab Empty KLock Empty where
  params := ps
  erg := e
  gruende := 0
  haelt := h
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def kBraucht : KTab → List (KLock ⊕ (Empty × Nat))
  | .t => [.inl .l]
  | .u => [.inl .m]

/-- Both tables are shared, each guarded by its lock. -/
def kGeteilt : KTab → Bool
  | _ => true

def kRang : KLock → Int
  | .l => 0
  | .m => 1

def kSigNr : Nat → Signatur KTab Empty KLock Empty
  | 0 => kSig [Ty.index 4] none [.l] [.t]
  | 1 => kSig [] none [] [.t]
  | 2 => kSig [Ty.index 4] none [.m] [.u]
  | 3 => kSig [] none [] [.u]
  | _ => kSig [] none [] []

def kSigOf : KFn → Nat
  | .writeA => 0
  | .distA => 1
  | .writeB => 2
  | .distB => 3

/-- The declaration of `beispiele/109`: tables `T`, `U` (shared, guarded by
    `L`/`M`), two slots... four slots each, `v = u32`; no global, no table
    invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := KTab
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 4294967295
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := kGeteilt
  ggeteilt := fun e => nomatch e
  Lock := KLock
  decLock := inferInstance
  rang := kRang
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := kBraucht
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := KFn
  sig := kSigOf
  sigNr := kSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by cases t <;> simp_all [kGeteilt, kBraucht]
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def kWriteA : kD.Fn := KFn.writeA
def kDistA : kD.Fn := KFn.distA
def kWriteB : kD.Fn := KFn.writeB
def kDistB : kD.Fn := KFn.distB

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq KFn)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq KLock)

abbrev kLA : List (Res kD) := [Res.held (D := kD) KLock.l]
abbrev kLB : List (Res kD) := [Res.held (D := kD) KLock.m]

theorem kDarfTA : darf kD KTab.t kLA := by
  intro w h
  change w ∈ ([Sum.inl KLock.l] : List (KLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl KLock.l := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem kDarfUB : darf kD KTab.u kLB := by
  intro w h
  change w ∈ ([Sum.inl KLock.m] : List (KLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl KLock.m := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- The index literal `0` (call argument and slot index). -/
def kJ0 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (Ty.index 4) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- The constants the leaves write. -/
def kEins {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 4294967295) :=
  .weiter (by decide) (by decide) (.lit 1)

def kZwei {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 4294967295) :=
  .weiter (by decide) (by decide) (.lit 2)

/-- The call-site typing of every call. -/
theorem kHaeltWriteA : (kD.signatur kWriteA).haelt = [KLock.l] := rfl

theorem kHaeltWriteB : (kD.signatur kWriteB).haelt = [KLock.m] := rfl

theorem kHp (caller callee : kD.Fn) {Λ : List (Res kD)}
    (hw : ∀ t, (kD.signatur callee).schreibt t = true → (vertragVon kD caller).schreibt t = true)
    (hh : ∀ L, L ∈ (kD.signatur callee).haelt → Res.held L ∈ Λ)
    (hx : ∀ L, Res.held L ∈ Λ → L ∈ (kD.signatur callee).haelt)
    (hk : (kD.signatur callee).konsumiert = []) (hbc : (kD.signatur caller).boden = none) :
    RufPasst kD (vertragVon kD caller) (kD.signatur callee) Λ where
  hw := hw
  hg := fun g => nomatch g
  hb := fun c hc => by
    have : (vertragVon kD caller).boden = (kD.signatur caller).boden := rfl
    rw [this, hbc] at hc; cases hc
  hk := by rw [hk]; exact ⟨[], List.Perm.refl [], by simp⟩
  hh := hh
  hx := fun L hL hn => absurd (hx L hL) hn

theorem kHpWriteA : RufPasst kD (vertragVon kD kDistA) (kD.signatur kWriteA) kLA :=
  kHp kDistA kWriteA (fun t h => by cases t <;> simp_all [kD, kWriteA, kDistA, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L hL => by cases L with
      | l => exact List.mem_singleton.mpr rfl
      | m => rw [kHaeltWriteA] at hL; exact KLock.noConfusion (List.mem_singleton.mp hL))
    (fun L hL => by
      have h2 : Res.held L = Res.held KLock.l := List.mem_singleton.mp hL
      have h3 : L = KLock.l := by cases h2; rfl
      rw [h3, kHaeltWriteA]; exact List.mem_singleton.mpr rfl) rfl rfl

theorem kHpWriteB : RufPasst kD (vertragVon kD kDistB) (kD.signatur kWriteB) kLB :=
  kHp kDistB kWriteB (fun t h => by cases t <;> simp_all [kD, kWriteB, kDistB, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L hL => by cases L with
      | l => rw [kHaeltWriteB] at hL; exact KLock.noConfusion (List.mem_singleton.mp hL)
      | m => exact List.mem_singleton.mpr rfl)
    (fun L hL => by
      have h2 : Res.held L = Res.held KLock.m := List.mem_singleton.mp hL
      have h3 : L = KLock.m := by cases h2; rfl
      rw [h3, kHaeltWriteB]; exact List.mem_singleton.mpr rfl) rfl rfl

/-- `write_a(i)`: `T.slots[i].v = 1;`. -/
def kRumpfWriteA : Endblock kD (vertragVon kD kWriteA) false [Ty.index 4] kLA :=
  .cons (.assignSlot KTab.t () (.var .hier) kEins rfl kDarfTA)
    (.ret .keine (by rfl))

/-- `write_b(i)`: `U.slots[i].v = 2;`. -/
def kRumpfWriteB : Endblock kD (vertragVon kD kWriteB) false [Ty.index 4] kLB :=
  .cons (.assignSlot KTab.u () (.var .hier) kZwei rfl kDarfUB)
    (.ret .keine (by rfl))

/-- The call `write_a(0)` inside `distribute_a`'s lock. -/
def kRufA : Stmt kD (vertragVon kD kDistA) false [] kLA kLA :=
  .call kWriteA (.cons kJ0 .nil) kHpWriteA rfl

/-- `distribute_a`'s `locks L { write_a(0); }`. -/
def kLocksA : Stmt kD (vertragVon kD kDistA) false [] [] [] :=
  .locks KLock.l (fun _ h => nomatch h) (.cons kRufA .nil)

/-- `distribute_a`, as in the source. -/
def kRumpfDistA : Endblock kD (vertragVon kD kDistA) false [] [] :=
  .cons kLocksA (.ret .keine List.Perm.nil)

/-- The call `write_b(0)` inside `distribute_b`'s lock. -/
def kRufB : Stmt kD (vertragVon kD kDistB) false [] kLB kLB :=
  .call kWriteB (.cons kJ0 .nil) kHpWriteB rfl

/-- `distribute_b`'s `locks M { write_b(0); }`. -/
def kLocksB : Stmt kD (vertragVon kD kDistB) false [] [] [] :=
  .locks KLock.m (fun _ h => nomatch h) (.cons kRufB .nil)

/-- `distribute_b`, as in the source. -/
def kRumpfDistB : Endblock kD (vertragVon kD kDistB) false [] [] :=
  .cons kLocksB (.ret .keine List.Perm.nil)

/-- **The program of `beispiele/109`**: the source's bodies; trivial contracts
    (the source declares no `requires`/`ensures` on these four functions). -/
def kP : Programm kD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .writeA => kRumpfWriteA
    | .distA => kRumpfDistA
    | .writeB => kRumpfWriteB
    | .distB => kRumpfDistB

def kFs : List kD.Fn := [kWriteA, kDistA, kWriteB, kDistB]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The lock family**: `L` protects `T`, `M` protects `U`; the source
    declares no invariant, so both are trivially true. -/
def kSI : SperrInv kD :=
  ⟨fun | KLock.l => [.inl KTab.t] | KLock.m => [.inl KTab.u], fun _ _ => true⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => rfl⟩
  · cases L
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([KLock.l, KLock.m] : List kD.Lock) := fun L => by
  cases L
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inl KTab.t, .inl KTab.u]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · cases t <;> simp [kCs]
  · exact nomatch g

/-- **The checker accepts the program** with its declared starts
    `distribute_a`, `distribute_b` (the two entry dispatch roots). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [KLock.l, KLock.m] kCs [kDistA, kDistB] = true := by decide

/-! ## 3. The user obligations -/

/-- Every `requires` is `.wahr`, at every function, world and environment. -/
theorem kReqWahr (f : kD.Fn) (W : World kD) (ρ : Env kD (kD.params f)) :
    ReqAmEintritt kP f W ρ := rfl

theorem kP_koerper_writeA : KoerperGutS kP 0 (axWahr kD) kSI kWriteA := by
  have hr : kP.rumpf kWriteA = kRumpfWriteA := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfWriteA, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfWriteA, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfWriteA, execEndH, execStmtH] at hrun
    cases hrun

theorem kP_koerper_writeB : KoerperGutS kP 0 (axWahr kD) kSI kWriteB := by
  have hr : kP.rumpf kWriteB = kRumpfWriteB := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfWriteB, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfWriteB, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfWriteB, execEndH, execStmtH] at hrun
    cases hrun

theorem kDistA_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kDistA)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfDistA σ ρ =
        execEndH S O U passes R (.cons kLocksA (.ret .keine List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

theorem kDistB_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kDistB)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfDistB σ ρ =
        execEndH S O U passes R (.cons kLocksB (.ret .keine List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

/-- `distribute_a`: `ensures` is `.wahr`; the caller duty of the call from the
    trivial `requires`; no `logik` outcome because the release check is the
    trivially-true invariant. -/
theorem kP_koerper_distA : KoerperGutS kP 0 (axWahr kD) kSI kDistA := by
  have hr : kP.rumpf kDistA = kRumpfDistA := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistA_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kWriteA (((U KLock.l σ2).nimmt KLock.l).lese kLA [])
        (evalArgs (((U KLock.l σ2).nimmt KLock.l).lese kLA []) (Args.cons (Λ := kLA) (Γ := []) kJ0 .nil)
          (((U KLock.l σ2).nimmt KLock.l).lese kLA []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kWriteA (.cons kJ0 .nil) kHpWriteA rfl ((U KLock.l σ2).nimmt KLock.l) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.l σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kWriteA _ _ = R kWriteA _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistA_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kWriteA (.cons kJ0 .nil) kHpWriteA rfl ((U KLock.l σ2).nimmt KLock.l) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.l σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

/-- `distribute_b`: the mirror image over `M`/`U`. -/
theorem kP_koerper_distB : KoerperGutS kP 0 (axWahr kD) kSI kDistB := by
  have hr : kP.rumpf kDistB = kRumpfDistB := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistB_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kWriteB (((U KLock.m σ2).nimmt KLock.m).lese kLB [])
        (evalArgs (((U KLock.m σ2).nimmt KLock.m).lese kLB []) (Args.cons (Λ := kLB) (Γ := []) kJ0 .nil)
          (((U KLock.m σ2).nimmt KLock.m).lese kLB []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kWriteB (.cons kJ0 .nil) kHpWriteB rfl ((U KLock.m σ2).nimmt KLock.m) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.m σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kWriteB _ _ = R kWriteB _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kDistB_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kWriteB (.cons kJ0 .nil) kHpWriteB rfl ((U KLock.m σ2).nimmt KLock.m) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.m σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem kP_koerper : ∀ f : kD.Fn, KoerperGutS kP 0 (axWahr kD) kSI f := by
  intro f
  cases f
  · exact kP_koerper_writeA
  · exact kP_koerper_distA
  · exact kP_koerper_writeB
  · exact kP_koerper_distB

theorem kP_inv : ∀ f : kD.Fn, InvGutS kP 0 (axWahr kD) kSI f :=
  fun _ => invGutS_ohne fun i _ => nomatch i

theorem kP_ohneEwig : ohneEwigB kP kFs = true := by decide

theorem kP_koerper_alle : ∀ (passes : Nat) (f : kD.Fn), KoerperGutS kP passes (axWahr kD) kSI f :=
  koerperGutS_alle kFs_voll kP_ohneEwig kP_koerper

theorem kP_inv_alle : ∀ (passes : Nat) (f : kD.Fn), InvGutS kP passes (axWahr kD) kSI f :=
  invGutS_alle kFs_voll kP_ohneEwig kP_inv

/-! ## 4. The program as one declaration, and every premise group -/

/-- The start memory: every slot zero. -/
def kSp : Speicher kD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- **`beispiele/109` as ONE declaration**: code `kP`, lock family `kSI`,
    no axiom, declared starts `distribute_a` and `distribute_b` (the two
    entry dispatch roots, no parameters), initial memory all zero. -/
def kE : Zielsatz.Einheit kD := ⟨kP, kSI, axWahr kD, [⟨kDistA, .nil⟩, ⟨kDistB, .nil⟩], kSp, []⟩

theorem korpus109_nutzer : Zielsatz.NutzerPflicht kE :=
  ⟨⟨fun passes f => ⟨kP_koerper_alle passes f, kP_inv_alle passes f,
      invGutGrund_ohneGrund (by cases f <;> rfl)⟩, fun _ _ _ _ => rfl, axEnsLokal_wahr⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [kE, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl⟩⟩

/-- No axiom, no register, no global: the oracle is empty. -/
def kO : Orakel kD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem kO_gut : GutO kO := fun a => nomatch a

theorem kO_lokal : RegLokal kO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

theorem kO_hw : Zielsatz.HardwareAnnahmen kO kE.Q := ⟨kO_gut, kO_lokal, axVertragO_wahr kO⟩

theorem kE_akzeptiert : akzeptiert_pruefer.akzeptiert kE kFs [KLock.l, KLock.m] kCs = true :=
  (by show Akzeptiert kP kSI kFs [KLock.l, KLock.m] kCs [kDistA, kDistB] = true; exact kP_akzeptiert)

/-- **The goal theorem on `beispiele/109`**: for every oracle meeting (c), every
    budget, every runtime start meeting (d), and every reachable machine of
    `kP.mitRuhe`, the conclusion `Ziel` holds -- `gabbro_ziel` with the
    concrete checker. -/
theorem korpus109_ziel (O : Orakel kD) (hO : Zielsatz.HardwareAnnahmen O kE.Q) (passes : Nat)
    (sp : Speicher kD.mitRuhe)
    (init : Faden → Σ f : kD.mitRuhe.Fn, Env kD.mitRuhe (kD.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit kE sp init) (M : RufMaschineG kD.mitRuhe)
    (hM : RufErreichbarG kE.P.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M) :
    Zielsatz.Ziel kE.P.mitRuhe kE.S.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M :=
  Zielsatz.gabbro_ziel_g akzeptiert_pruefer kD kE ⟨kFs, kFs_voll⟩ ⟨[KLock.l, KLock.m], kLocks_voll⟩ ⟨kCs, kCs_voll⟩
    kE_akzeptiert korpus109_nutzer O hO passes sp init hL M hM

/-- The index-`0` environment for the witness run. -/
def kRho0 : Env kD [Ty.index 4] := .cons ⟨0, by decide, by decide⟩ .nil

/-- **Witness for `korpus109_nutzer`** (rule 13): the premise group jointly
    with a non-degenerate run -- `write_a`'s body from the all-zero world
    returns with `T[0] = 1` while it started `0`: a reached run with a
    memory-changing step, on a table a function writes. -/
theorem korpus109_nutzer_zeuge
    (R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f) :
    Zielsatz.NutzerPflicht kE ∧ ∃ (σ' : World kD) (v : ErgVal kD (kD.erg kWriteA)),
      execEndH kSI kO (fun _ σ => σ) 0 R kRumpfWriteA (kSp.welt []) kRho0 = .zurueck σ' v ∧
      (σ'.slots KTab.t 0 ()).n = 1 ∧ ((kSp.welt []).slots KTab.t 0 ()).n = 0 :=
  ⟨korpus109_nutzer, _, _, rfl, rfl, rfl⟩

/-
  CUTS: nothing is cut inside this file. The model covers the whole source
  file `beispiele/109-lockfree-entry-roots.gab` except its `costs` effects
  (ignored form, like `reads`) and the `entry` register/stack hardware around
  the two dispatch roots (the roots themselves are the declared starts).
  What is NOT claimed: anything about the `.gab` source text (no exporter
  link yet -- lane 201), and no stage-(b) simulation certificate.
-/
#print axioms K109.kP_akzeptiert
#print axioms K109.korpus109_nutzer
#print axioms K109.korpus109_ziel
#print axioms K109.korpus109_nutzer_zeuge

end K109

end Gabbro.Grammatik
