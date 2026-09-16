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

end K109

end Gabbro.Grammatik
