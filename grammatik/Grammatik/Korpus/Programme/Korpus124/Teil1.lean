module

public import Grammatik.Zielsatz.Kern.Proben

@[expose] public section



namespace Gabbro.Grammatik

namespace K124

/-! ## 1. The declaration -/

inductive KTab where
  | konto
  | privA
  | privB
  deriving DecidableEq

inductive KFn where
  | setze
  | hauptA
  | hauptB
  | pruefeA
  deriving DecidableEq

/-- A signature: parameters, result, signature locks, written tables. -/
def kSig (ps : List Ty) (e : Option Ty) (h : List Unit) (ts : List KTab) :
    Signatur KTab Empty Unit Empty where
  params := ps
  erg := e
  gruende := 0
  haelt := h
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def kBraucht : KTab → List (Unit ⊕ (Empty × Nat))
  | .konto => [.inl ()]
  | _ => []

def kGeteilt : KTab → Bool
  | .konto => true
  | _ => false

def kSigNr : Nat → Signatur KTab Empty Unit Empty
  | 0 => kSig [.int 0 100] none [()] [.konto]
  | 1 => kSig [] none [] [.konto, .privA]
  | 2 => kSig [] none [] [.konto, .privB]
  | 3 => kSig [] (some (.int 0 100)) [] []
  | _ => kSig [] none [] []

def kSigOf : KFn → Nat
  | .setze => 0
  | .hauptA => 1
  | .hauptB => 2
  | .pruefeA => 3

/-- The declaration of `beispiele/124`: tables `konto` (shared, guarded by the
    lock `L = ()`), `privA`, `privB` (not shared), two slots each, `Stand =
    u32 in 0 .. 100`; no global, no table invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := KTab
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := kGeteilt
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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

def kSetze : kD.Fn := KFn.setze
def kHauptA : kD.Fn := KFn.hauptA
def kHauptB : kD.Fn := KFn.hauptB
def kPruefeA : kD.Fn := KFn.pruefeA

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq KFn)

abbrev kL : List (Res kD) := [Res.held (D := kD) ()]

theorem kDarfK : darf kD KTab.konto kL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem kDarfA (Λ : List (Res kD)) : darf kD KTab.privA Λ := fun _ h => nomatch h
theorem kDarfB (Λ : List (Res kD)) : darf kD KTab.privB Λ := fun _ h => nomatch h

def kI0 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.index 2) :=
  .widen (by decide) (by decide) (.lit 0)

def kI1 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.index 2) :=
  .widen (by decide) (by decide) (.lit 1)

def k7 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 7)
def k5 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 5)
def k30 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 30)
def k70 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 70)

/-- `konto[0] == konto[1]` (the lock invariant), at the holdings `kL`. -/
def kGleich {Γ : Ctx} : Expr kD Γ kL .bool :=
  .eq (.slot KTab.konto () kI0 kDarfK) (.slot KTab.konto () kI1 kDarfK)

/-- `privA[0] == 7`. -/
def kA7 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ .bool :=
  .eq (.slot KTab.privA () kI0 (kDarfA Λ)) k7

/-! ## 2. The program -/

/-- The call-site typing of every call. -/
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
  hk := by rw [hk]; exact ⟨[], List.Perm.refl [], by simp only [List.nil_sublist]⟩
  hh := hh
  hx := fun L hL hn => absurd (hx L hL) hn

theorem kHpSetzeA : RufPasst kD (vertragVon kD kHauptA) (kD.signatur kSetze) kL :=
  kHp kHauptA kSetze (fun t h => by cases t <;> simp_all [kD, kSetze, kHauptA, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl)
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl) rfl rfl

theorem kHpSetzeB : RufPasst kD (vertragVon kD kHauptB) (kD.signatur kSetze) kL :=
  kHp kHauptB kSetze (fun t h => by cases t <;> simp_all [kD, kSetze, kHauptB, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl)
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl) rfl rfl

theorem kHpPruefe : RufPasst kD (vertragVon kD kHauptA) (kD.signatur kPruefeA) [] :=
  kHp kHauptA kPruefeA (fun t h => by cases t <;> simp_all [kD, kPruefeA, Deklaration.signatur,
    kSigNr, kSigOf, kSig])
    (fun L h => nomatch h) (fun L h => nomatch h) rfl rfl

/-- `setze(x)`: `konto.slots[0].stand = x; konto.slots[1].stand = x;`. -/
def kRumpfSetze : Endblock kD (vertragVon kD kSetze) false [.int 0 100] kL :=
  .cons (.assignSlot KTab.konto () kI0 (.var .here) rfl kDarfK)
    (.cons (.assignSlot KTab.konto () kI1 (.var .here) rfl kDarfK) (.ret .empty (by rfl)))

/-- `pruefeA()`: `return privA.slots[0].stand;`. -/
def kRumpfP : Endblock kD (vertragVon kD kPruefeA) false [] [] :=
  .ret (.val (.slot KTab.privA () kI0 (kDarfA _))) List.Perm.nil

/-- `privA.slots[0].stand = 7;` -/
def kA0 : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .assignSlot KTab.privA () kI0 k7 rfl (kDarfA _)

/-- `privA.slots[1].stand = 7;` -/
def kA1 : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .assignSlot KTab.privA () kI1 k7 rfl (kDarfA _)

/-- The call `setze(30)` inside `hauptA`'s lock. -/
def kRufA : Stmt kD (vertragVon kD kHauptA) false [] kL kL :=
  .call kSetze (.cons k30 .nil) kHpSetzeA rfl

/-- `hauptA`'s `locks L { setze(30); }`. -/
def kLocksA : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons kRufA .nil)

/-- `pruefeA();` (the answer dropped). -/
def kRufP : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .call kPruefeA .nil kHpPruefe rfl

/-- `pruefeA(); return` -- the tail of `hauptA`. -/
def kRestA : Endblock kD (vertragVon kD kHauptA) false [] [] :=
  .cons kRufP (.ret .empty List.Perm.nil)

/-- `hauptA`, as in the source. -/
def kRumpfA : Endblock kD (vertragVon kD kHauptA) false [] [] :=
  .cons kA0 (.cons kA1 (.cons kLocksA kRestA))

/-- `privB.slots[0].stand = 5;` -/
def kB0 : Stmt kD (vertragVon kD kHauptB) false [] [] [] :=
  .assignSlot KTab.privB () kI0 k5 rfl (kDarfB _)

/-- The call `setze(70)` inside `hauptB`'s lock. -/
def kRufB : Stmt kD (vertragVon kD kHauptB) false [] kL kL :=
  .call kSetze (.cons k70 .nil) kHpSetzeB rfl

/-- `hauptB`'s `locks L { setze(70); }`. -/
def kLocksB : Stmt kD (vertragVon kD kHauptB) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons kRufB .nil)

/-- `hauptB`, as in the source. -/
def kRumpfB : Endblock kD (vertragVon kD kHauptB) false [] [] :=
  .cons kB0 (.cons kLocksB (.ret .empty List.Perm.nil))

/-- **The program of `beispiele/124`**: the source's bodies and the source's
    contracts (`setze`'s `ensures` matches the source since lane 204; see the
    header for the history). -/
def kP : Programm kD where
  invariante := fun i => nomatch i
  requires
    | .setze => kGleich
    | .pruefeA => kA7
    | _ => .tru
  ensures
    | .setze => .and kGleich (.eq (.slot KTab.konto () kI0 kDarfK) (.var .here))
    | .hauptA => kA7
    | .pruefeA => .eq (.var .here) k7
    | _ => .tru
  rumpf
    | .setze => kRumpfSetze
    | .hauptA => kRumpfA
    | .hauptB => kRumpfB
    | .pruefeA => kRumpfP

def kFs : List kD.Fn := [kSetze, kHauptA, kHauptB, kPruefeA]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The lock invariant `konto[0] == konto[1]`**, protecting `konto`. -/
def kSI : SperrInv kD :=
  ⟨fun _ => [.inl KTab.konto], fun _ s => decide ((s.slots KTab.konto 0 ()).n = (s.slots KTab.konto 1 ()).n)⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => ?_⟩
  · cases L
    rw [List.mem_singleton.mp hc]
    exact List.mem_singleton.mpr rfl
  · have e : s.slots KTab.konto = s'.slots KTab.konto := h (.inl KTab.konto) List.mem_cons_self
    show decide ((s.slots KTab.konto 0 ()).n = (s.slots KTab.konto 1 ()).n) =
      decide ((s'.slots KTab.konto 0 ()).n = (s'.slots KTab.konto 1 ()).n)
    rw [e]

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([()] : List kD.Lock) := fun L => by
  cases L; exact List.mem_singleton_self _

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inl KTab.konto, .inl KTab.privA, .inl KTab.privB]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · cases t <;> simp only [kCs, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
  · exact nomatch g

/-- **The checker accepts the program** with its declared starts `hauptA`,
    `hauptB` (`concurrent { hauptA, hauptB }`). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [()] kCs [kHauptA, kHauptB] = true := by decide

/-! ## 3. The user obligations -/

theorem kA_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kHauptA)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfA σ ρ =
        execEndH S O U passes R (.cons kLocksA kRestA) σ2 ρ ∧
      (σ2.slots KTab.privA 0 ()).n = 7 ∧ (σ2.slots KTab.privA 1 ()).n = 7 :=
  ⟨_, rfl, rfl, rfl⟩

theorem kInv_of_ens {κ σ2 : World kD} {ρk : Env kD (kD.params kSetze)}
    {v : ErgVal kD (kD.erg kSetze)} (h : EnsAmRueck kP kSetze κ σ2 ρk v) :
    kSI.inv () σ2.speicher = true := by
  have h' : (decide ((σ2.slots KTab.konto 0 ()).n = (σ2.slots KTab.konto 1 ()).n) &&
      decide ((σ2.slots KTab.konto 0 ()).n = (ρk.get .here).n)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1

theorem kA_req {W : World kD} (h : (W.slots KTab.privA 0 ()).n = 7) :
    ReqAmEintritt kP kPruefeA W .nil := by
  show decide ((W.slots KTab.privA 0 ()).n = 7) = true
  simp only [h, decide_true]

theorem kA_lauf {O : Orakel kD} {U : Umwelt kD} (hU : HavocOk kSI U)
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (hR : RespektiertRahmen kP R)
    (σ : World kD) (ρ : Env kD (kD.params kHauptA)) {σ' : World kD} {v : ErgVal kD (kD.erg kHauptA)}
    (hrun : execEndH kSI O U 0 R kRumpfA σ ρ = .zurueck σ' v) :
    (σ'.slots KTab.privA 0 ()).n = 7 := by
  obtain ⟨σ2, e2, h20, _⟩ := kA_schreib (S := kSI) (O := O) (U := U) (passes := 0) (R := R) σ ρ
  rw [e2] at hrun
  simp only [execEndH, kLocksA] at hrun
  erw [execStmtH_locks_eins] at hrun
  have hU2 : (U () σ2).slots KTab.privA = σ2.slots KTab.privA :=
    (hU () σ2).2.1 (.inl KTab.privA) (fun h => by have := List.mem_singleton.mp h; cases this)
  rcases execStmtH_call_fall (S := kSI) (O := O) (U := U) (passes := 0) (R := R)
    (l := false) (Γ := []) kSetze (.cons k30 .nil) kHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
    ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
  · have hf1 := (hR.2 _ _ _ _ _ hR1).1.1 KTab.privA rfl
    cases hi : kSI.inv () σ1.speicher with
    | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
    | true =>
      simp only [freiH, hi, if_true] at hrun
      simp only [kRestA, kRufP, execEndH] at hrun
      rcases execStmtH_call_fall (S := kSI) (O := O) (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) kPruefeA .nil kHpPruefe rfl (σ1.gibt ()) ρ with
        ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
      · simp only at hrun
        cases hrun
        have hf3 := (hR.2 _ _ _ _ _ hR3).1.1 KTab.privA rfl
        have e0 : σ3.slots KTab.privA 0 () = σ2.slots KTab.privA 0 () :=
          (hf3 0 ()).trans ((hf1 0 ()).trans (congrFun (congrFun hU2 0) ()))
        show (σ3.slots KTab.privA 0 ()).n = 7
        rw [e0]
        exact h20
      · cases hrun
      · cases hrun
  · simp only [freiH] at hrun; cases hrun
  · simp only [freiH] at hrun; cases hrun

/-- `hauptA`: `ensures privA[0] == 7` from its write (the lock's move and the
    callees' frames leave `privA` alone); the caller duty of both calls from
    the lock invariant at the acquire and from the frames; no `logik` outcome
    because the release check follows from `setze`'s `ensures`. -/
theorem kP_koerper_A : KoerperGutS kP 0 (axWahr kD) kSI kHauptA := by
  have hr : kP.rumpf kHauptA = kRumpfA := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    have h := kA_lauf hU hR σ ρ hrun
    show decide ((σ'.slots KTab.privA 0 ()).n = 7) = true
    simp only [h, decide_true]
  · rw [hr] at hrun
    obtain ⟨σ2, e2, h20, _⟩ := kA_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hU2 : (U () σ2).slots KTab.privA = σ2.slots KTab.privA :=
      (hU () σ2).2.1 (.inl KTab.privA) (fun h => by have := List.mem_singleton.mp h; cases this)
    have hreq : ReqAmEintritt kP kSetze (((U () σ2).nimmt ()).lese kL [])
        (evalArgs (((U () σ2).nimmt ()).lese kL []) (Args.cons (Λ := kL) (Γ := []) k30 .nil)
          (((U () σ2).nimmt ()).lese kL []) ρ) := (hU () σ2).2.2
    have htor : ∀ w a, ReqAmEintritt kP kSetze w a → torRuf kP R kSetze w a = R kSetze w a :=
      fun _ _ h => if_pos h
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kSetze (.cons k30 .nil) kHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hR1' := (htor _ _ hreq).symm.trans hR1
      have hf1 := (hR.2 _ _ _ _ _ hR1').1.1 KTab.privA rfl
      cases hi : kSI.inv () σ1.speicher with
      | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
      | true =>
        simp only [freiH, hi, if_true] at hrun
        simp only [kRestA, kRufP, execEndH] at hrun
        have e0 : ((σ1.gibt ()).lese [] []).slots KTab.privA 0 () = σ2.slots KTab.privA 0 () :=
          (hf1 0 ()).trans (congrFun (congrFun hU2 0) ())
        have hreq3 : ReqAmEintritt kP kPruefeA ((σ1.gibt ()).lese [] []) .nil :=
          kA_req (by rw [e0]; exact h20)
        rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
          (l := false) (Γ := []) kPruefeA .nil kHpPruefe rfl (σ1.gibt ()) ρ with
          ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
        · cases hrun
        · cases hrun
          have htor3 : torRuf kP R kPruefeA ((σ1.gibt ()).lese [] []) .nil =
              R kPruefeA ((σ1.gibt ()).lese [] []) .nil := if_pos hreq3
          exact hOV _ _ _ _ (htor3.symm.trans he3) g rfl
        · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOV _ _ _ _ ((htor _ _ hreq).symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2, _, _⟩ := kA_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kSetze (((U () σ2).nimmt ()).lese kL [])
        (evalArgs (((U () σ2).nimmt ()).lese kL []) (Args.cons (Λ := kL) (Γ := []) k30 .nil)
          (((U () σ2).nimmt ()).lese kL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kSetze (.cons k30 .nil) kHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv := kInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      simp only [kRestA, kRufP, execEndH] at hrun
      rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) kPruefeA .nil kHpPruefe rfl (σ1.gibt ()) ρ with
        ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
      · cases hrun
      · cases hrun
        exact hOL _ _ _ _ he3
      · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem kB_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kHauptB)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfB σ ρ =
        execEndH S O U passes R (.cons kLocksB (.ret .empty List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

end K124
end Gabbro.Grammatik
