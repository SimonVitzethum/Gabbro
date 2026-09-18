/-
  File:      Grammatik/Korpus59.lean
  Subject:   THE G PROGRAM OF `beispiele/59-eintritt-nimmt-maskierte-sperre.gab`,
             with the bodies of the source, and every premise group of the goal
             theorem on it.

  The source: two modules. `takt`: table `Takte` (count 64, `u64` field
  `stand`), lock `TAKT` (rank 0, `masks irqs`), leaf `zaehle` (`requires Held`,
  one slot write of `1`), distributor `takt_verteiler` (`locks TAKT` around
  `zaehle(0)`), one `entry` dispatching to it. `ruf`: table `Auftraege`
  (count 16), lock `RING` (rank 0, no mask), leaf `bearbeite`, distributor
  `ruf_verteiler`, one `entry`. Every form has a G counterpart: index params
  are `Ty.index (count)`, `requires Held` is the signature-held set, `locks`
  blocks and direct calls are `Stmt`, `masks irqs` is `D.maskiert`, the entry
  dispatch roots are the declared starts, `costs`/`reads` are ignored form.

  ONE DOCUMENTED ANNOTATION-WEAKENING: every function of the source carries
  `deadline <= … arch x86_64 falsifier …`, and the exporter refuses exactly
  that in `check_fn` (`crates/gabbro-check/src/lean_g.rs`):
  `refuse("LG001", format!("function {} carries a form with no G counterpart",
  f.name))` when `d.deadline.is_some() || … || d.arch.is_some() || …`. Timing
  promises have no `Expr` form, so the model drops `deadline`/`arch`/
  `falsifier` and keeps bodies, Held sets, locks, starts and `costs`-free
  effects. No lock invariant is declared in the source, so the family is
  trivially true (owed nowhere).
-/
import Grammatik.Zielsatz.Proben

namespace Gabbro.Grammatik

namespace K59

/-- Tables `Takte` and `Auftraege` of the source. -/
inductive KTab where
  | takte
  | auftraege
  deriving DecidableEq

/-- Locks `TAKT` (rank 0, masks irqs, protects `Takte`) and `RING` (rank 0,
    protects `Auftraege`). -/
inductive KLock where
  | takt
  | ring
  deriving DecidableEq

/-- Functions `zaehle`, `takt_verteiler`, `bearbeite`, `ruf_verteiler`. -/
inductive KFn where
  | zaehle
  | taktVert
  | bearbeite
  | rufVert
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
  | .takte => [.inl .takt]
  | .auftraege => [.inl .ring]

/-- Both tables are shared, each guarded by its lock. -/
def kGeteilt : KTab → Bool
  | _ => true

def kRang : KLock → Int
  | .takt => 0
  | .ring => 0

/-- Only `TAKT` masks irqs -- the source's one-word difference from gift 460. -/
def kMaskiert : KLock → Bool
  | .takt => true
  | .ring => false

def kSigNr : Nat → Signatur KTab Empty KLock Empty
  | 0 => kSig [Ty.index 64] none [.takt] [.takte]
  | 1 => kSig [] none [] [.takte]
  | 2 => kSig [Ty.index 16] none [.ring] [.auftraege]
  | 3 => kSig [] none [] [.auftraege]
  | _ => kSig [] none [] []

def kSigOf : KFn → Nat
  | .zaehle => 0
  | .taktVert => 1
  | .bearbeite => 2
  | .rufVert => 3

/-- The declaration of `beispiele/59`: tables `Takte` (64 slots) and
    `Auftraege` (16 slots), `stand = u64`, each shared and guarded by its
    lock; no global, no table invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := KTab
  decTab := inferInstance
  count
    | .takte => 64
    | .auftraege => 16
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 18446744073709551615
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
  maskiert := kMaskiert
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

def kZaehle : kD.Fn := KFn.zaehle
def kTaktVert : kD.Fn := KFn.taktVert
def kBearbeite : kD.Fn := KFn.bearbeite
def kRufVert : kD.Fn := KFn.rufVert

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq KFn)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq KLock)

abbrev kLT : List (Res kD) := [Res.held (D := kD) KLock.takt]
abbrev kLR : List (Res kD) := [Res.held (D := kD) KLock.ring]

theorem kDarfTakte : darf kD KTab.takte kLT := by
  intro w h
  change w ∈ ([Sum.inl KLock.takt] : List (KLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl KLock.takt := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem kDarfAuftr : darf kD KTab.auftraege kLR := by
  intro w h
  change w ∈ ([Sum.inl KLock.ring] : List (KLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl KLock.ring := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- The index literal `0` as an index into `Takte` / `Auftraege`. -/
def kJ0T {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (Ty.index 64) :=
  .weiter (by decide) (by decide) (.lit 0)

def kJ0U {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (Ty.index 16) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- The constant both leaves write. -/
def kEins {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 18446744073709551615) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- The call-site typing of every call. -/
theorem kHaeltZaehle : (kD.signatur kZaehle).haelt = [KLock.takt] := rfl

theorem kHaeltBearbeite : (kD.signatur kBearbeite).haelt = [KLock.ring] := rfl

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

theorem kHpZaehle : RufPasst kD (vertragVon kD kTaktVert) (kD.signatur kZaehle) kLT :=
  kHp kTaktVert kZaehle (fun t h => by cases t <;> simp_all [kD, kZaehle, kTaktVert, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L hL => by cases L with
      | takt => exact List.mem_singleton.mpr rfl
      | ring => rw [kHaeltZaehle] at hL; exact KLock.noConfusion (List.mem_singleton.mp hL))
    (fun L hL => by
      have h2 : Res.held L = Res.held KLock.takt := List.mem_singleton.mp hL
      have h3 : L = KLock.takt := by cases h2; rfl
      rw [h3, kHaeltZaehle]; exact List.mem_singleton.mpr rfl) rfl rfl

theorem kHpBearbeite : RufPasst kD (vertragVon kD kRufVert) (kD.signatur kBearbeite) kLR :=
  kHp kRufVert kBearbeite (fun t h => by cases t <;> simp_all [kD, kBearbeite, kRufVert, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L hL => by cases L with
      | takt => rw [kHaeltBearbeite] at hL; exact KLock.noConfusion (List.mem_singleton.mp hL)
      | ring => exact List.mem_singleton.mpr rfl)
    (fun L hL => by
      have h2 : Res.held L = Res.held KLock.ring := List.mem_singleton.mp hL
      have h3 : L = KLock.ring := by cases h2; rfl
      rw [h3, kHaeltBearbeite]; exact List.mem_singleton.mpr rfl) rfl rfl

/-- `zaehle(i)`: `Takte.slots[i].stand = 1;`. -/
def kRumpfZaehle : Endblock kD (vertragVon kD kZaehle) false [Ty.index 64] kLT :=
  .cons (.assignSlot KTab.takte () (.var .hier) kEins rfl kDarfTakte)
    (.ret .keine (by rfl))

/-- `bearbeite(i)`: `Auftraege.slots[i].stand = 1;`. -/
def kRumpfBearbeite : Endblock kD (vertragVon kD kBearbeite) false [Ty.index 16] kLR :=
  .cons (.assignSlot KTab.auftraege () (.var .hier) kEins rfl kDarfAuftr)
    (.ret .keine (by rfl))

/-- The call `zaehle(0)` inside `takt_verteiler`'s lock. -/
def kRufZ : Stmt kD (vertragVon kD kTaktVert) false [] kLT kLT :=
  .call kZaehle (.cons kJ0T .nil) kHpZaehle rfl

/-- `takt_verteiler`'s `locks TAKT { zaehle(0); }`. -/
def kLocksT : Stmt kD (vertragVon kD kTaktVert) false [] [] [] :=
  .locks KLock.takt (fun _ h => nomatch h) (.cons kRufZ .nil)

/-- `takt_verteiler`, as in the source. -/
def kRumpfTaktVert : Endblock kD (vertragVon kD kTaktVert) false [] [] :=
  .cons kLocksT (.ret .keine List.Perm.nil)

/-- The call `bearbeite(0)` inside `ruf_verteiler`'s lock. -/
def kRufB : Stmt kD (vertragVon kD kRufVert) false [] kLR kLR :=
  .call kBearbeite (.cons kJ0U .nil) kHpBearbeite rfl

/-- `ruf_verteiler`'s `locks RING { bearbeite(0); }`. -/
def kLocksR : Stmt kD (vertragVon kD kRufVert) false [] [] [] :=
  .locks KLock.ring (fun _ h => nomatch h) (.cons kRufB .nil)

/-- `ruf_verteiler`, as in the source. -/
def kRumpfRufVert : Endblock kD (vertragVon kD kRufVert) false [] [] :=
  .cons kLocksR (.ret .keine List.Perm.nil)

/-- **The program of `beispiele/59`**: the source's bodies; trivial contracts
    (the source declares no `requires`/`ensures` on these four functions). -/
def kP : Programm kD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .zaehle => kRumpfZaehle
    | .taktVert => kRumpfTaktVert
    | .bearbeite => kRumpfBearbeite
    | .rufVert => kRumpfRufVert

def kFs : List kD.Fn := [kZaehle, kTaktVert, kBearbeite, kRufVert]

theorem kFs_voll : ∀ g : kD.Fn, g ∈ kFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The lock family**: `TAKT` protects `Takte`, `RING` protects `Auftraege`;
    the source declares no invariant, so both are trivially true. -/
def kSI : SperrInv kD :=
  ⟨fun | KLock.takt => [.inl KTab.takte] | KLock.ring => [.inl KTab.auftraege], fun _ _ => true⟩

theorem kSI_ok : SperrInvOk kSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => rfl⟩
  · cases L
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl
    · rw [List.mem_singleton.mp hc]; exact List.mem_singleton.mpr rfl

theorem kLocks_voll : ∀ L : kD.Lock, L ∈ ([KLock.takt, KLock.ring] : List kD.Lock) := fun L => by
  cases L
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

def kCs : List (kD.Tab ⊕ kD.Glob) := [.inl KTab.takte, .inl KTab.auftraege]

theorem kCs_voll : ∀ c : kD.Tab ⊕ kD.Glob, c ∈ kCs := fun c => by
  rcases c with t | g
  · cases t <;> simp [kCs]
  · exact nomatch g

/-- **The checker accepts the program** with its declared starts
    `takt_verteiler`, `ruf_verteiler` (the two entry dispatch roots). -/
theorem kP_akzeptiert : Akzeptiert kP kSI kFs [KLock.takt, KLock.ring] kCs [kTaktVert, kRufVert] = true := by decide

/-! ## 3. The user obligations -/

/-- Every `requires` is `.wahr`, at every function, world and environment. -/
theorem kReqWahr (f : kD.Fn) (W : World kD) (ρ : Env kD (kD.params f)) :
    ReqAmEintritt kP f W ρ := rfl

theorem kP_koerper_zaehle : KoerperGutS kP 0 (axWahr kD) kSI kZaehle := by
  have hr : kP.rumpf kZaehle = kRumpfZaehle := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfZaehle, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfZaehle, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfZaehle, execEndH, execStmtH] at hrun
    cases hrun

theorem kP_koerper_bearbeite : KoerperGutS kP 0 (axWahr kD) kSI kBearbeite := by
  have hr : kP.rumpf kBearbeite = kRumpfBearbeite := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [kRumpfBearbeite, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      rfl
  · rw [hr] at hrun
    simp only [kRumpfBearbeite, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [kRumpfBearbeite, execEndH, execStmtH] at hrun
    cases hrun

theorem kTakt_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kTaktVert)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfTaktVert σ ρ =
        execEndH S O U passes R (.cons kLocksT (.ret .keine List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

theorem kRuf_schreib {S : SperrInv kD} {O : Orakel kD} {U : Umwelt kD} {passes : Nat}
    {R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f} (σ : World kD)
    (ρ : Env kD (kD.params kRufVert)) :
    ∃ σ2 : World kD, execEndH S O U passes R kRumpfRufVert σ ρ =
        execEndH S O U passes R (.cons kLocksR (.ret .keine List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

/-- `takt_verteiler`: `ensures` is `.wahr`; the caller duty of the call from
    the trivial `requires`; no `logik` outcome because the release check is
    the trivially-true invariant. -/
theorem kP_koerper_taktVert : KoerperGutS kP 0 (axWahr kD) kSI kTaktVert := by
  have hr : kP.rumpf kTaktVert = kRumpfTaktVert := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kTakt_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksT] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kZaehle (((U KLock.takt σ2).nimmt KLock.takt).lese kLT [])
        (evalArgs (((U KLock.takt σ2).nimmt KLock.takt).lese kLT []) (Args.cons (Λ := kLT) (Γ := []) kJ0T .nil)
          (((U KLock.takt σ2).nimmt KLock.takt).lese kLT []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kZaehle (.cons kJ0T .nil) kHpZaehle rfl ((U KLock.takt σ2).nimmt KLock.takt) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.takt σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kZaehle _ _ = R kZaehle _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kTakt_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksT] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kZaehle (.cons kJ0T .nil) kHpZaehle rfl ((U KLock.takt σ2).nimmt KLock.takt) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.takt σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

/-- `ruf_verteiler`: the mirror image over `RING`/`Auftraege`. -/
theorem kP_koerper_rufVert : KoerperGutS kP 0 (axWahr kD) kSI kRufVert := by
  have hr : kP.rumpf kRufVert = kRumpfRufVert := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kRuf_schreib (S := kSI) (O := O') (U := U) (passes := 0)
      (R := torRuf kP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksR] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt kP kBearbeite (((U KLock.ring σ2).nimmt KLock.ring).lese kLR [])
        (evalArgs (((U KLock.ring σ2).nimmt KLock.ring).lese kLR []) (Args.cons (Λ := kLR) (Γ := []) kJ0U .nil)
          (((U KLock.ring σ2).nimmt KLock.ring).lese kLR []) ρ) := kReqWahr _ _ _
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := torRuf kP R)
      (l := false) (Γ := []) kBearbeite (.cons kJ0U .nil) kHpBearbeite rfl ((U KLock.ring σ2).nimmt KLock.ring) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.ring σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf kP R kBearbeite _ _ = R kBearbeite _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := kRuf_schreib (S := kSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, kLocksR] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := kSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) kBearbeite (.cons kJ0U .nil) kHpBearbeite rfl ((U KLock.ring σ2).nimmt KLock.ring) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv : kSI.inv KLock.ring σ1.speicher = true := rfl
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem kP_koerper : ∀ f : kD.Fn, KoerperGutS kP 0 (axWahr kD) kSI f := by
  intro f
  cases f
  · exact kP_koerper_zaehle
  · exact kP_koerper_taktVert
  · exact kP_koerper_bearbeite
  · exact kP_koerper_rufVert

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

/-- **`beispiele/59` as ONE declaration**: code `kP`, lock family `kSI`,
    no axiom, declared starts `takt_verteiler` and `ruf_verteiler` (the two
    entry dispatch roots, no parameters), initial memory all zero. -/
def kE : Zielsatz.Einheit kD := ⟨kP, kSI, axWahr kD, [⟨kTaktVert, .nil⟩, ⟨kRufVert, .nil⟩], kSp⟩

theorem korpus59_nutzer : Zielsatz.NutzerPflicht kE :=
  ⟨⟨fun passes f => ⟨kP_koerper_alle passes f, kP_inv_alle passes f,
      invGutGrund_ohneGrund (by cases f <;> rfl)⟩, fun _ _ _ _ => rfl, axEnsLokal_wahr⟩,
    ⟨fun _ => rfl, fun a ha => by
      simp only [kE, List.mem_cons, List.not_mem_nil, or_false] at ha
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

theorem kE_akzeptiert : akzeptiert_pruefer.akzeptiert kE kFs [KLock.takt, KLock.ring] kCs = true :=
  (by show Akzeptiert kP kSI kFs [KLock.takt, KLock.ring] kCs [kTaktVert, kRufVert] = true; exact kP_akzeptiert)

/-- **The goal theorem on `beispiele/59`**: for every oracle meeting (c), every
    budget, every runtime start meeting (d), and every reachable machine of
    `kP.mitRuhe`, the conclusion `Ziel` holds -- `gabbro_ziel` with the
    concrete checker. -/
theorem korpus59_ziel (O : Orakel kD) (hO : Zielsatz.HardwareAnnahmen O kE.Q) (passes : Nat)
    (sp : Speicher kD.mitRuhe)
    (init : Faden → Σ f : kD.mitRuhe.Fn, Env kD.mitRuhe (kD.mitRuhe.params f))
    (hL : Zielsatz.Laufzeit kE sp init) (M : RufMaschineG kD.mitRuhe)
    (hM : RufErreichbarG kE.P.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M) :
    Zielsatz.Ziel kE.P.mitRuhe kE.S.mitRuhe O.mitRuhe passes (RufStartG kE.P.mitRuhe sp init) M :=
  Zielsatz.gabbro_ziel akzeptiert_pruefer kD kE ⟨kFs, kFs_voll⟩ ⟨[KLock.takt, KLock.ring], kLocks_voll⟩ ⟨kCs, kCs_voll⟩
    kE_akzeptiert korpus59_nutzer O hO passes sp init hL
    (cloneAssume_empty _ _ _ _) M hM

/-- The index-`0` environment for the witness run. -/
def kRho0 : Env kD [Ty.index 64] := .cons ⟨0, by decide, by decide⟩ .nil

/-- **Witness for `korpus59_nutzer`** (rule 13): the premise group jointly
    with a non-degenerate run -- `zaehle`'s body from the all-zero world
    returns with `Takte[0] = 1` while it started `0`: a reached run with a
    memory-changing step, on a table a function writes. -/
theorem korpus59_nutzer_zeuge
    (R : ∀ f : kD.Fn, World kD → Env kD (kD.params f) → RufAusgang f) :
    Zielsatz.NutzerPflicht kE ∧ ∃ (σ' : World kD) (v : ErgVal kD (kD.erg kZaehle)),
      execEndH kSI kO (fun _ σ => σ) 0 R kRumpfZaehle (kSp.welt []) kRho0 = .zurueck σ' v ∧
      (σ'.slots KTab.takte 0 ()).n = 1 ∧ ((kSp.welt []).slots KTab.takte 0 ()).n = 0 :=
  ⟨korpus59_nutzer, _, _, rfl, rfl, rfl⟩

/-
  CUTS: the `deadline <= … arch x86_64 falsifier …` annotations of all four
  source functions are dropped (no `Expr` form; exporter refusal LG001
  `check_fn`, quoted in the header). Everything else of the source is
  modelled: tables, locks (including `masks irqs` as `D.maskiert`), bodies,
  Held sets, entry dispatch roots as starts. `costs`/`reads` are ignored
  form. What is NOT claimed: anything about the `.gab` source text (no
  exporter link yet -- lane 201), and no stage-(b) simulation certificate.
-/
#print axioms K59.kP_akzeptiert
#print axioms K59.korpus59_nutzer
#print axioms K59.korpus59_ziel
#print axioms K59.korpus59_nutzer_zeuge

end K59

end Gabbro.Grammatik
