/- Part 2 of 4 of `Schlusssatz104` (split by instrumente/teile/lean-teilen.py; the umbrella `Schlusssatz104.lean` imports all parts). -/
import Grammatik.Korrespondenz.Kette.Schlusssatz104.T1

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze
open G104_referenz (GTab GLock GKontoFeld GFn g_einzahlen g_lies gCtx_einzahlen gCtx_lies
  gL_einzahlen gL_lies gDarf_einzahlen_Konto gDarf_lies_Konto gHp_einzahlen_lies gBody_einzahlen
  gBody_lies gSig_einzahlen gSig_lies)
set_option maxRecDepth 100000

/-- A call of a `requires true` function through the gate never fails the
    gate when the handler blames nobody (over `gD`). -/
theorem g_call_tor {V : Vertrag G104_referenz.gD} {l : Bool} {Γ : Ctx}
    {Λ : List (Res G104_referenz.gD)} (O : Orakel G104_referenz.gD) (passes : Nat)
    (R : ∀ f : G104_referenz.gD.Fn, World G104_referenz.gD → Env G104_referenz.gD
      (G104_referenz.gD.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : G104_referenz.gD.Fn) (args : Args G104_referenz.gD Γ Λ (G104_referenz.gD.params g))
    (hp : RufPasst G104_referenz.gD V (G104_referenz.gD.signatur g) Λ)
    (hr : G104_referenz.gD.gruende g = 0) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD Γ) (g' : G104_referenz.gD.Fn) :
    execStmt O passes (torRuf G104_referenz.gP R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf G104_referenz.gP R g σ1 ρ1 = R g σ1 ρ1 :=
    fun _ _ => if_pos (by cases g <;> rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

/-- `lies` meets its obligation: the returned value is the slot. -/
theorem gP_koerper_lies : KoerperGutV G104_referenz.gP 0 g_lies := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : G104_referenz.gP.rumpf g_lies = gBody_lies := rfl
    rw [hr] at hrun
    simp only [gBody_lies, execEnd] at hrun
    cases hrun
    exact decide_eq_true rfl
  · have hr : G104_referenz.gP.rumpf g_lies = gBody_lies := rfl
    rw [hr] at hrun
    simp only [gBody_lies, execEnd] at hrun
    cases hrun

/-- **`einzahlen` of the parsed program meets the obligation against
    declared frames**: the write sets the slot to `100`, `lies` declares no
    write (every frame-respecting answer keeps the slots), so
    `old(stand) <= stand` is `old(stand) <= 100`, true by the range. -/
theorem gP_einzahlen_R : KoerperGutR G104_referenz.gP 0 g_einzahlen := by
  intro O' _ _ R hR hOV σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : G104_referenz.gP.rumpf g_einzahlen = gBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, h1, hrun1⟩
    · simp [execStmt] at h1
    rcases execEnd_cons_zurueck _ _ _ _ _ hrun1 with h2 | ⟨σ2, ρ2, h2, hrun2⟩
    · simp only [execStmt] at h2
      split at h2
      · cases h2
      · rename_i r _
        exact r.elim0
      · cases h2
      · cases h2
    simp only [execEnd] at hrun2
    simp only [execStmt] at h2
    split at h2
    · rename_i σ3 w hRv
      cases h2
      cases hrun2
      have hfr := (hR.2 g_lies _ _ σ2 w hRv).1.1 GTab.Konto rfl
      simp only [execStmt] at h1
      cases h1
      show decide ((σ.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n ≤
        (σ2.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n) = true
      have e3 := (hfr (ρ.get (.there .here)).n GKontoFeld.stand).trans
        (storeSlot_hit (D := G104_referenz.gD) _ GTab.Konto _ GKontoFeld.stand _)
      have h100 : (σ2.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).n = 100 :=
        (congrArg (fun z : Zahl 0 100 => z.n) e3).trans rfl
      apply decide_eq_true
      exact Int.le_trans (σ.slots GTab.Konto (ρ.get (.there .here)).n GKontoFeld.stand).le_hi
        (Int.le_of_eq h100.symm)
    · rename_i r _
      exact r.elim0
    · cases h2
    · cases h2
  · have hr : G104_referenz.gP.rumpf g_einzahlen = gBody_einzahlen := rfl
    rw [hr] at hrun
    rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
    · simp [execStmt] at h1
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
      · exact g_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
      · simp only [execEnd] at h2
        cases h2

theorem gFs_voll : ∀ g : G104_referenz.gD.Fn, g ∈ G104_referenz.gFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem gP_logikFrei : programmLogikFrei G104_referenz.gP G104_referenz.gFs = true := by decide

/-- **THE MODEL JUDGEMENT on the parsed program**: every function meets the
    per-function obligation of the goal theorem (`KoerperGutS`, over the
    empty lock-invariant family and the trivial axiom ensures -- the
    declaration has no axiom). -/
theorem gP_koerperS : ∀ f : G104_referenz.gD.Fn,
    KoerperGutS G104_referenz.gP 0 (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  fun f => koerperGutS_leer ⟨koerperGutRQ_of_R _ (match f with
    | .einzahlen => gP_einzahlen_R
    | .lies => koerperGutR_of_V gP_koerper_lies),
    programmLogikFrei_ok gFs_voll gP_logikFrei 0 _ f⟩

theorem gP_invGutS : ∀ f : G104_referenz.gD.Fn,
    InvGutS G104_referenz.gP 0 (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  invGutS_leer rfl

/-- No body of the parsed program contains a `forever` loop. -/
theorem gP_ohneEwig : ohneEwigB G104_referenz.gP G104_referenz.gFs = true := by decide

/-- **The model judgement at EVERY `forever` budget** (`Durchgaenge.lean`):
    the goal statements demand the obligation at every budget. -/
theorem gP_koerperS_alle : ∀ (passes : Nat) (f : G104_referenz.gD.Fn),
    KoerperGutS G104_referenz.gP passes (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  koerperGutS_alle gFs_voll gP_ohneEwig gP_koerperS

theorem gP_invGutS_alle : ∀ (passes : Nat) (f : G104_referenz.gD.Fn),
    InvGutS G104_referenz.gP passes (axWahr G104_referenz.gD) (SperrInv.leer G104_referenz.gD) f :=
  fun _ => invGutS_leer rfl

/-- **The call semantics of the parsed program does not depend on the
    budget**: every statement of part 4 at budget `0` holds at every
    budget. -/
theorem gP_rufAt_passes : ∀ (passes k : Nat) (f : G104_referenz.gD.Fn) (σ : World G104_referenz.gD)
    (ρ : Env G104_referenz.gD (G104_referenz.gD.params f)),
    rufAt G104_referenz.gP gO104 passes k f σ ρ = rufAt G104_referenz.gP gO104 0 k f σ ρ :=
  fun passes => rufAt_passes gO104 (ohneEwigB_ok gFs_voll gP_ohneEwig) passes 0


/-! ## 5. The machine -/

/-! ### 5.1 The finding: no G machine of `gP` alone has one active thread -/

/-- No function of the parsed program is an idle root (`ruhig`): both hold
    `M` by signature and touch `Konto`. -/
theorem gP_kein_ruhig : ∀ f : G104_referenz.gD.Fn, ruhig G104_referenz.gP f = false := by
  intro f; cases f <;> decide

/-- **No start assignment of `gP` is exclusive**: G starts EVERY thread in
    some function, and every function of `gD` holds `M` by signature, so
    threads 0 and 1 both start holding `M`. Neither `ziel_ort_einfaden`
    (idle roots) nor `ziel_ort_sperre`/`_inv` (`StartExklusiv`) applies to
    a machine of `gP` alone: the start of the other threads is runtime
    data, not source text. -/
theorem gP_kein_exklusiv (init : Faden → Σ f : G104_referenz.gD.Fn,
    Env G104_referenz.gD (G104_referenz.gD.params f)) : ¬ StartExklusiv init := by
  intro h
  have hM : ∀ f : G104_referenz.gD.Fn, GLock.M ∈ G104_referenz.gD.haelt f := by
    intro f; cases f <;> exact List.mem_singleton.mpr rfl
  exact h 0 1 (by decide) GLock.M (hM _) (hM _)

/-! ### 5.2 The runtime's idle root: `gDB`, `gPB` -/

/-- The idle root's signature: no parameter, no result, no lock, no write. -/
def sigRuhe : Signatur GTab Empty GLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- **`gD` plus the idle root**: every carrier, lock, table, field, global,
    axiom and register IS `gD`'s (the fields are `gD`'s own); the functions
    are `some f` for `gD`'s `f` (same signature number) and `none`, the
    idle root (signature number 2, unused by `gD`: `gD` has no function
    pointer). -/
abbrev gDB : Deklaration :=
  { G104_referenz.gD with
    Fn := Option GFn
    sig := fun | some f => G104_referenz.gD.sig f | none => 2
    sigNr := fun | 2 => sigRuhe | n => G104_referenz.gD.sigNr n
    eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
    rzusage := fun r => nomatch r
    invarianten_gehalten := fun _ i => nomatch i }

abbrev gbL : List (Res gDB) := [Res.held (D := gDB) GLock.M]

theorem gbDarf : darf gDB GTab.Konto gbL := by unfold darf; decide

theorem gbHp : RufPasst gDB (vertragVon gDB (some GFn.einzahlen)) (gDB.signatur (some GFn.lies))
    gbL where
  hw := fun t => by cases t <;> decide
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := RufPasst.hh_von (fun L => by cases L <;> decide)
  hx := RufPasst.hx_von (fun L => by cases L <;> decide)

def gbEns_einzahlen : Expr gDB (ErgCtx (gDB.params (some GFn.einzahlen)) (gDB.erg (some GFn.einzahlen)))
    (vertragVon gDB (some GFn.einzahlen)).ende .bool :=
  (.le (Expr.oldS (D := gDB) GTab.Konto GKontoFeld.stand ((.var (.there .here))) gbDarf)
    (Expr.thru (D := gDB) (.var .here) GTab.Konto rfl GKontoFeld.stand ((.var (.there .here))) gbDarf))

def gbEns_lies : Expr gDB (ErgCtx (gDB.params (some GFn.lies)) (gDB.erg (some GFn.lies)))
    (vertragVon gDB (some GFn.lies)).ende .bool :=
  (.eq (.var .here) (Expr.thru (D := gDB) (.var (.there .here)) GTab.Konto rfl GKontoFeld.stand
    ((.var (.there (.there .here)))) gbDarf))

def gbBody_einzahlen : Endblock gDB (vertragVon gDB (some GFn.einzahlen)) false
    (gDB.params (some GFn.einzahlen)) gbL :=
  (.cons (.assignThru (.var .here) GTab.Konto rfl GKontoFeld.stand ((.var (.there .here)))
    (.widen (by decide) (by decide) (.lit 100)) (by decide) gbDarf)
    (.cons (.call (some GFn.lies) (.cons (.ptrOf GTab.Konto 0 rfl false) (.cons (.var (.there .here)) .nil))
      gbHp rfl) (.ret .empty (List.Perm.refl _))))

def gbBody_lies : Endblock gDB (vertragVon gDB (some GFn.lies)) false
    (gDB.params (some GFn.lies)) gbL :=
  (.ret (.val (Expr.thru (D := gDB) (.var .here) GTab.Konto rfl GKontoFeld.stand
    ((.var (.there .here))) gbDarf)) (List.Perm.refl _))

def gbBody_ruhe : Endblock gDB (vertragVon gDB none) false (gDB.params none) [] :=
  .ret .empty List.Perm.nil

/-- **The program the machine runs**: `gP`'s contracts and bodies on
    `some f` (section 5.3 proves them the renamings of the parser's), the
    idle root on `none`. -/
def gPB : Programm gDB where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures
    | some .einzahlen => gbEns_einzahlen
    | some .lies => gbEns_lies
    | none => .tru
  rumpf
    | some .einzahlen => gbBody_einzahlen
    | some .lies => gbBody_lies
    | none => gbBody_ruhe

def gbFs : List gDB.Fn := [some GFn.einzahlen, some GFn.lies, none]

theorem gbFs_voll : ∀ g : gDB.Fn, g ∈ gbFs := by
  intro g
  rcases g with _ | g
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · cases g
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem gPB_fragment : programmImFragmentG gPB gbFs = true := by decide

theorem gPB_logikFrei : programmLogikFrei gPB gbFs = true := by decide

theorem gPB_ruhig : ruhig gPB none = true := by decide


/-! ### 5.3 `gPB`'s source part IS the parsed program, renamed

`renE`/`renArgs`/`renErg`/`renS`/`renEnd` rename a term over `gD` to the same
term over `gDB`: every constructor to the same-named constructor, every
table, field, lock, index and literal to itself, a function `f` to `some f`;
proofs are transported (`darf_rm`, `rufPasst_rm`, `perm_rm`), never
re-invented. The renaming is PARTIAL: it covers the constructors of the
104 fragment (and a few more) and answers `none` elsewhere, so an equation
`ren x = some y` is a kernel-checked statement that `y` is `x` renamed. -/

/-- A resource of `gD` as a resource of `gDB` (same lock, same mark). -/
def rm : Res G104_referenz.gD → Res gDB
  | .held L => .held L
  | .marke m s => .marke m s

theorem rm_von (w : GLock ⊕ (Empty × Nat)) : rm (Res.von G104_referenz.gD w) = Res.von gDB w := by
  rcases w with L | ⟨m, s⟩
  · rfl
  · exact m.elim

theorem darf_rm {t : GTab} {Λ : List (Res G104_referenz.gD)} (h : darf G104_referenz.gD t Λ) :
    darf gDB t (Λ.map rm) := by
  intro w hw
  rw [← rm_von]
  exact List.mem_map_of_mem (h w hw)

/-- A contract of `gD` as a contract of `gDB` (field by field). -/
def vm (V : Vertrag G104_referenz.gD) : Vertrag gDB :=
  ⟨V.schreibt, V.gschreibt, V.erg, V.gruende, V.haelt, V.produziert, V.boden⟩

theorem ende_rm (V : Vertrag G104_referenz.gD) : (vm V).ende = V.ende.map rm := by
  have hp : V.produziert = [] := by
    cases h : V.produziert with
    | nil => rfl
    | cons x _ => exact x.1.elim
  simp [Vertrag.ende, vm, hp, rm]

theorem perm_rm {V : Vertrag G104_referenz.gD} {Λ : List (Res G104_referenz.gD)}
    (h : Λ.Perm V.ende) : (Λ.map rm).Perm (vm V).ende := by
  rw [ende_rm]
  exact h.map rm

theorem konsumiert_leer (S : Signatur GTab Empty GLock Empty) : S.konsumiert = [] := by
  cases h : S.konsumiert with
  | nil => rfl
  | cons x _ => exact x.1.elim

theorem produziert_leer (S : Signatur GTab Empty GLock Empty) : S.produziert = [] := by
  cases h : S.produziert with
  | nil => rfl
  | cons x _ => exact x.1.elim

theorem held_rm_mem {L : GLock} {Λ : List (Res G104_referenz.gD)}
    (h : Res.held (D := gDB) L ∈ Λ.map rm) : Res.held (D := G104_referenz.gD) L ∈ Λ := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp h
  cases x with
  | held L' => cases e; exact hx
  | marke m s => exact m.elim

theorem rufPasst_rm {V : Vertrag G104_referenz.gD} {S : Signatur GTab Empty GLock Empty}
    {Λ : List (Res G104_referenz.gD)} (h : RufPasst G104_referenz.gD V S Λ) :
    RufPasst gDB (vm V) S (Λ.map rm) where
  hw := h.hw
  hg := h.hg
  hk := ⟨[], by rw [konsumiert_leer]; exact List.Perm.refl [], List.nil_sublist _⟩
  hh := fun L hL => List.mem_map_of_mem (f := rm) (h.hh L hL)
  hx := fun L hL hn => h.hx L (held_rm_mem hL) hn
  hb := h.hb

theorem params_some (f : GFn) : gDB.params (some f) = G104_referenz.gD.params f := by
  cases f <;> rfl

theorem signatur_some (f : GFn) : gDB.signatur (some f) = G104_referenz.gD.signatur f := by
  cases f <;> rfl

theorem nach_rm (f : GFn) (Λ : List (Res G104_referenz.gD)) :
    (nach G104_referenz.gD f Λ).map rm = nach gDB (some f) (Λ.map rm) := by
  cases f <;> simp [nach, nachSig, Deklaration.signatur, gSig_einzahlen, gSig_lies]

/-- Expressions. -/
def renE : {Γ : Ctx} → {Λ : List (Res G104_referenz.gD)} → {τ : Ty} →
    Expr G104_referenz.gD Γ Λ τ → Option (Expr gDB Γ (Λ.map rm) τ)
  | _, _, _, .lit n => some (.lit n)
  | _, _, _, .tru => some .tru
  | _, _, _, .fls => some .fls
  | _, _, _, .var x => some (.var x)
  | _, _, _, .slot t f i hL => (renE i).map fun i' => Expr.slot (D := gDB) t f i' (darf_rm hL)
  | _, _, _, .thru p t ht f i hL =>
    (renE p).bind fun p' => (renE i).map fun i' => Expr.thru (D := gDB) p' t ht f i' (darf_rm hL)
  | _, _, _, .ptrOf t n ht rw => some (Expr.ptrOf (D := gDB) t n ht rw)
  | _, _, _, .oldS t f i hL => (renE i).map fun i' => Expr.oldS (D := gDB) t f i' (darf_rm hL)
  | _, _, _, .widen h1 h2 e => (renE e).map (.widen h1 h2)
  | _, _, _, .add a b => (renE a).bind fun a' => (renE b).map (.add a')
  | _, _, _, .sub a b => (renE a).bind fun a' => (renE b).map (.sub a')
  | _, _, _, .lt a b => (renE a).bind fun a' => (renE b).map (.lt a')
  | _, _, _, .le a b => (renE a).bind fun a' => (renE b).map (.le a')
  | _, _, _, .eq a b => (renE a).bind fun a' => (renE b).map (.eq a')
  | _, _, _, .and a b => (renE a).bind fun a' => (renE b).map (.and a')
  | _, _, _, .or a b => (renE a).bind fun a' => (renE b).map (.or a')
  | _, _, _, .not a => (renE a).map .not
  | _, _, _, _ => none

/-- Argument lists. -/
def renArgs : {Γ : Ctx} → {Λ : List (Res G104_referenz.gD)} → {τs : List Ty} →
    Args G104_referenz.gD Γ Λ τs → Option (Args gDB Γ (Λ.map rm) τs)
  | _, _, _, .nil => some .nil
  | _, _, _, .cons e rest => (renE e).bind fun e' => (renArgs rest).map (.cons e')

/-- Return values. -/
def renErg {Γ : Ctx} {Λ : List (Res G104_referenz.gD)} : {e : Option Ty} →
    ErgExpr G104_referenz.gD Γ Λ e → Option (ErgExpr gDB Γ (Λ.map rm) e)
  | _, .empty => some .empty
  | _, .val e => (renE e).map .val

section Ren
variable {V : Vertrag G104_referenz.gD} {l : Bool}

/-- Statements: the table writes and the direct call (`f` to `some f`, the
    argument list, the transported `RufPasst`; the resource index moves along
    `nach_rm`). Every other statement: none. -/
def renS {Γ : Ctx} {Λ Λ' : List (Res G104_referenz.gD)} :
    Stmt G104_referenz.gD V l Γ Λ Λ' → Option (Stmt gDB (vm V) l Γ (Λ.map rm) (Λ'.map rm))
  | .assignSlot t f i e hw hL =>
    (renE i).bind fun i' => (renE e).map fun e' => Stmt.assignSlot (V := vm V) t f i' e' hw (darf_rm hL)
  | .assignThru p t ht f i e hw hL =>
    (renE p).bind fun p' => (renE i).bind fun i' => (renE e).map fun e' =>
      Stmt.assignThru (V := vm V) p' t ht f i' e' hw (darf_rm hL)
  | .call f args hp hr =>
    (renArgs args).map fun a =>
      (nach_rm f Λ) ▸ Stmt.call (V := vm V) (l := l) (some f) ((params_some f).symm ▸ a)
        ((signatur_some f).symm ▸ rufPasst_rm hp) (by cases f <;> exact hr)
  | _ => none

/-- Terminal blocks. -/
def renEnd {Γ : Ctx} : {Λ : List (Res G104_referenz.gD)} →
    Endblock G104_referenz.gD V l Γ Λ → Option (Endblock gDB (vm V) l Γ (Λ.map rm))
  | _, .ret e hΛ => (renErg e).map fun e' => .ret e' (perm_rm hΛ)
  | _, .retWhy r hΛ => some (.retWhy r (perm_rm hΛ))
  | _, .leave h => some (.leave h)
  | _, .next h => some (.next h)
  | _, .cons s rest => (renS s).bind fun s' => (renEnd rest).map (.cons s')
  | _, .bind e rest => (renE e).bind fun e' => (renEnd rest).map (.bind e')

end Ren
theorem ren_rumpf_einzahlen :
    renEnd (G104_referenz.gP.rumpf g_einzahlen) = some (gPB.rumpf (some GFn.einzahlen)) := rfl

theorem ren_rumpf_lies :
    renEnd (G104_referenz.gP.rumpf g_lies) = some (gPB.rumpf (some GFn.lies)) := rfl

theorem ren_ensures_einzahlen :
    renE (G104_referenz.gP.ensures g_einzahlen) = some (gPB.ensures (some GFn.einzahlen)) := rfl

theorem ren_ensures_lies :
    renE (G104_referenz.gP.ensures g_lies) = some (gPB.ensures (some GFn.lies)) := rfl

theorem ren_requires_einzahlen :
    renE (G104_referenz.gP.requires g_einzahlen) = some (gPB.requires (some GFn.einzahlen)) := rfl

theorem ren_requires_lies :
    renE (G104_referenz.gP.requires g_lies) = some (gPB.requires (some GFn.lies)) := rfl

/-- **`gPB`'s source part IS the parsed program `gP`, renamed**: every
    body, `ensures` and `requires` of `gPB` at `some f` is the renaming of
    `gP`'s at `f` (kernel-checked, `rfl`); `gPB` adds exactly the idle root
    `none`, which holds no lock, touches nothing and returns. -/
theorem gPB_ist_gP_umbenannt :
    renEnd (G104_referenz.gP.rumpf g_einzahlen) = some (gPB.rumpf (some GFn.einzahlen)) ∧
    renEnd (G104_referenz.gP.rumpf g_lies) = some (gPB.rumpf (some GFn.lies)) ∧
    renE (G104_referenz.gP.ensures g_einzahlen) = some (gPB.ensures (some GFn.einzahlen)) ∧
    renE (G104_referenz.gP.ensures g_lies) = some (gPB.ensures (some GFn.lies)) ∧
    renE (G104_referenz.gP.requires g_einzahlen) = some (gPB.requires (some GFn.einzahlen)) ∧
    renE (G104_referenz.gP.requires g_lies) = some (gPB.requires (some GFn.lies)) ∧
    ruhig gPB none = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩


/-! ### 5.4 The goal theorem for the machine of `gPB` -/

theorem gb_call_tor {V : Vertrag gDB} {l : Bool} {Γ : Ctx}
    {Λ : List (Res gDB)} (O : Orakel gDB) (passes : Nat)
    (R : ∀ f : gDB.Fn, World gDB → Env gDB (gDB.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : gDB.Fn) (args : Args gDB Γ Λ (gDB.params g))
    (hp : RufPasst gDB V (gDB.signatur g) Λ)
    (hr : gDB.gruende g = 0) (σ : World gDB) (ρ : Env gDB Γ) (g' : gDB.Fn) :
    execStmt O passes (torRuf gPB R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf gPB R g σ1 ρ1 = R g σ1 ρ1 :=
    fun _ _ => if_pos (by rcases g with _ | g; rfl; cases g <;> rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

theorem gPB_koerper_lies : KoerperGutV gPB 0 (some GFn.lies) := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : gPB.rumpf (some GFn.lies) = gbBody_lies := rfl
    rw [hr] at hrun
    simp only [gbBody_lies, execEnd] at hrun
    cases hrun
    exact decide_eq_true rfl
  · have hr : gPB.rumpf (some GFn.lies) = gbBody_lies := rfl
    rw [hr] at hrun
    simp only [gbBody_lies, execEnd] at hrun
    cases hrun

theorem gPB_koerper_ruhe : KoerperGutV gPB 0 none := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : gPB.rumpf none = gbBody_ruhe := rfl
  rw [hr] at hrun
  simp only [gbBody_ruhe, execEnd] at hrun
  cases hrun


end Gabbro.Grammatik
