module
public import Grammatik.Zielsatz.Einbettung.Ressourcen
@[expose] public section


/-!
  File:      Grammatik/Zielsatz/Einbettung/Syntax.lean
  Subject:   The syntax of `D` as syntax of `D'` under an embedding (stage E0).

  Every constructor goes to the same constructor: items to their images, types by `tyE`,
  holdings by `resE`, contracts by `vertragE`. Where `D'` meets a side condition only
  propositionally (a field's type, a table's count, a parameter list), the term is transported
  along the equation the embedding provides.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

/-! ## Transports -/

def Expr.umTy {Γ : Ctx} {Λ : List (Res D)} {τ τ' : Ty} (h : τ = τ') (e : Expr D Γ Λ τ) :
    Expr D Γ Λ τ' := h ▸ e

def Block.umΓ {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} {Λ Λ' : List (Res D)} (h : Γ = Γ')
    (b : Block D V l Γ Λ Λ') : Block D V l Γ' Λ Λ' := h ▸ b

def Endblock.umΓ {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} {Λ : List (Res D)} (h : Γ = Γ')
    (b : Endblock D V l Γ Λ) : Endblock D V l Γ' Λ := h ▸ b

def Endblock.umV {V V' : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (h : V = V')
    (b : Endblock D V l Γ Λ) : Endblock D V' l Γ Λ := h ▸ b

def Args.umτs {Γ : Ctx} {Λ : List (Res D)} {τs τs' : List Ty} (h : τs = τs') (a : Args D Γ Λ τs) :
    Args D Γ Λ τs' := h ▸ a

namespace Einbettung

variable (E : Einbettung D D')

/-! ## What `D'` knows of the image -/

theorem schreibtE {V : Vertrag D} {t : D.Tab} (h : V.schreibt t = true) :
    (E.vertragE V).schreibt (E.tab t) = true := by
  simp only [vertragE, E.tabZ_tab]; exact h

theorem gschreibtE {V : Vertrag D} {g : D.Glob} (h : V.gschreibt g = true) :
    (E.vertragE V).gschreibt (E.glob g) = true := by
  simp only [vertragE, E.globZ_glob]; exact h

theorem axSchreibtE {V : Vertrag D} {a : D.Ax} (h : ∀ t, D.aschreibt a t = true → V.schreibt t = true) :
    ∀ t', D'.aschreibt (E.ax a) t' = true → (E.vertragE V).schreibt t' = true := by
  intro t' ht'
  rw [E.aschreibt] at ht'
  simp only [vertragE]
  revert ht'
  cases E.tabZ t' with
  | none => intro ht'; cases ht'
  | some t => exact h t

theorem axGSchreibtE {V : Vertrag D} {a : D.Ax}
    (h : ∀ g, D.agschreibt a g = true → V.gschreibt g = true) :
    ∀ g', D'.agschreibt (E.ax a) g' = true → (E.vertragE V).gschreibt g' = true := by
  intro g' hg'
  rw [E.agschreibt] at hg'
  simp only [vertragE]
  revert hg'
  cases E.globZ g' with
  | none => intro hg'; cases hg'
  | some g => exact h g

theorem axDarfE {Λ : List (Res D)} {a : D.Ax} (h : ∀ t, D.aschreibt a t = true → darf D t Λ) :
    ∀ t', D'.aschreibt (E.ax a) t' = true → darf D' t' (Λ.map E.resE) := by
  intro t' ht'
  rw [E.aschreibt] at ht'
  cases hz : E.tabZ t' with
  | none => rw [hz] at ht'; cases ht'
  | some t =>
    rw [hz] at ht'
    rw [← E.tab_tabZ t' t hz]
    exact E.darfE (h t ht')

theorem axGDarfE {Λ : List (Res D)} {a : D.Ax} (h : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
    ∀ g', D'.agschreibt (E.ax a) g' = true → gdarf D' g' (Λ.map E.resE) := by
  intro g' hg'
  rw [E.agschreibt] at hg'
  cases hz : E.globZ g' with
  | none => rw [hz] at hg'; cases hg'
  | some g =>
    rw [hz] at hg'
    rw [← E.glob_globZ g' g hz]
    exact E.gdarfE (h g hg')

theorem tabNrE {n : Nat} {t : D.Tab} (h : D.tabNr n = some t) : D'.tabNr (E.tnum n) = some (E.tab t) := by
  rw [E.tabNr.1, h]; rfl

/-- Capability resolution transports the table and retains its registered nominal space. -/
theorem capTabE {space n : Nat} {t : D.Tab} (h : D.capTab space n = some t) :
    D'.capTab space (E.tnum n) = some (E.tab t) := by
  obtain ⟨hn, hs, hb⟩ := Deklaration.capTab_sound h
  exact Deklaration.capTab_of (E.tabNrE hn) (hs.trans (E.tabNr.2.1 t).symm)
    (by simpa only [E.tabNr.2.2] using hb)

theorem countE (t : D.Tab) : Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) := by
  rw [E.count]

variable {E}

theorem paramsE (hS : E.SigTreu) (f : D.Fn) : (D.params f).map E.tyE = D'.params (E.fn f) := by
  unfold Deklaration.params; rw [hS.signatur]; rfl

theorem ergE_fn (hS : E.SigTreu) (f : D.Fn) : (D.erg f).map E.tyE = D'.erg (E.fn f) := by
  unfold Deklaration.erg; rw [hS.signatur]; rfl

theorem gruendeE (hS : E.SigTreu) (f : D.Fn) : D'.gruende (E.fn f) = D.gruende f := by
  unfold Deklaration.gruende; rw [hS.signatur]; rfl

theorem vertragVonE (hS : E.SigTreu) (f : D.Fn) : E.vertragE (vertragVon D f) = vertragVon D' (E.fn f) := by
  unfold vertragVon; rw [hS.signatur]; rfl

theorem anfangE_fn (hS : E.SigTreu) (f : D.Fn) :
    (Signatur.anfang D (D.signatur f)).map E.resE = Signatur.anfang D' (D'.signatur (E.fn f)) := by
  rw [hS.signatur]; exact E.anfangE _

theorem rufPasstE_fn (hS : E.SigTreu) {V : Vertrag D} {f : D.Fn} {Λ : List (Res D)}
    (h : RufPasst D V (D.signatur f) Λ) :
    RufPasst D' (E.vertragE V) (D'.signatur (E.fn f)) (Λ.map E.resE) := by
  rw [hS.signatur]; exact E.rufPasstE h

theorem rufPasstE_nr (hS : E.SigTreu) {V : Vertrag D} {n : Nat} {Λ : List (Res D)}
    (h : RufPasst D V (D.sigNr n) Λ) :
    RufPasst D' (E.vertragE V) (D'.sigNr (E.val n)) (Λ.map E.resE) := by
  rw [hS.sigNr]; exact E.rufPasstE h

theorem nachSigE_nr (hS : E.SigTreu) (n : Nat) (Λ : List (Res D)) :
    (nachSig D (D.sigNr n) Λ).map E.resE = nachSig D' (D'.sigNr (E.val n)) (Λ.map E.resE) := by
  rw [hS.sigNr]; exact E.nachSigE _ Λ

variable (E)

/-! ## The translation -/

def varE : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Var (Γ.map E.tyE) (E.tyE τ)
  | _, _, .here => .here
  | _, _, .there x => .there (varE x)

/-- A builtin of `D` as a builtin of `D'`: widths and ranges are numbers, so `tyE` leaves its types alone. -/
def ibE {ts : List Ty} {τ : Ty} : IntBuiltin ts τ → IntBuiltin (ts.map E.tyE) (E.tyE τ)
  | .addW w => .addW w
  | .subW w => .subW w
  | .mulW w => .mulW w
  | .shlW w => .shlW w
  | .addS lo hi => .addS lo hi
  | .clz w => .clz w
  | .ctz w => .ctz w
  | .log2Floor w => .log2Floor w
  | .popcount w => .popcount w
  | .rotl w => .rotl w
  | .rotr w => .rotr w
  | .bswap16 => .bswap16
  | .bswap32 => .bswap32
  | .bswap64 => .bswap64

mutual

/-- **An expression of `D` as an expression of `D'`.** -/
def exE : {Γ : Ctx} → {Λ : List (Res D)} → {τ : Ty} → Expr D Γ Λ τ →
    Expr D' (Γ.map E.tyE) (Λ.map E.resE) (E.tyE τ)
  | _, _, _, .lit n => .lit n
  | _, _, _, .tru => .tru
  | _, _, _, .fls => .fls
  | _, _, _, .var x => .var (varE E x)
  | _, _, _, .glob g hL => Expr.umTy (E.gtyp g) (Expr.glob (D := D') (E.glob g) (E.gdarfE hL))
  | _, _, _, .slot t f i hL =>
      Expr.umTy (E.typ t f)
        (Expr.slot (D := D') (E.tab t) (E.feld t f) (Expr.umTy (E.countE t) (exE i)) (E.darfE hL))
  | _, _, _, .thru p t ht f i hL =>
      Expr.umTy (E.typ t f)
        (Expr.thru (D := D') (exE p) (E.tab t) (E.capTabE ht) (E.feld t f)
          (Expr.umTy (E.countE t) (exE i)) (E.darfE hL))
  | _, _, _, .ptrOf t n ht rw => Expr.ptrOf (D := D') (E.tab t) (E.tnum n) (E.capTabE ht) rw
  | _, _, _, .fnref f n h => .fnref (D := D') (E.fn f) (E.val n) ((E.passt f n).trans h)
