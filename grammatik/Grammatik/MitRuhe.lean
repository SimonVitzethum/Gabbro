/-
  File:      Grammatik/MitRuhe.lean
  Subject:   THE RUNTIME'S IDLE ROOT, GENERICALLY -- `D.mitRuhe` is `D`
             plus one function `none` (the runtime's idle function: body
             `return`, empty signature, no locks, no reasons, writes
             nothing), and `P.mitRuhe` is `P` over it. DEFINITIONS only
             (part of the review package of `Zielsatz/Spec.lean`).

  Why: machine G starts EVERY thread of `Faden = Nat` in some function.
  A program without an idle function (the export of `beispiele/104`,
  probes B/C) has no admissible start at all, and a goal statement over
  its machine says nothing. The runtime supplies the idle root; `GabbroZiel`
  runs the machine of `P.mitRuhe` (assumption A4).

  THE ENCODING. `Fn := Option D.Fn`; `some f` is `f`, `none` is the root.
  Signature numbers shift by one: `some f` has number `D.sig f + 1`, the
  root has `0`, and `sigNr (n + 1)` is `D.sigNr n` with its types shifted
  (`sigR`). Function-pointer types shift with them (`tyR`: `fnptr n` ↦
  `fnptr (n + 1)`, every other type unchanged), so a value of a shifted type
  is a value of the original type (`valR`/`valZ`, inverse to each other: the
  root has number `0`, which no shifted type names -- no value of `P.mitRuhe`
  ever points to the root). Every other field of `D` is kept; field, global,
  axiom and register types are shifted. Resources, events, worlds,
  environments and memories carry over (`resR`, `evR`, `worldR`, `envR`,
  `speicherR`, with inverses), and so do oracles (`Orakel.mitRuhe`) and lock
  invariant families (`SperrInv.mitRuhe`).

  THE PROGRAM. `P.mitRuhe` translates every body, `requires`, `ensures`
  and invariant of `P` constructor by constructor (`ruE`, `ruS`, `ruB`,
  `ruEnd`, ...): `f ↦ some f`, `fnptr n ↦ fnptr (n + 1)`, everything else
  the same constructor. Where a typing index is equal only propositionally
  (the holdings after a call, `nach`; after `advances`/`retires`; the
  holdings at entry and at return), the term is transported along the
  equation (`Stmt.nachΛ`, `Block.vorΛ`, `Endblock.umΛ`, `Expr.umΛ`,
  `Expr.umΓ`). The root's `requires`/`ensures` are `true`, its body is
  `return`.

  What it would mean if it were wrong: a translation that changed a body
  would make every conjunct of `GabbroZiel` speak about another program.
  The transfer theorems (`MitRuheStatisch.lean`, `MitRuheSemantik.lean`)
  state that it does not: every checker fact of `P` holds of `P.mitRuhe` at
  `some f`, and every function behaves in `P.mitRuhe` as in `P`.
-/
import Grammatik.SperreSem

namespace Gabbro.Grammatik

/-! ## 1. Types, signatures, the declaration -/

/-- Types of `D.mitRuhe`: function-pointer numbers shift by one. -/
@[reducible] def tyR : Ty → Ty
  | .int lo hi => .int lo hi
  | .bool => .bool
  | .opt n => .opt n
  | .sum cs => .sum cs
  | .grund n => .grund n
  | .never => .never
  | .fl lo hi => .fl lo hi
  | .fnptr n => .fnptr (n + 1)
  | .ptr t rw => .ptr t rw

/-- A signature with its types shifted. -/
def sigR {Tab Glob Lock Marke : Type} (S : Signatur Tab Glob Lock Marke) :
    Signatur Tab Glob Lock Marke :=
  { S with params := S.params.map tyR, erg := S.erg.map tyR }

/-- **The idle root's signature**: no parameter, no result, no reason, no
    lock, no write, no mark, no floor. -/
def sigRuheM (Tab Glob Lock Marke : Type) : Signatur Tab Glob Lock Marke where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []
  boden := none

variable {D : Deklaration}

/-- Signature numbers of `D.mitRuhe`: the root `0`, `some f` one above `f`. -/
def sigM (D : Deklaration) : Option D.Fn → Nat
  | some f => D.sig f + 1
  | none => 0

/-- The signature table of `D.mitRuhe`. -/
def sigNrM (D : Deklaration) : Nat → Signatur D.Tab D.Glob D.Lock D.Marke
  | 0 => sigRuheM _ _ _ _
  | n + 1 => sigR (D.sigNr n)

/-- A value of `τ` as a value of the shifted `τ`. -/
@[reducible] def valR : (τ : Ty) → Val D.Fn D.sig τ → Val (Option D.Fn) (sigM D) (tyR τ)
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum _, v => v
  | .grund _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr _, v => ⟨some v.1, congrArg (· + 1) v.2⟩
  | .ptr _ _, v => v

/-- A value of the shifted `τ` as a value of `τ` (the root has number `0`,
    which no shifted pointer type names). -/
def valZ : (τ : Ty) → Val (Option D.Fn) (sigM D) (tyR τ) → Val D.Fn D.sig τ
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum _, v => v
  | .grund _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr n, v => match v with
    | ⟨some f, h⟩ => ⟨f, by simp only [sigM] at h; omega⟩
    | ⟨none, h⟩ => absurd h (by simp [sigM])
  | .ptr _ _, v => v

theorem valZ_valR : ∀ (τ : Ty) (v : Val D.Fn D.sig τ), valZ τ (valR τ v) = v
  | .int _ _, _ => rfl
  | .bool, _ => rfl
  | .opt _, _ => rfl
  | .sum _, _ => rfl
  | .grund _, _ => rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr _, ⟨_, _⟩ => rfl
  | .ptr _ _, _ => rfl

theorem valR_valZ : ∀ (τ : Ty) (v : Val (Option D.Fn) (sigM D) (tyR τ)), valR τ (valZ τ v) = v
  | .int _ _, _ => rfl
  | .bool, _ => rfl
  | .opt _, _ => rfl
  | .sum _, _ => rfl
  | .grund _, _ => rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr n, ⟨some f, h⟩ => rfl
  | .fnptr n, ⟨none, h⟩ => absurd h (by simp [sigM])
  | .ptr _ _, _ => rfl

/-- **`D` plus the runtime's idle root.** Every carrier, lock, mark,
    invariant, axiom and register is `D`'s; field, global, axiom and
    register types are shifted (`tyR`); the functions are `some f` and the
    root `none`. -/
@[reducible] def Deklaration.mitRuhe (D : Deklaration) : Deklaration where
  Tab := D.Tab
  decTab := D.decTab
  count := D.count
  Feld := D.Feld
  decFeld := D.decFeld
  typ := fun t f => tyR (D.typ t f)
  erlaubt := D.erlaubt
  tabNr := D.tabNr
  Glob := D.Glob
  decGlob := D.decGlob
  gtyp := fun g => tyR (D.gtyp g)
  nutzlast := D.nutzlast
  atomar := D.atomar
  geteilt := D.geteilt
  ggeteilt := D.ggeteilt
  Lock := D.Lock
  decLock := D.decLock
  rang := D.rang
  maskiert := D.maskiert
  Marke := D.Marke
  decMarke := D.decMarke
  stufen := D.stufen
  braucht := D.braucht
  gbraucht := D.gbraucht
  eigner := D.eigner
  Fn := Option D.Fn
  sig := sigM D
  sigNr := sigNrM D
  eigner_nie_erzeugt := fun n t m s hm => match n with
    | 0 => by simp [sigNrM, sigRuheM]
    | n + 1 => D.eigner_nie_erzeugt n t m s hm
  Inv := D.Inv
  traeger := D.traeger
  invs := D.invs
  Ax := D.Ax
  aparams := fun a => (D.aparams a).map tyR
  aerg := fun a => (D.aerg a).map tyR
  aschreibt := D.aschreibt
  agschreibt := D.agschreibt
  Reg := D.Reg
  rtyp := fun r => tyR (D.rtyp r)
  rklasse := D.rklasse
  spiegel := D.spiegel
  rzusage := fun r v => D.rzusage r (valZ (D.rtyp r) v)
  rtraeger := D.rtraeger
  Annahme := D.Annahme
  a10 := D.a10
  geteilt_bewacht := D.geteilt_bewacht
  invarianten_gehalten := fun n i h t ht L hL => match n with
    | 0 => by simp [sigNrM, sigRuheM] at h
    | n + 1 => D.invarianten_gehalten n i h t ht L hL
  ggeteilt_bewacht := D.ggeteilt_bewacht
  geist := D.geist
  ggeist := D.ggeist
  -- **Lane O-1:** the clone gates travel to the idle-root declaration --
  -- axioms are `D`'s, functions gain the root (`some`), so each gate keeps
  -- its axiom and maps its entry.
  klon := D.klon.map fun (a, f) => (a, some f)

instance instDecEqFnMitRuhe [DecidableEq D.Fn] : DecidableEq D.mitRuhe.Fn :=
  inferInstanceAs (DecidableEq (Option D.Fn))

/-- The idle root of `D.mitRuhe`. -/
def ruheFn (D : Deklaration) : D.mitRuhe.Fn := none

/-! ## 2. Resources, events, worlds, environments, memories -/

/-- A resource of `D` as a resource of `D.mitRuhe`. -/
def resR : Res D → Res D.mitRuhe
  | .held L => .held L
  | .marke m s => .marke m s

/-- A resource of `D.mitRuhe` as a resource of `D`. -/
def resZ : Res D.mitRuhe → Res D
  | .held L => .held L
  | .marke m s => .marke m s

theorem rz_rm (r : Res D) : resZ (resR r) = r := by cases r <;> rfl

theorem rm_rz (r : Res D.mitRuhe) : resR (resZ r) = r := by cases r <;> rfl

theorem rm_inj {a b : Res D} (h : resR a = resR b) : a = b := by
  rw [← rz_rm a, ← rz_rm b, h]

theorem map_rz_rm (Λ : List (Res D)) : (Λ.map resR).map resZ = Λ := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id Λ]
  exact List.map_congr_left fun r _ => rz_rm r

theorem map_rm_rz (Λ : List (Res D.mitRuhe)) : (Λ.map resZ).map resR = Λ := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id Λ]
  exact List.map_congr_left fun r _ => rm_rz r

/-- An event of `D` as an event of `D.mitRuhe`. -/
def evR : Ereignis D → Ereignis D.mitRuhe
  | .zugriff t w Λ h => .zugriff t w (Λ.map resR) h
  | .gzugriff g w Λ h => .gzugriff g w (Λ.map resR) h
  | .nimmt L h => .nimmt L h
  | .gibt L => .gibt L

/-- An event of `D.mitRuhe` as an event of `D`. -/
def evZ : Ereignis D.mitRuhe → Ereignis D
  | .zugriff t w Λ h => .zugriff t w (Λ.map resZ) h
  | .gzugriff g w Λ h => .gzugriff g w (Λ.map resZ) h
  | .nimmt L h => .nimmt L h
  | .gibt L => .gibt L

theorem evZ_evR (e : Ereignis D) : evZ (evR e) = e := by
  cases e <;> simp only [evR, evZ, map_rz_rm]

theorem evR_evZ (e : Ereignis D.mitRuhe) : evR (evZ e) = e := by
  cases e <;> simp only [evR, evZ, map_rm_rz]

/-- A world of `D` as a world of `D.mitRuhe`. -/
def worldR (σ : World D) : World D.mitRuhe :=
  ⟨fun t k f => valR (D.typ t f) (σ.slots t k f), fun g => valR (D.gtyp g) (σ.globs g),
    σ.spur.map evR⟩

/-- A world of `D.mitRuhe` as a world of `D`. -/
def worldZ (σ : World D.mitRuhe) : World D :=
  ⟨fun t k f => valZ (D.typ t f) (σ.slots t k f), fun g => valZ (D.gtyp g) (σ.globs g),
    σ.spur.map evZ⟩

/-- A memory of `D` as a memory of `D.mitRuhe`. -/
def speicherR (s : Speicher D) : Speicher D.mitRuhe :=
  ⟨fun t k f => valR (D.typ t f) (s.slots t k f), fun g => valR (D.gtyp g) (s.globs g)⟩

/-- A memory of `D.mitRuhe` as a memory of `D`. -/
def speicherZ (s : Speicher D.mitRuhe) : Speicher D :=
  ⟨fun t k f => valZ (D.typ t f) (s.slots t k f), fun g => valZ (D.gtyp g) (s.globs g)⟩

theorem speicherZ_speicherR (s : Speicher D) : speicherZ (speicherR s) = s := by
  cases s
  simp only [speicherZ, speicherR, valZ_valR]

/-- An environment of `D` as an environment of `D.mitRuhe`. -/
def envR : {Γ : Ctx} → Env D Γ → Env D.mitRuhe (Γ.map tyR)
  | _, .nil => .nil
  | _ :: _, .cons v ρ => .cons (valR _ v) (envR ρ)

/-- An environment of `D.mitRuhe` as an environment of `D`. -/
def envZ : {Γ : Ctx} → Env D.mitRuhe (Γ.map tyR) → Env D Γ
  | [], _ => .nil
  | τ :: _, ρ => match ρ with
    | .cons v ρ => .cons (valZ τ v) (envZ ρ)

/-! ## 3. Contracts and the equations of the holdings -/

/-- A contract of `D` as a contract of `D.mitRuhe`. -/
def vertragR (V : Vertrag D) : Vertrag D.mitRuhe :=
  ⟨V.schreibt, V.gschreibt, V.erg.map tyR, V.gruende, V.haelt, V.produziert, V.boden⟩

theorem von_rm (w : D.Lock ⊕ (D.Marke × Nat)) : Res.von D.mitRuhe w = resR (Res.von D w) := by
  rcases w with L | ⟨m, s⟩ <;> rfl

theorem vonMarke_rm (m : D.Marke × Nat) : Res.vonMarke D.mitRuhe m = resR (Res.vonMarke D m) := by
  rcases m with ⟨m, s⟩; rfl

theorem darfR {t : D.Tab} {Λ : List (Res D)} (h : darf D t Λ) : darf D.mitRuhe t (Λ.map resR) :=
  fun w hw => by rw [von_rm (D := D) w]; exact List.mem_map_of_mem (h w hw)

theorem gdarfR {g : D.Glob} {Λ : List (Res D)} (h : gdarf D g Λ) :
    gdarf D.mitRuhe g (Λ.map resR) :=
  fun w hw => by rw [von_rm (D := D) w]; exact List.mem_map_of_mem (h w hw)

theorem mem_map_rm {r : Res D} {Λ : List (Res D)} : resR r ∈ Λ.map resR ↔ r ∈ Λ := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := List.mem_map.mp h
    rw [← rm_inj he]
    exact ha
  · exact List.mem_map_of_mem

theorem held_mem_map {L : D.Lock} {Λ : List (Res D)} :
    (Res.held L : Res D.mitRuhe) ∈ Λ.map resR ↔ Res.held L ∈ Λ :=
  mem_map_rm (r := Res.held L)

theorem erase_map_rm (Λ : List (Res D)) (a : Res D) :
    (Λ.erase a).map resR = (Λ.map resR).erase (resR a) := by
  induction Λ with
  | nil => rfl
  | cons b Λ ih =>
      by_cases h : b = a
      · subst h
        simp
      · have h' : resR b ≠ resR a := fun e => h (rm_inj e)
        simp [h, h', ih]

theorem map_held_rm (l : List D.Lock) :
    (l.map (Res.held (D := D))).map resR = l.map (Res.held (D := D.mitRuhe)) := by
  induction l with
  | nil => rfl
  | cons L l ih => simp only [List.map_cons, ih]; rfl

theorem map_vonMarke_rm (l : List (D.Marke × Nat)) :
    (l.map (Res.vonMarke D)).map resR = l.map (Res.vonMarke D.mitRuhe) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
      rcases m with ⟨m, s⟩
      show _ :: _ = _ :: _
      rw [ih]
      rfl

theorem ende_map (V : Vertrag D) : V.ende.map resR = (vertragR V).ende := by
  simp only [Vertrag.ende, List.map_append, map_held_rm, map_vonMarke_rm]
  rfl

theorem anfang_map (S : Signatur D.Tab D.Glob D.Lock D.Marke) :
    (Signatur.anfang D S).map resR = Signatur.anfang D.mitRuhe (sigR S) := by
  simp only [Signatur.anfang, List.map_append, map_held_rm, map_vonMarke_rm]
  rfl

theorem foldl_erase_map (ks : List (D.Marke × Nat)) (Λ : List (Res D)) :
    (ks.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ).map resR =
      ks.foldl (fun (acc : List (Res D.mitRuhe)) (m : D.Marke × Nat) =>
        acc.erase (Res.vonMarke D.mitRuhe m)) (Λ.map resR) := by
  induction ks generalizing Λ with
  | nil => rfl
  | cons k ks ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, erase_map_rm, ← vonMarke_rm (D := D) k]

theorem nachSig_map (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) :
    (nachSig D S Λ).map resR = nachSig D.mitRuhe (sigR S) (Λ.map resR) := by
  simp only [nachSig, List.map_append, map_vonMarke_rm, foldl_erase_map]
  rfl

theorem nach_map (f : D.Fn) (Λ : List (Res D)) :
    (nach D f Λ).map resR = nach D.mitRuhe (some f) (Λ.map resR) :=
  nachSig_map (D.signatur f) Λ

theorem invSicht_map (i : D.Inv) : (invSicht D i).map resR = invSicht D.mitRuhe i := by
  simp only [invSicht]
  show ((D.traeger i).foldr (fun t acc => (D.braucht t).map (Res.von D) ++ acc) []).map resR =
    (D.traeger i).foldr (fun t (acc : List (Res D.mitRuhe)) =>
      (D.braucht t).map (Res.von D.mitRuhe) ++ acc) []
  induction D.traeger i with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.foldr_cons, List.map_append, ih]
      congr 1
      rw [List.map_map]
      exact List.map_congr_left fun w _ => (von_rm (D := D) w).symm

theorem ergCtx_map (Γ : Ctx) (e : Option Ty) :
    (ErgCtx Γ e).map tyR = ErgCtx (Γ.map tyR) (e.map tyR) := by
  cases e <;> rfl

theorem rufPasstR {V : Vertrag D} {S : Signatur D.Tab D.Glob D.Lock D.Marke}
    {Λ : List (Res D)} (h : RufPasst D V S Λ) : RufPasst D.mitRuhe (vertragR V) (sigR S) (Λ.map resR) where
  hw := h.hw
  hg := h.hg
  hk := by
    obtain ⟨l, hp, hs⟩ := h.hk
    refine ⟨l.map resR, ?_, hs.map resR⟩
    have e := map_vonMarke_rm (D := D) S.konsumiert
    show (S.konsumiert.map (Res.vonMarke D.mitRuhe)).Perm (l.map resR)
    rw [← e]
    exact hp.map resR
  hh := fun L hL => held_mem_map.mpr (h.hh L hL)
  hx := fun L hL hn => h.hx L (held_mem_map.mp hL) hn
  hb := h.hb

/-! ## 4. The syntax translation -/

/-- A variable of `Γ` as a variable of the shifted `Γ`. -/
def varR : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Var (Γ.map tyR) (tyR τ)
  | _, _, .hier => .hier
  | _, _, .dort x => .dort (varR x)

/-- Transport an expression along an equation of its holdings. -/
def Expr.umΛ {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (h : Λ = Λ') (e : Expr D Γ Λ τ) :
    Expr D Γ Λ' τ := h ▸ e

/-- Transport an expression along an equation of its scope. -/
def Expr.umΓ {Γ Γ' : Ctx} {Λ : List (Res D)} {τ : Ty} (h : Γ = Γ') (e : Expr D Γ Λ τ) :
    Expr D Γ' Λ τ := h ▸ e

/-- Transport a statement along an equation of its holdings AFTER. -/
def Stmt.nachΛ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) : Stmt D V l Γ Λ Λ₂ := h ▸ s

/-- Transport a block along an equation of its holdings BEFORE. -/
def Block.vorΛ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') : Block D V l Γ Λ₂ Λ' := h ▸ b

/-- Transport an end block along an equation of its holdings. -/
def Endblock.umΛ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) : Endblock D V l Γ Λ₂ := h ▸ e

mutual

/-- **An expression of `D` as an expression of `D.mitRuhe`**: the same
    constructor, `f ↦ some f` in `&f`. -/
def ruE : {Γ : Ctx} → {Λ : List (Res D)} → {τ : Ty} → Expr D Γ Λ τ →
    Expr D.mitRuhe (Γ.map tyR) (Λ.map resR) (tyR τ)
  | _, _, _, .lit n => .lit n
  | _, _, _, .wahr => .wahr
  | _, _, _, .falsch => .falsch
  | _, _, _, .var x => .var (varR x)
  | _, _, _, .glob g hL => Expr.glob (D := D.mitRuhe) g (gdarfR hL)
  | _, _, _, .slot t f i hL => Expr.slot (D := D.mitRuhe) t f (ruE i) (darfR hL)
  | _, _, _, .durch p t ht f i hL => Expr.durch (D := D.mitRuhe) (ruE p) t ht f (ruE i) (darfR hL)
  | _, _, _, .ptrOf t n ht rw => Expr.ptrOf (D := D.mitRuhe) t n ht rw
  | _, _, _, .fnref f n h => .fnref (D := D.mitRuhe) (some f) (n + 1) (congrArg (· + 1) h)
  | _, _, _, .altGlob g hL => Expr.altGlob (D := D.mitRuhe) g (gdarfR hL)
  | _, _, _, .altSlot t f i hL => Expr.altSlot (D := D.mitRuhe) t f (ruE i) (darfR hL)
  | _, _, _, .weiter h1 h2 e => .weiter h1 h2 (ruE e)
  | _, _, _, .add a b => .add (ruE a) (ruE b)
  | _, _, _, .sub a b => .sub (ruE a) (ruE b)
  | _, _, _, .neg a => .neg (ruE a)
  | _, _, _, .mul a b => .mul (ruE a) (ruE b)
  | _, _, _, .div h0 h1 a b => .div h0 h1 (ruE a) (ruE b)
  | _, _, _, .rem h0 h1 a b => .rem h0 h1 (ruE a) (ruE b)
  | _, _, _, .sdiv hb a b => .sdiv hb (ruE a) (ruE b)
  | _, _, _, .srem hb a b => .srem hb (ruE a) (ruE b)
  | _, _, _, .leseBytes t f hf n i hlo hhi hL =>
      .leseBytes (D := D.mitRuhe) t f (congrArg tyR hf) n (ruE i) hlo
        hhi (darfR hL)
  | _, _, _, .band h0 h0' a b => .band h0 h0' (ruE a) (ruE b)
  | _, _, _, .bor w h0 h0' hw1 hw2 a b => .bor w h0 h0' hw1 hw2 (ruE a) (ruE b)
  | _, _, _, .bxor w h0 h0' hw1 hw2 a b => .bxor w h0 h0' hw1 hw2 (ruE a) (ruE b)
  | _, _, _, .shl w hw1 hw2 h0 h0' a b => .shl w hw1 hw2 h0 h0' (ruE a) (ruE b)
  | _, _, _, .shr w hw1 hw2 h0 h0' a b => .shr w hw1 hw2 h0 h0' (ruE a) (ruE b)
  | _, _, _, .lt a b => .lt (ruE a) (ruE b)
  | _, _, _, .le a b => .le (ruE a) (ruE b)
  | _, _, _, .eq a b => .eq (ruE a) (ruE b)
  | _, _, _, .fllt a b => .fllt (ruE a) (ruE b)
  | _, _, _, .flle a b => .flle (ruE a) (ruE b)
  | _, _, _, .und a b => .und (ruE a) (ruE b)
  | _, _, _, .oder a b => .oder (ruE a) (ruE b)
  | _, _, _, .nicht a => .nicht (ruE a)
  | _, _, _, .none n => .none n
  | _, _, _, .some e => .some (ruE e)
  | _, _, _, .istSome e => .istSome (ruE e)
  | _, _, _, .fall cs i nutz => .fall cs i (ruN nutz)
  | _, _, _, .grund n r => .grund n r
  | _, _, _, .forallSlots t body hL => Expr.forallSlots (D := D.mitRuhe) t (ruE body) (darfR hL)
  | _, _, _, .existsSlots t body hL => Expr.existsSlots (D := D.mitRuhe) t (ruE body) (darfR hL)
  | _, _, _, .reaches t f hf a b hL =>
      .reaches (D := D.mitRuhe) t f (congrArg tyR hf) (ruE a) (ruE b)
        (darfR hL)

/-- A payload expression, translated. -/
def ruN : {Γ : Ctx} → {Λ : List (Res D)} → {c : Option (Int × Int)} → NutzlastExpr D Γ Λ c →
    NutzlastExpr D.mitRuhe (Γ.map tyR) (Λ.map resR) c
  | _, _, _, .keine => .keine
  | _, _, _, .zahl e => .zahl (ruE e)

end

/-- Arguments, translated. -/
def ruA : {Γ : Ctx} → {Λ : List (Res D)} → {τs : List Ty} → Args D Γ Λ τs →
    Args D.mitRuhe (Γ.map tyR) (Λ.map resR) (τs.map tyR)
  | _, _, _, .nil => .nil
  | _, _, _, .cons e rest => .cons (ruE e) (ruA rest)

/-- A result expression, translated. -/
def ruErg : {Γ : Ctx} → {Λ : List (Res D)} → {e : Option Ty} → ErgExpr D Γ Λ e →
    ErgExpr D.mitRuhe (Γ.map tyR) (Λ.map resR) (e.map tyR)
  | _, _, _, .keine => .keine
  | _, _, _, .wert e => .wert (ruE e)

mutual

/-- **A statement of `D` as a statement of `D.mitRuhe`**: the same
    constructor, `f ↦ some f` in calls, holdings transported where their
    equation is propositional. -/
def ruS {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Stmt D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR)
  | _, _, _, _, .assignSlot t f i e hw hL => .assignSlot t f (ruE i) (ruE e) hw (darfR hL)
  | _, _, _, _, .assignDurch p t ht f i e hw hL =>
      .assignDurch (ruE p) t ht f (ruE i) (ruE e) hw (darfR hL)
  | _, _, _, _, .assignGlob g e hw hL => .assignGlob g (ruE e) hw (gdarfR hL)
  | _, _, _, _, .schreibBytes t f hf n i hlo hhi e hw hL =>
      .schreibBytes (V := vertragR V) t f (congrArg tyR hf) n (ruE i) hlo hhi
        (ruE e) hw (darfR hL)
  | _, _, _, _, .assignVar x e => .assignVar (varR x) (ruE e)
  | _, _, _, _, .uebergang t f hτ i von nach hn he hw hL =>
      .uebergang (V := vertragR V) t f (congrArg tyR hτ) (ruE i) von nach hn
        he hw (darfR hL)
  | _, _, _, _, .ite c t e => .ite (ruE c) (ruB t) (ruB e)
  | _, _, _, _, .onOption o p a => .onOption (ruE o) (ruB p) (ruB a)
  | _, _, _, _, .onTag v arms => .onTag (ruE v) (ruArms arms)
  | _, _, _, _, .onGrund r arms => .onGrund (ruE r) (ruGArms arms)
  | _, _, Λ, _, .call f args hp hr =>
      Stmt.nachΛ (nach_map f Λ).symm
        (.call (V := vertragR V) (some f) (ruA args) (rufPasstR hp) hr)
  | _, _, Λ, _, .callInd (n := n) p args hp hr =>
      Stmt.nachΛ (nachSig_map (D.sigNr n) Λ).symm
        (.callInd (V := vertragR V) (n := n + 1) (ruE p) (ruA args) (rufPasstR hp) hr)
  | _, _, _, _, .locks L hr body =>
      .locks L (fun M hM => hr M (held_mem_map.mp hM)) (ruB body)
  | _, _, _, _, .breaking i body => .breaking i (ruB body)
  | _, _, _, _, .traverse t inv body => .traverse t (ruE inv) (ruB body)
  | _, _, _, _, .retry n bis body ueber => .retry n (ruE bis) (ruB body) (ruB ueber)
  | _, _, _, _, .forever a inv body => .forever a (ruE inv) (ruB body)
  | _, _, _, _, .axiomCall a args h hw hg hd hgd =>
      .axiomCall (V := vertragR V) a (ruA args) (by show Option.map tyR (D.aerg a) = _; rw [h]; rfl)
        hw hg (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg'))
  | _, _, _, _, .regSchreib r hk e => .regSchreib r hk (ruE e)
  | _, _, _, _, .transition r hk m hm hl maske bits => .transition r hk m hm hl maske bits
  | _, _, _, _, .publish g e payload hp hw hL => .publish g (ruE e) payload hp hw (gdarfR hL)
  | _, _, Λ, _, .advances m a h hs =>
      Stmt.nachΛ (by rw [List.map_append, erase_map_rm]; rfl)
        (.advances (V := vertragR V) m a (mem_map_rm.mpr h) hs)
  | _, _, Λ, _, .retires m s h a =>
      Stmt.nachΛ (by rw [erase_map_rm]; rfl) (.retires (V := vertragR V) m s (mem_map_rm.mpr h) a)
  | _, _, _, _, .ret e hΛ => .ret (ruErg e) ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, _, .retGrund r hΛ => .retGrund r ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, _, .leave h => .leave h
  | _, _, _, _, .next h => .next h

/-- A block, translated. -/
def ruB {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Block D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons s rest => .cons (ruS s) (ruB rest)
  | _, _, _, _, .bind e rest => .bind (ruE e) (ruB rest)
  | _, _, Λ, _, .bindCall f args he hp hr rest =>
      .bindCall (V := vertragR V) (some f) (ruA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Block.vorΛ (nach_map f Λ) (ruB rest))
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest =>
      .bindCallInd (V := vertragR V) (n := n + 1) (ruE p) (ruA args)
        (by show Option.map tyR (D.sigNr n).erg = _; rw [he]; rfl) (rufPasstR hp) hr
        (Block.vorΛ (nachSig_map (D.sigNr n) Λ) (ruB rest))
  | _, _, Λ, _, .bindCallElse f args he hp hr err rest =>
      .bindCallElse (V := vertragR V) (some f) (ruA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Endblock.umΛ (nach_map f Λ) (ruEnd err)) (Block.vorΛ (nach_map f Λ) (ruB rest))
  | _, _, _, _, .bindAxiom a args he hw hg hd hgd rest =>
      .bindAxiom (V := vertragR V) a (ruA args)
        (by show Option.map tyR (D.aerg a) = _; rw [he]; rfl) hw hg
        (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg')) (ruB rest)
  | _, _, _, _, .regLies r hk rest => .regLies r hk (ruB rest)
  | _, _, _, _, .regLiesElse r hk zusage sonst rest =>
      .regLiesElse r hk (ruE zusage) (ruEnd sonst) (ruB rest)
  | _, _, _, _, .awaits g payload hp hL rest => .awaits g payload hp (gdarfR hL) (ruB rest)
  | _, _, _, _, .exchange g neu hw hL rest => .exchange g (ruE neu) hw (gdarfR hL) (ruB rest)
  | _, _, _, _, .narrow e lo' hi' sonst rest => .narrow (ruE e) lo' hi' (ruEnd sonst) (ruB rest)
  | _, _, _, _, .pruefung c sonst rest => .pruefung (ruE c) (ruEnd sonst) (ruB rest)
  | _, _, _, _, .gleit op a b lo hi rest => .gleit op (ruE a) (ruE b) lo hi (ruB rest)
  | _, _, _, _, .gleitLit q lo hi rest => .gleitLit q lo hi (ruB rest)
  | _, _, _, _, .gleitVon e lo hi rest => .gleitVon (ruE e) lo hi (ruB rest)
  | _, _, _, _, .gleitNarrow e lo hi sonst rest =>
      .gleitNarrow (ruE e) lo hi (ruEnd sonst) (ruB rest)

/-- An end block, translated. -/
def ruEnd {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Endblock D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR)
  | _, _, _, .ret e hΛ => .ret (ruErg e) ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, .retGrund r hΛ => .retGrund r ((hΛ.map resR).trans (by rw [ende_map]))
  | _, _, _, .leave h => .leave h
  | _, _, _, .next h => .next h
  | _, _, _, .cons s rest => .cons (ruS s) (ruEnd rest)
  | _, _, _, .bind e rest => .bind (ruE e) (ruEnd rest)

/-- Arms, translated (the arm scope `ArmCtx` is split on the case). -/
def ruArms {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs →
      Arms D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR) cs
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons (c := none) b rest => .cons (c := none) (ruB b) (ruArms rest)
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest =>
      .cons (c := some (lo, hi)) (ruB b) (ruArms rest)

/-- Reason arms, translated. -/
def ruGArms {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    GrundArms D V l Γ Λ Λ' n → GrundArms D.mitRuhe (vertragR V) l (Γ.map tyR) (Λ.map resR) (Λ'.map resR) n
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons b rest => .cons (ruB b) (ruGArms rest)

end

/-! ## 5. The program, the oracle, the lock invariants -/

/-- **`P` over `D.mitRuhe`**: every function `some f` is `f` translated;
    the idle root `none` has `requires true`, `ensures true`, body
    `return`. -/
def Programm.mitRuhe (P : Programm D) : Programm D.mitRuhe where
  invariante i := Expr.umΛ (invSicht_map (D := D) i) (ruE (P.invariante i))
  requires
    | none => .wahr
    | some f => Expr.umΛ (anfang_map (D.signatur f)) (ruE (P.requires f))
  ensures
    | none => .wahr
    | some f => Expr.umΓ (ergCtx_map (D.params f) (D.erg f))
        (Expr.umΛ (ende_map (vertragVon D f)) (ruE (P.ensures f)))
  rumpf
    | none => .ret .keine List.Perm.nil
    | some f => Endblock.umΛ (anfang_map (D.signatur f)) (ruEnd (P.rumpf f))

/-- The member list of `D.mitRuhe`'s functions: the root, then `fs`. -/
def fsRuhe (fs : List D.Fn) : List D.mitRuhe.Fn := none :: fs.map some

theorem fsRuhe_voll {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) :
    ∀ g : D.mitRuhe.Fn, g ∈ fsRuhe fs
  | none => List.mem_cons_self
  | some g => List.mem_cons_of_mem _ (List.mem_map_of_mem (hvoll g))

/-- The declared starts, as functions of `D.mitRuhe`. -/
def wsRuhe (ws : List D.Fn) : List D.mitRuhe.Fn := ws.map some

/-- **The oracle of `D.mitRuhe`**: `O` on the translated-back world and
    arguments, its world translated forth. -/
def Orakel.mitRuhe (O : Orakel D) : Orakel D.mitRuhe where
  wirkt a σ ρ :=
    (worldR (O.wirkt a (worldZ σ) (envZ (Γ := D.aparams a) ρ)).1,
      (O.wirkt a (worldZ σ) (envZ (Γ := D.aparams a) ρ)).2)
  regLies r σ := O.regLies r (worldZ σ)
  regSchreib := O.regSchreib
  sichtbar g σ := O.sichtbar g (worldZ σ)
  zeiger k := (O.zeiger k).map some

/-- **The lock invariants of `D.mitRuhe`**: the same carriers, `S.inv` on the
    translated-back memory. -/
def SperrInv.mitRuhe (S : SperrInv D) : SperrInv D.mitRuhe :=
  ⟨S.orte, fun L s => S.inv L (speicherZ s)⟩

end Gabbro.Grammatik
