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
  environments and memories carry over (`rm`, `evR`, `worldR`, `envR`,
  `speicherR`, with inverses), and so do oracles (`Orakel.mitRuhe`) and lock
  invariant families (`SperrInv.mitRuhe`).

  THE PROGRAM. `P.mitRuhe` translates every body, `requires`, `ensures`
  and invariant of `P` constructor by constructor (`renE`, `renS`, `renB`,
  `renEnd`, ...): `f ↦ some f`, `fnptr n ↦ fnptr (n + 1)`, everything else
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
def tyR : Ty → Ty
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
def sigRuhe (Tab Glob Lock Marke : Type) : Signatur Tab Glob Lock Marke where
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
  | 0 => sigRuhe _ _ _ _
  | n + 1 => sigR (D.sigNr n)

/-- A value of `τ` as a value of the shifted `τ`. -/
def valR : (τ : Ty) → Val D.Fn D.sig τ → Val (Option D.Fn) (sigM D) (tyR τ)
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
def Deklaration.mitRuhe (D : Deklaration) : Deklaration where
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
    | 0 => by simp [sigNrM, sigRuhe]
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
    | 0 => by simp [sigNrM, sigRuhe] at h
    | n + 1 => D.invarianten_gehalten n i h t ht L hL
  ggeteilt_bewacht := D.ggeteilt_bewacht
  geist := D.geist
  ggeist := D.ggeist

/-- The idle root of `D.mitRuhe`. -/
def ruheFn (D : Deklaration) : D.mitRuhe.Fn := none

/-! ## 2. Resources, events, worlds, environments, memories -/

/-- A resource of `D` as a resource of `D.mitRuhe`. -/
def rm : Res D → Res D.mitRuhe
  | .held L => .held L
  | .marke m s => .marke m s

/-- A resource of `D.mitRuhe` as a resource of `D`. -/
def rz : Res D.mitRuhe → Res D
  | .held L => .held L
  | .marke m s => .marke m s

theorem rz_rm (r : Res D) : rz (rm r) = r := by cases r <;> rfl

theorem rm_rz (r : Res D.mitRuhe) : rm (rz r) = r := by cases r <;> rfl

theorem rm_inj {a b : Res D} (h : rm a = rm b) : a = b := by
  rw [← rz_rm a, ← rz_rm b, h]

theorem map_rz_rm (Λ : List (Res D)) : (Λ.map rm).map rz = Λ := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id Λ]
  exact List.map_congr_left fun r _ => rz_rm r

theorem map_rm_rz (Λ : List (Res D.mitRuhe)) : (Λ.map rz).map rm = Λ := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id Λ]
  exact List.map_congr_left fun r _ => rm_rz r

/-- An event of `D` as an event of `D.mitRuhe`. -/
def evR : Ereignis D → Ereignis D.mitRuhe
  | .zugriff t w Λ h => .zugriff t w (Λ.map rm) h
  | .gzugriff g w Λ h => .gzugriff g w (Λ.map rm) h
  | .nimmt L h => .nimmt L h
  | .gibt L => .gibt L

/-- An event of `D.mitRuhe` as an event of `D`. -/
def evZ : Ereignis D.mitRuhe → Ereignis D
  | .zugriff t w Λ h => .zugriff t w (Λ.map rz) h
  | .gzugriff g w Λ h => .gzugriff g w (Λ.map rz) h
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
def vm (V : Vertrag D) : Vertrag D.mitRuhe :=
  ⟨V.schreibt, V.gschreibt, V.erg.map tyR, V.gruende, V.haelt, V.produziert, V.boden⟩

theorem von_rm (w : D.Lock ⊕ (D.Marke × Nat)) : Res.von D.mitRuhe w = rm (Res.von D w) := by
  rcases w with L | ⟨m, s⟩ <;> rfl

theorem vonMarke_rm (m : D.Marke × Nat) : Res.vonMarke D.mitRuhe m = rm (Res.vonMarke D m) := by
  rcases m with ⟨m, s⟩; rfl

theorem darfR {t : D.Tab} {Λ : List (Res D)} (h : darf D t Λ) : darf D.mitRuhe t (Λ.map rm) :=
  fun w hw => by rw [von_rm (D := D) w]; exact List.mem_map_of_mem (h w hw)

theorem gdarfR {g : D.Glob} {Λ : List (Res D)} (h : gdarf D g Λ) :
    gdarf D.mitRuhe g (Λ.map rm) :=
  fun w hw => by rw [von_rm (D := D) w]; exact List.mem_map_of_mem (h w hw)

theorem mem_map_rm {r : Res D} {Λ : List (Res D)} : rm r ∈ Λ.map rm ↔ r ∈ Λ := by
  constructor
  · intro h
    obtain ⟨a, ha, he⟩ := List.mem_map.mp h
    rw [← rm_inj he]
    exact ha
  · exact List.mem_map_of_mem

theorem held_mem_map {L : D.Lock} {Λ : List (Res D)} :
    (Res.held L : Res D.mitRuhe) ∈ Λ.map rm ↔ Res.held L ∈ Λ :=
  mem_map_rm (r := Res.held L)

theorem erase_map_rm (Λ : List (Res D)) (a : Res D) :
    (Λ.erase a).map rm = (Λ.map rm).erase (rm a) := by
  induction Λ with
  | nil => rfl
  | cons b Λ ih =>
      by_cases h : b = a
      · subst h
        simp
      · have h' : rm b ≠ rm a := fun e => h (rm_inj e)
        simp [h, h', ih]

theorem map_held_rm (l : List D.Lock) :
    (l.map (Res.held (D := D))).map rm = l.map (Res.held (D := D.mitRuhe)) := by
  induction l with
  | nil => rfl
  | cons L l ih => simp only [List.map_cons, ih]; rfl

theorem map_vonMarke_rm (l : List (D.Marke × Nat)) :
    (l.map (Res.vonMarke D)).map rm = l.map (Res.vonMarke D.mitRuhe) := by
  induction l with
  | nil => rfl
  | cons m l ih =>
      rcases m with ⟨m, s⟩
      show _ :: _ = _ :: _
      rw [ih]
      rfl

theorem ende_map (V : Vertrag D) : V.ende.map rm = (vm V).ende := by
  simp only [Vertrag.ende, List.map_append, map_held_rm, map_vonMarke_rm]
  rfl

theorem anfang_map (S : Signatur D.Tab D.Glob D.Lock D.Marke) :
    (Signatur.anfang D S).map rm = Signatur.anfang D.mitRuhe (sigR S) := by
  simp only [Signatur.anfang, List.map_append, map_held_rm, map_vonMarke_rm]
  rfl

theorem foldl_erase_map (ks : List (D.Marke × Nat)) (Λ : List (Res D)) :
    (ks.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ).map rm =
      ks.foldl (fun (acc : List (Res D.mitRuhe)) (m : D.Marke × Nat) =>
        acc.erase (Res.vonMarke D.mitRuhe m)) (Λ.map rm) := by
  induction ks generalizing Λ with
  | nil => rfl
  | cons k ks ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, erase_map_rm, ← vonMarke_rm (D := D) k]

theorem nachSig_map (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) :
    (nachSig D S Λ).map rm = nachSig D.mitRuhe (sigR S) (Λ.map rm) := by
  simp only [nachSig, List.map_append, map_vonMarke_rm, foldl_erase_map]
  rfl

theorem nach_map (f : D.Fn) (Λ : List (Res D)) :
    (nach D f Λ).map rm = nach D.mitRuhe (some f) (Λ.map rm) :=
  nachSig_map (D.signatur f) Λ

theorem invSicht_map (i : D.Inv) : (invSicht D i).map rm = invSicht D.mitRuhe i := by
  simp only [invSicht]
  show ((D.traeger i).foldr (fun t acc => (D.braucht t).map (Res.von D) ++ acc) []).map rm =
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
    {Λ : List (Res D)} (h : RufPasst D V S Λ) : RufPasst D.mitRuhe (vm V) (sigR S) (Λ.map rm) where
  hw := h.hw
  hg := h.hg
  hk := by
    obtain ⟨l, hp, hs⟩ := h.hk
    refine ⟨l.map rm, ?_, hs.map rm⟩
    have e := map_vonMarke_rm (D := D) S.konsumiert
    show (S.konsumiert.map (Res.vonMarke D.mitRuhe)).Perm (l.map rm)
    rw [← e]
    exact hp.map rm
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
def renE : {Γ : Ctx} → {Λ : List (Res D)} → {τ : Ty} → Expr D Γ Λ τ →
    Expr D.mitRuhe (Γ.map tyR) (Λ.map rm) (tyR τ)
  | _, _, _, .lit n => .lit n
  | _, _, _, .wahr => .wahr
  | _, _, _, .falsch => .falsch
  | _, _, _, .var x => .var (varR x)
  | _, _, _, .glob g hL => Expr.glob (D := D.mitRuhe) g (gdarfR hL)
  | _, _, _, .slot t f i hL => Expr.slot (D := D.mitRuhe) t f (renE i) (darfR hL)
  | _, _, _, .durch p t ht f i hL => Expr.durch (D := D.mitRuhe) (renE p) t ht f (renE i) (darfR hL)
  | _, _, _, .ptrOf t n ht rw => Expr.ptrOf (D := D.mitRuhe) t n ht rw
  | _, _, _, .fnref f n h => .fnref (D := D.mitRuhe) (some f) (n + 1) (congrArg (· + 1) h)
  | _, _, _, .altGlob g hL => Expr.altGlob (D := D.mitRuhe) g (gdarfR hL)
  | _, _, _, .altSlot t f i hL => Expr.altSlot (D := D.mitRuhe) t f (renE i) (darfR hL)
  | _, _, _, .weiter h1 h2 e => .weiter h1 h2 (renE e)
  | _, _, _, .add a b => .add (renE a) (renE b)
  | _, _, _, .sub a b => .sub (renE a) (renE b)
  | _, _, _, .neg a => .neg (renE a)
  | _, _, _, .mul a b => .mul (renE a) (renE b)
  | _, _, _, .div h0 h1 a b => .div h0 h1 (renE a) (renE b)
  | _, _, _, .rem h0 h1 a b => .rem h0 h1 (renE a) (renE b)
  | _, _, _, .sdiv hb a b => .sdiv hb (renE a) (renE b)
  | _, _, _, .srem hb a b => .srem hb (renE a) (renE b)
  | _, _, _, .leseBytes t f hf n i hlo hhi hL =>
      .leseBytes (D := D.mitRuhe) t f (by show tyR (D.typ t f) = _; rw [hf]; rfl) n (renE i) hlo
        hhi (darfR hL)
  | _, _, _, .band h0 h0' a b => .band h0 h0' (renE a) (renE b)
  | _, _, _, .bor w h0 h0' hw1 hw2 a b => .bor w h0 h0' hw1 hw2 (renE a) (renE b)
  | _, _, _, .bxor w h0 h0' hw1 hw2 a b => .bxor w h0 h0' hw1 hw2 (renE a) (renE b)
  | _, _, _, .shl w hw1 hw2 h0 h0' a b => .shl w hw1 hw2 h0 h0' (renE a) (renE b)
  | _, _, _, .shr w hw1 hw2 h0 h0' a b => .shr w hw1 hw2 h0 h0' (renE a) (renE b)
  | _, _, _, .lt a b => .lt (renE a) (renE b)
  | _, _, _, .le a b => .le (renE a) (renE b)
  | _, _, _, .eq a b => .eq (renE a) (renE b)
  | _, _, _, .fllt a b => .fllt (renE a) (renE b)
  | _, _, _, .flle a b => .flle (renE a) (renE b)
  | _, _, _, .und a b => .und (renE a) (renE b)
  | _, _, _, .oder a b => .oder (renE a) (renE b)
  | _, _, _, .nicht a => .nicht (renE a)
  | _, _, _, .none n => .none n
  | _, _, _, .some e => .some (renE e)
  | _, _, _, .istSome e => .istSome (renE e)
  | _, _, _, .fall cs i nutz => .fall cs i (renN nutz)
  | _, _, _, .grund n r => .grund n r
  | _, _, _, .forallSlots t body hL => Expr.forallSlots (D := D.mitRuhe) t (renE body) (darfR hL)
  | _, _, _, .existsSlots t body hL => Expr.existsSlots (D := D.mitRuhe) t (renE body) (darfR hL)
  | _, _, _, .reaches t f hf a b hL =>
      .reaches (D := D.mitRuhe) t f (by show tyR (D.typ t f) = _; rw [hf]; rfl) (renE a) (renE b)
        (darfR hL)

/-- A payload expression, translated. -/
def renN : {Γ : Ctx} → {Λ : List (Res D)} → {c : Option (Int × Int)} → NutzlastExpr D Γ Λ c →
    NutzlastExpr D.mitRuhe (Γ.map tyR) (Λ.map rm) c
  | _, _, _, .keine => .keine
  | _, _, _, .zahl e => .zahl (renE e)

end

/-- Arguments, translated. -/
def renA : {Γ : Ctx} → {Λ : List (Res D)} → {τs : List Ty} → Args D Γ Λ τs →
    Args D.mitRuhe (Γ.map tyR) (Λ.map rm) (τs.map tyR)
  | _, _, _, .nil => .nil
  | _, _, _, .cons e rest => .cons (renE e) (renA rest)

/-- A result expression, translated. -/
def renErg : {Γ : Ctx} → {Λ : List (Res D)} → {e : Option Ty} → ErgExpr D Γ Λ e →
    ErgExpr D.mitRuhe (Γ.map tyR) (Λ.map rm) (e.map tyR)
  | _, _, _, .keine => .keine
  | _, _, _, .wert e => .wert (renE e)

mutual

/-- **A statement of `D` as a statement of `D.mitRuhe`**: the same
    constructor, `f ↦ some f` in calls, holdings transported where their
    equation is propositional. -/
def renS {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Stmt D.mitRuhe (vm V) l (Γ.map tyR) (Λ.map rm) (Λ'.map rm)
  | _, _, _, _, .assignSlot t f i e hw hL => .assignSlot t f (renE i) (renE e) hw (darfR hL)
  | _, _, _, _, .assignDurch p t ht f i e hw hL =>
      .assignDurch (renE p) t ht f (renE i) (renE e) hw (darfR hL)
  | _, _, _, _, .assignGlob g e hw hL => .assignGlob g (renE e) hw (gdarfR hL)
  | _, _, _, _, .schreibBytes t f hf n i hlo hhi e hw hL =>
      .schreibBytes (V := vm V) t f (by show tyR (D.typ t f) = _; rw [hf]; rfl) n (renE i) hlo hhi
        (renE e) hw (darfR hL)
  | _, _, _, _, .assignVar x e => .assignVar (varR x) (renE e)
  | _, _, _, _, .uebergang t f hτ i von nach hn he hw hL =>
      .uebergang (V := vm V) t f (by show tyR (D.typ t f) = _; rw [hτ]; rfl) (renE i) von nach hn
        he hw (darfR hL)
  | _, _, _, _, .ite c t e => .ite (renE c) (renB t) (renB e)
  | _, _, _, _, .onOption o p a => .onOption (renE o) (renB p) (renB a)
  | _, _, _, _, .onTag v arms => .onTag (renE v) (renArms arms)
  | _, _, _, _, .onGrund r arms => .onGrund (renE r) (renGArms arms)
  | _, _, Λ, _, .call f args hp hr =>
      Stmt.nachΛ (nach_map f Λ).symm
        (.call (V := vm V) (some f) (renA args) (rufPasstR hp) hr)
  | _, _, Λ, _, .callInd (n := n) p args hp hr =>
      Stmt.nachΛ (nachSig_map (D.sigNr n) Λ).symm
        (.callInd (V := vm V) (n := n + 1) (renE p) (renA args) (rufPasstR hp) hr)
  | _, _, _, _, .locks L hr body =>
      .locks L (fun M hM => hr M (held_mem_map.mp hM)) (renB body)
  | _, _, _, _, .breaking i body => .breaking i (renB body)
  | _, _, _, _, .traverse t inv body => .traverse t (renE inv) (renB body)
  | _, _, _, _, .retry n bis body ueber => .retry n (renE bis) (renB body) (renB ueber)
  | _, _, _, _, .forever a inv body => .forever a (renE inv) (renB body)
  | _, _, _, _, .axiomCall a args h hw hg hd hgd =>
      .axiomCall (V := vm V) a (renA args) (by show Option.map tyR (D.aerg a) = _; rw [h]; rfl)
        hw hg (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg'))
  | _, _, _, _, .regSchreib r hk e => .regSchreib r hk (renE e)
  | _, _, _, _, .transition r hk m hm hl maske bits => .transition r hk m hm hl maske bits
  | _, _, _, _, .publish g e payload hp hw hL => .publish g (renE e) payload hp hw (gdarfR hL)
  | _, _, Λ, _, .advances m a h hs =>
      Stmt.nachΛ (by rw [List.map_append, erase_map_rm]; rfl)
        (.advances (V := vm V) m a (mem_map_rm.mpr h) hs)
  | _, _, Λ, _, .retires m s h a =>
      Stmt.nachΛ (by rw [erase_map_rm]; rfl) (.retires (V := vm V) m s (mem_map_rm.mpr h) a)
  | _, _, _, _, .ret e hΛ => .ret (renErg e) ((hΛ.map rm).trans (by rw [ende_map]))
  | _, _, _, _, .retGrund r hΛ => .retGrund r ((hΛ.map rm).trans (by rw [ende_map]))
  | _, _, _, _, .leave h => .leave h
  | _, _, _, _, .next h => .next h

/-- A block, translated. -/
def renB {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Block D.mitRuhe (vm V) l (Γ.map tyR) (Λ.map rm) (Λ'.map rm)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons s rest => .cons (renS s) (renB rest)
  | _, _, _, _, .bind e rest => .bind (renE e) (renB rest)
  | _, _, Λ, _, .bindCall f args he hp hr rest =>
      .bindCall (V := vm V) (some f) (renA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Block.vorΛ (nach_map f Λ) (renB rest))
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest =>
      .bindCallInd (V := vm V) (n := n + 1) (renE p) (renA args)
        (by show Option.map tyR (D.sigNr n).erg = _; rw [he]; rfl) (rufPasstR hp) hr
        (Block.vorΛ (nachSig_map (D.sigNr n) Λ) (renB rest))
  | _, _, Λ, _, .bindCallElse f args he hp hr err rest =>
      .bindCallElse (V := vm V) (some f) (renA args)
        (by show Option.map tyR (D.erg f) = _; rw [he]; rfl) (rufPasstR hp) hr
        (Endblock.umΛ (nach_map f Λ) (renEnd err)) (Block.vorΛ (nach_map f Λ) (renB rest))
  | _, _, _, _, .bindAxiom a args he hw hg hd hgd rest =>
      .bindAxiom (V := vm V) a (renA args)
        (by show Option.map tyR (D.aerg a) = _; rw [he]; rfl) hw hg
        (fun t ht => darfR (hd t ht)) (fun g hg' => gdarfR (hgd g hg')) (renB rest)
  | _, _, _, _, .regLies r hk rest => .regLies r hk (renB rest)
  | _, _, _, _, .regLiesElse r hk zusage sonst rest =>
      .regLiesElse r hk (renE zusage) (renEnd sonst) (renB rest)
  | _, _, _, _, .awaits g payload hp hL rest => .awaits g payload hp (gdarfR hL) (renB rest)
  | _, _, _, _, .exchange g neu hw hL rest => .exchange g (renE neu) hw (gdarfR hL) (renB rest)
  | _, _, _, _, .narrow e lo' hi' sonst rest => .narrow (renE e) lo' hi' (renEnd sonst) (renB rest)
  | _, _, _, _, .pruefung c sonst rest => .pruefung (renE c) (renEnd sonst) (renB rest)
  | _, _, _, _, .gleit op a b lo hi rest => .gleit op (renE a) (renE b) lo hi (renB rest)
  | _, _, _, _, .gleitLit q lo hi rest => .gleitLit q lo hi (renB rest)
  | _, _, _, _, .gleitVon e lo hi rest => .gleitVon (renE e) lo hi (renB rest)
  | _, _, _, _, .gleitNarrow e lo hi sonst rest =>
      .gleitNarrow (renE e) lo hi (renEnd sonst) (renB rest)

/-- An end block, translated. -/
def renEnd {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Endblock D.mitRuhe (vm V) l (Γ.map tyR) (Λ.map rm)
  | _, _, _, .ret e hΛ => .ret (renErg e) ((hΛ.map rm).trans (by rw [ende_map]))
  | _, _, _, .retGrund r hΛ => .retGrund r ((hΛ.map rm).trans (by rw [ende_map]))
  | _, _, _, .leave h => .leave h
  | _, _, _, .next h => .next h
  | _, _, _, .cons s rest => .cons (renS s) (renEnd rest)
  | _, _, _, .bind e rest => .bind (renE e) (renEnd rest)

/-- Arms, translated (the arm scope `ArmCtx` is split on the case). -/
def renArms {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs →
      Arms D.mitRuhe (vm V) l (Γ.map tyR) (Λ.map rm) (Λ'.map rm) cs
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons (c := none) b rest => .cons (c := none) (renB b) (renArms rest)
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest =>
      .cons (c := some (lo, hi)) (renB b) (renArms rest)

/-- Reason arms, translated. -/
def renGArms {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    GrundArms D V l Γ Λ Λ' n → GrundArms D.mitRuhe (vm V) l (Γ.map tyR) (Λ.map rm) (Λ'.map rm) n
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons b rest => .cons (renB b) (renGArms rest)

end

/-! ## 5. The program, the oracle, the lock invariants -/

/-- **`P` over `D.mitRuhe`**: every function `some f` is `f` translated;
    the idle root `none` has `requires true`, `ensures true`, body
    `return`. -/
def Programm.mitRuhe (P : Programm D) : Programm D.mitRuhe where
  invariante i := Expr.umΛ (invSicht_map (D := D) i) (renE (P.invariante i))
  requires
    | none => .wahr
    | some f => Expr.umΛ (anfang_map (D.signatur f)) (renE (P.requires f))
  ensures
    | none => .wahr
    | some f => Expr.umΓ (ergCtx_map (D.params f) (D.erg f))
        (Expr.umΛ (ende_map (vertragVon D f)) (renE (P.ensures f)))
  rumpf
    | none => .ret .keine List.Perm.nil
    | some f => Endblock.umΛ (anfang_map (D.signatur f)) (renEnd (P.rumpf f))

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

/-- **The lock invariants of `D.mitRuhe`**: the same carriers, `S.inv` on the
    translated-back memory. -/
def SperrInv.mitRuhe (S : SperrInv D) : SperrInv D.mitRuhe :=
  ⟨S.orte, fun L s => S.inv L (speicherZ s)⟩

end Gabbro.Grammatik
