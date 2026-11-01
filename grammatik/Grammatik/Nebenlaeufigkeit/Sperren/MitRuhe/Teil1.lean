module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. Types, signatures, the declaration -/

/-- Types of `D.mitRuhe`: function-pointer numbers shift by one. -/
@[reducible] def tyR : Ty → Ty
  | .int lo hi => .int lo hi
  | .bool => .bool
  | .opt n => .opt n
  | .sum cs => .sum cs
  | .why n => .why n
  | .never => .never
  | .fl lo hi => .fl lo hi
  | .fnptr n => .fnptr (n + 1)
  | .ptr t rw => .ptr t rw
  | .ref t => .ref t
  | .arr τ n => .arr (tyR τ) n
  | .str n => .str n

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

/-- Conformance in `D.mitRuhe`: `some f` to `n + 1` as `f` to `n`; the root only to `0`. -/
def passtM (D : Deklaration) : Option D.Fn → Nat → Bool
  | some f, n + 1 => D.passt f n
  | some _, 0 => false
  | none, n => decide (n = 0)

/-- Shifting the types keeps conformance. -/
theorem SigPasst.sigR {Tab Glob Lock Marke : Type} {rang : Lock → Int} {S T : Signatur Tab Glob Lock Marke}
    (h : SigPasst rang S T) : SigPasst rang (sigR S) (sigR T) :=
  ⟨congrArg (List.map tyR) h.params, congrArg (Option.map tyR) h.erg, h.gruende, h.schreibt, h.gschreibt,
    h.konsumiert, h.produziert, h.haelt, h.extra, h.boden⟩

theorem passtM_ok (D : Deklaration) : ∀ f n, passtM D f n = true →
    SigPasst D.rang (sigNrM D (sigM D f)) (sigNrM D n)
  | some f, n + 1, h => SigPasst.sigR (D.passt_ok f n h)
  | some _, 0, h => by simp only [passtM, Bool.false_eq_true] at h
  | none, n, h => by
    have : n = 0 := of_decide_eq_true h
    subst this; exact SigPasst.refl _ _

/-- A value of `τ` as a value of the shifted `τ`. -/
@[reducible] def valR : (τ : Ty) → Val D.Fn D.passt τ → Val (Option D.Fn) (passtM D) (tyR τ)
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum _, v => v
  | .why _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr _, v => ⟨some v.1, v.2⟩
  | .ptr _ _, v => v
  | .ref _, v => v
  | .arr τ _, v => fun j => valR τ (v j)
  | .str _, v => v

/-- A value of the shifted `τ` as a value of `τ` (the root has number `0`,
    which no shifted pointer type names). -/
def valZ : (τ : Ty) → Val (Option D.Fn) (passtM D) (tyR τ) → Val D.Fn D.passt τ
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum _, v => v
  | .why _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr n, v => match v with
    | ⟨some f, h⟩ => ⟨f, h⟩
    | ⟨none, h⟩ => absurd h (by simp only [passtM, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, decide_false, Bool.false_eq_true,
  not_false_eq_true])
  | .ptr _ _, v => v
  | .ref _, v => v
  | .arr τ _, v => fun j => valZ τ (v j)
  | .str _, v => v

theorem valZ_valR : ∀ (τ : Ty) (v : Val D.Fn D.passt τ), valZ τ (valR τ v) = v
  | .int _ _, _ => rfl
  | .bool, _ => rfl
  | .opt _, _ => rfl
  | .sum _, _ => rfl
  | .why _, _ => rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr _, ⟨_, _⟩ => rfl
  | .ptr _ _, _ => rfl
  | .ref _, _ => rfl
  | .arr τ _, v => funext fun j => valZ_valR τ (v j)
  | .str _, _ => rfl

theorem valR_valZ : ∀ (τ : Ty) (v : Val (Option D.Fn) (passtM D) (tyR τ)), valR τ (valZ τ v) = v
  | .int _ _, _ => rfl
  | .bool, _ => rfl
  | .opt _, _ => rfl
  | .sum _, _ => rfl
  | .why _, _ => rfl
  | .never, _ => rfl
  | .fl _ _, _ => rfl
  | .fnptr n, ⟨some f, h⟩ => rfl
  | .fnptr n, ⟨none, h⟩ => absurd h (by simp only [passtM, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, decide_false, Bool.false_eq_true,
  not_false_eq_true])
  | .ptr _ _, _ => rfl
  | .ref _, _ => rfl
  | .arr τ _, v => funext fun j => valR_valZ τ (v j)
  | .str _, _ => rfl

/-- **`D` plus the runtime's idle root.** Every carrier, lock, mark,
    invariant, axiom and register is `D`'s; field, global, axiom and
    register types are shifted (`tyR`); the functions are `some f` and the
    root `none`. -/
@[reducible] def Deklaration.mitRuhe (D : Deklaration) : Deklaration where
  Tab := D.Tab
  decTab := D.decTab
  count := D.count
  offen := D.offen
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
  passt := passtM D
  passt_ok := passtM_ok D
  eigner_nie_erzeugt := fun n t m s hm => match n with
    | 0 => by simp only [sigNrM, sigRuheM, List.not_mem_nil, not_false_eq_true]
    | n + 1 => D.eigner_nie_erzeugt n t m s hm
  Inv := D.Inv
  traeger := D.traeger
  invs := D.invs
  Ax := D.Ax
  aparams := fun a => (D.aparams a).map tyR
  aerg := fun a => (D.aerg a).map tyR
  aschreibt := D.aschreibt
  agschreibt := D.agschreibt
  agruende := D.agruende
  anbieter := D.anbieter
  anbieter_passt := fun t a h => by
    obtain ⟨h1, h2, n, h3, h4⟩ := D.anbieter_passt t a h
    exact ⟨h1, by simp only [h2, List.map_nil], n, by simp only [h3, Option.map_some, tyR], h4⟩
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
    | 0 => by simp only [sigNrM, sigRuheM, List.any_eq_true, Bool.false_eq_true, and_false, exists_false] at h
    | n + 1 => D.invarianten_gehalten n i h t ht L hL
  ggeteilt_bewacht := D.ggeteilt_bewacht
  geist := D.geist
  ggeist := D.ggeist

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
  | .fremd q => .fremd q

/-- An event of `D.mitRuhe` as an event of `D`. -/
def evZ : Ereignis D.mitRuhe → Ereignis D
  | .zugriff t w Λ h => .zugriff t w (Λ.map resZ) h
  | .gzugriff g w Λ h => .gzugriff g w (Λ.map resZ) h
  | .nimmt L h => .nimmt L h
  | .gibt L => .gibt L
  | .fremd q => .fremd q

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
        simp only [List.erase_cons_head, List.map_cons]
      · have h' : resR b ≠ resR a := fun e => h (rm_inj e)
        simp only [beq_iff_eq, h, not_false_eq_true, List.erase_cons_tail, List.map_cons, ih, h']

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
  | _, _, .here => .here
  | _, _, .there x => .there (varR x)

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

end Gabbro.Grammatik
