import Grammatik.Zielsatz.Kern.Spec

/-!
  File:      Grammatik/Zielsatz/Einbettung/Einbettung.lean
  Subject:   EMBEDDING A DECLARATION INTO A LARGER ONE (`BUILD-SYSTEM.md` §7.10, stage E0).

  A project is proved over its OWN declaration `D`: its tables, globals, locks, marks, functions,
  invariants, axioms, registers and assumptions, and the heads it imports. A program that links
  it has a larger declaration `D'`. `Einbettung D D'` says how `D` sits in `D'`: an injection of
  every sort with its partial inverse, a bijection of the fields of every table, and the
  preservation of every attribute the semantics or the checker reads of an item of `D`. The
  table and signature NUMBERS map injectively (`tnum`, `num`), so a type of `D` translates to a
  type of `D'` (`tyN`: only `fnptr`, `ptr` and `ref` change their number) and the program keeps
  free numbers for its own signatures and tables.

  A diamond of projects is two embeddings into one `D'`; no quotient is needed.

  * `Einbettung` -- the structure; `Einbettung.id` -- the identity (it is inhabited).
  * `valE`, `ergE` -- values; `resE` -- held resources; `sigE` -- signatures; `vertragE` -- contracts.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

/-- **A type under the number maps**: signature numbers by `sn`, table numbers by `tn`. -/
@[reducible] def tyN (sn tn : Nat → Nat) : Ty → Ty
  | .int lo hi => .int lo hi
  | .bool => .bool
  | .opt n => .opt n
  | .sum cs => .sum cs
  | .why n => .why n
  | .never => .never
  | .fl lo hi => .fl lo hi
  | .fnptr n => .fnptr (sn n)
  | .ptr t rw => .ptr (tn t) rw
  | .ref t => .ref (tn t)
  | .arr τ n => .arr (tyN sn tn τ) n
  | .str n => .str n

/-- Under the identity maps a type is itself. -/
theorem tyN_id : ∀ τ : Ty, tyN (fun n => n) (fun n => n) τ = τ
  | .int _ _ | .bool | .opt _ | .sum _ | .why _ | .never | .fl _ _ | .fnptr _ | .ptr _ _ | .ref _ | .str _ => rfl
  | .arr τ n => by simp only [tyN, tyN_id τ]

/-- **`D` inside `D'`.** -/
structure Einbettung (D D' : Deklaration) where
  -- the numbers: signature numbers (`fnptr`) and table numbers (`ptr`, `ref`)
  num : Nat → Nat
  num_inj : ∀ a b, num a = num b → a = b
  tnum : Nat → Nat
  tnum_inj : ∀ a b, tnum a = tnum b → a = b
  -- tables, and the fields of each
  tab : D.Tab → D'.Tab
  tabZ : D'.Tab → Option D.Tab
  tabZ_tab : ∀ t, tabZ (tab t) = some t
  tab_tabZ : ∀ t' t, tabZ t' = some t → tab t = t'
  feld : ∀ t, D.Feld t → D'.Feld (tab t)
  feldZ : ∀ t, D'.Feld (tab t) → D.Feld t
  feldZ_feld : ∀ t f, feldZ t (feld t f) = f
  feld_feldZ : ∀ t f, feld t (feldZ t f) = f
  count : ∀ t, D'.count (tab t) = D.count t
  offen : ∀ t, D'.offen (tab t) = D.offen t
  typ : ∀ t f, D'.typ (tab t) (feld t f) = tyN num tnum (D.typ t f)
  erlaubt : ∀ t f, D'.erlaubt (tab t) (feld t f) = D.erlaubt t f
  geteilt : ∀ t, D'.geteilt (tab t) = D.geteilt t
  geist : ∀ t, D'.geist (tab t) = D.geist t
  -- globals
  glob : D.Glob → D'.Glob
  globZ : D'.Glob → Option D.Glob
  globZ_glob : ∀ g, globZ (glob g) = some g
  glob_globZ : ∀ g' g, globZ g' = some g → glob g = g'
  gtyp : ∀ g, D'.gtyp (glob g) = tyN num tnum (D.gtyp g)
  nutzlast : ∀ g, D'.nutzlast (glob g) = (D.nutzlast g).map glob
  atomar : ∀ g, D'.atomar (glob g) = D.atomar g
  ggeteilt : ∀ g, D'.ggeteilt (glob g) = D.ggeteilt g
  ggeist : ∀ g, D'.ggeist (glob g) = D.ggeist g
  -- locks and marks, and what a carrier needs of them
  lock : D.Lock → D'.Lock
  lockZ : D'.Lock → Option D.Lock
  lockZ_lock : ∀ L, lockZ (lock L) = some L
  lock_lockZ : ∀ L' L, lockZ L' = some L → lock L = L'
  rang : ∀ L, D'.rang (lock L) = D.rang L
  maskiert : ∀ L, D'.maskiert (lock L) = D.maskiert L
  marke : D.Marke → D'.Marke
  markeZ : D'.Marke → Option D.Marke
  markeZ_marke : ∀ m, markeZ (marke m) = some m
  marke_markeZ : ∀ m' m, markeZ m' = some m → marke m = m'
  stufen : ∀ m, D'.stufen (marke m) = D.stufen m
  braucht : ∀ t, D'.braucht (tab t) = (D.braucht t).map (Sum.map lock (Prod.map marke id))
  gbraucht : ∀ g, D'.gbraucht (glob g) = (D.gbraucht g).map (Sum.map lock (Prod.map marke id))
  eigner : ∀ t, D'.eigner (tab t) = (D.eigner t).map marke
  -- functions: the project's own and the heads it imports
  fn : D.Fn → D'.Fn
  fnZ : D'.Fn → Option D.Fn
  fnZ_fn : ∀ f, fnZ (fn f) = some f
  fn_fnZ : ∀ f' f, fnZ f' = some f → fn f = f'
  -- invariants
  inv : D.Inv → D'.Inv
  invZ : D'.Inv → Option D.Inv
  invZ_inv : ∀ i, invZ (inv i) = some i
  inv_invZ : ∀ i' i, invZ i' = some i → inv i = i'
  traeger : ∀ i, D'.traeger (inv i) = (D.traeger i).map tab
  invs : ∀ i, inv i ∈ D'.invs ↔ i ∈ D.invs
  -- axioms (foreign bodies): their frames stay inside the image
  ax : D.Ax → D'.Ax
  axZ : D'.Ax → Option D.Ax
  axZ_ax : ∀ a, axZ (ax a) = some a
  ax_axZ : ∀ a' a, axZ a' = some a → ax a = a'
  aparams : ∀ a, D'.aparams (ax a) = (D.aparams a).map (tyN num tnum)
  aerg : ∀ a, D'.aerg (ax a) = (D.aerg a).map (tyN num tnum)
  agruende : ∀ a, D'.agruende (ax a) = D.agruende a
  aschreibt : ∀ a t', D'.aschreibt (ax a) t' = (match tabZ t' with | some t => D.aschreibt a t | none => false)
  agschreibt : ∀ a g', D'.agschreibt (ax a) g' =
    (match globZ g' with | some g => D.agschreibt a g | none => false)
  anbieter : ∀ t, D'.anbieter (tab t) = (D.anbieter t).map ax
  -- registers
  reg : D.Reg → D'.Reg
  regZ : D'.Reg → Option D.Reg
  regZ_reg : ∀ r, regZ (reg r) = some r
  reg_regZ : ∀ r' r, regZ r' = some r → reg r = r'
  rtyp : ∀ r, D'.rtyp (reg r) = tyN num tnum (D.rtyp r)
  rklasse : ∀ r, D'.rklasse (reg r) = D.rklasse r
  spiegel : ∀ r, D'.spiegel (reg r) = (D.spiegel r).map reg
  rtraeger : ∀ r, D'.rtraeger (reg r) = (D.rtraeger r).map (Sum.map tab glob)
  -- assumptions
  annahme : D.Annahme → D'.Annahme
  a10 : annahme D.a10 = D'.a10
  -- a table number names the image of its table
  tabNr : ∀ n, D'.tabNr (tnum n) = (D.tabNr n).map tab
  -- conformance (the signatures themselves need `sigE`, below: `SigTreu`)
  sig : ∀ f, D'.sig (fn f) = num (D.sig f)
  passt : ∀ f n, D'.passt (fn f) (num n) = D.passt f n

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

/-! ## Values, resources, signatures, contracts -/

/-- A type of `D` as a type of `D'`. -/
@[reducible] def tyE (τ : Ty) : Ty := tyN E.num E.tnum τ

/-- A value of `D` as a value of the translated type: only a function pointer moves. -/
def valE : (τ : Ty) → Wert D τ → Wert D' (E.tyE τ)
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum _, v => v
  | .why _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr _, v => ⟨E.fn v.1, (E.passt v.1 _).trans v.2⟩
  | .ptr _ _, v => v
  | .ref _, v => v
  | .arr τ _, v => fun j => valE τ (v j)
  | .str _, v => v

/-- A result value. -/
def ergE : (e : Option Ty) → ErgVal D e → ErgVal D' (e.map E.tyE)
  | none, v => v
  | some τ, v => E.valE τ v

/-- A held resource. -/
def resE : Res D → Res D'
  | .held L => .held (E.lock L)
  | .marke m s => .marke (E.marke m) s

/-- A carrier. -/
def ortE : D.Tab ⊕ D.Glob → D'.Tab ⊕ D'.Glob := Sum.map E.tab E.glob

/-- A signature: types translated, writes are the image's, locks and marks mapped. -/
def sigE (S : Signatur D.Tab D.Glob D.Lock D.Marke) : Signatur D'.Tab D'.Glob D'.Lock D'.Marke where
  params := S.params.map E.tyE
  erg := S.erg.map E.tyE
  gruende := S.gruende
  haelt := S.haelt.map E.lock
  schreibt := fun t' => match E.tabZ t' with | some t => S.schreibt t | none => false
  gschreibt := fun g' => match E.globZ g' with | some g => S.gschreibt g | none => false
  konsumiert := S.konsumiert.map (Prod.map E.marke id)
  produziert := S.produziert.map (Prod.map E.marke id)
  boden := S.boden

/-- A contract. -/
def vertragE (V : Vertrag D) : Vertrag D' where
  schreibt := fun t' => match E.tabZ t' with | some t => V.schreibt t | none => false
  gschreibt := fun g' => match E.globZ g' with | some g => V.gschreibt g | none => false
  erg := V.erg.map E.tyE
  gruende := V.gruende
  haelt := V.haelt.map E.lock
  produziert := V.produziert.map (Prod.map E.marke id)
  boden := V.boden

theorem vertragE_vonSig (S : Signatur D.Tab D.Glob D.Lock D.Marke) :
    E.vertragE (Vertrag.vonSig D S) = Vertrag.vonSig D' (E.sigE S) := rfl

theorem resE_von (w : D.Lock ⊕ (D.Marke × Nat)) :
    E.resE (Res.von D w) = Res.von D' (Sum.map E.lock (Prod.map E.marke id) w) := by
  rcases w with L | ⟨m, s⟩ <;> rfl

theorem resE_inj {a b : Res D} (h : E.resE a = E.resE b) : a = b := by
  have hl : Function.Injective E.lock := fun x y h => by
    have := congrArg E.lockZ h
    rw [E.lockZ_lock, E.lockZ_lock] at this
    exact Option.some.inj this
  have hm : Function.Injective E.marke := fun x y h => by
    have := congrArg E.markeZ h
    rw [E.markeZ_marke, E.markeZ_marke] at this
    exact Option.some.inj this
  cases a <;> cases b <;> simp only [resE, Res.held.injEq, Res.marke.injEq, reduceCtorEq] at h ⊢
  · exact hl h
  · exact ⟨hm h.1, h.2⟩

end Einbettung

/-- **The signatures agree**: every signature number of `D` names, under `num`, the mapped
    signature in `D'` (so a function's own signature and every pointer signature carry over), and a
    register's promise is the same about the same value. Stated beside the structure because it
    needs `sigE` and `valE`. -/
structure Einbettung.SigTreu (E : Einbettung D D') : Prop where
  sigNr : ∀ n, D'.sigNr (E.num n) = E.sigE (D.sigNr n)
  rzusage : ∀ r (v : Wert D (D.rtyp r)),
    D'.rzusage (E.reg r) ((E.rtyp r).symm ▸ E.valE (D.rtyp r) v) = D.rzusage r v

theorem Einbettung.SigTreu.signatur {E : Einbettung D D'} (h : E.SigTreu) (f : D.Fn) :
    D'.signatur (E.fn f) = E.sigE (D.signatur f) := by
  unfold Deklaration.signatur
  rw [E.sig, h.sigNr]

/-! ## The identity: every declaration embeds into itself -/

/-- The identity embedding. -/
def Einbettung.id (D : Deklaration) : Einbettung D D where
  num := fun n => n
  num_inj := fun _ _ h => h
  tnum := fun n => n
  tnum_inj := fun _ _ h => h
  tab := fun t => t
  tabZ := some
  tabZ_tab := fun _ => rfl
  tab_tabZ := fun _ _ h => (Option.some.inj h).symm
  feld := fun _ f => f
  feldZ := fun _ f => f
  feldZ_feld := fun _ _ => rfl
  feld_feldZ := fun _ _ => rfl
  count := fun _ => rfl
  offen := fun _ => rfl
  typ := fun t f => (tyN_id _).symm
  erlaubt := fun _ _ => rfl
  geteilt := fun _ => rfl
  geist := fun _ => rfl
  glob := fun g => g
  globZ := some
  globZ_glob := fun _ => rfl
  glob_globZ := fun _ _ h => (Option.some.inj h).symm
  gtyp := fun g => (tyN_id _).symm
  nutzlast := fun _ => by simp
  atomar := fun _ => rfl
  ggeteilt := fun _ => rfl
  ggeist := fun _ => rfl
  lock := fun L => L
  lockZ := some
  lockZ_lock := fun _ => rfl
  lock_lockZ := fun _ _ h => (Option.some.inj h).symm
  rang := fun _ => rfl
  maskiert := fun _ => rfl
  marke := fun m => m
  markeZ := some
  markeZ_marke := fun _ => rfl
  marke_markeZ := fun _ _ h => (Option.some.inj h).symm
  stufen := fun _ => rfl
  braucht := fun t => by
    conv => lhs; rw [← List.map_id (D.braucht t)]
    congr 1
    funext w
    rcases w with L | ⟨m, s⟩ <;> rfl
  gbraucht := fun g => by
    conv => lhs; rw [← List.map_id (D.gbraucht g)]
    congr 1
    funext w
    rcases w with L | ⟨m, s⟩ <;> rfl
  eigner := fun _ => by simp
  fn := fun f => f
  fnZ := some
  fnZ_fn := fun _ => rfl
  fn_fnZ := fun _ _ h => (Option.some.inj h).symm
  inv := fun i => i
  invZ := some
  invZ_inv := fun _ => rfl
  inv_invZ := fun _ _ h => (Option.some.inj h).symm
  traeger := fun _ => by simp
  invs := fun _ => Iff.rfl
  ax := fun a => a
  axZ := some
  axZ_ax := fun _ => rfl
  ax_axZ := fun _ _ h => (Option.some.inj h).symm
  aparams := fun a => by
    conv => lhs; rw [← List.map_id (D.aparams a)]
    congr 1
    funext τ
    exact (tyN_id τ).symm
  aerg := fun a => by cases D.aerg a with
    | none => rfl
    | some τ => exact congrArg some (tyN_id τ).symm
  agruende := fun _ => rfl
  aschreibt := fun _ _ => rfl
  agschreibt := fun _ _ => rfl
  anbieter := fun _ => by simp
  reg := fun r => r
  regZ := some
  regZ_reg := fun _ => rfl
  reg_regZ := fun _ _ h => (Option.some.inj h).symm
  rtyp := fun r => (tyN_id _).symm
  rklasse := fun _ => rfl
  spiegel := fun _ => by simp
  rtraeger := fun r => by
    conv => lhs; rw [← List.map_id (D.rtraeger r)]
    congr 1
    funext c
    rcases c with t | g <;> rfl
  annahme := fun a => a
  a10 := rfl
  tabNr := fun n => by simp
  sig := fun _ => rfl
  passt := fun _ _ => rfl

end Gabbro.Grammatik.Einbettung
