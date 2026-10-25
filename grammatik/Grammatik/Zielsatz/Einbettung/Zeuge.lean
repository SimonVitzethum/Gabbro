import Grammatik.Zielsatz.Einbettung.Uebertragung

/-!
  File:      Grammatik/Zielsatz/Einbettung/Zeuge.lean
  Subject:   **Every library links into a program with a callback** -- the witnesses of the
             embedding theorem, for every library and no particular program.

  For every declaration `D` and every function `g₀` of it, `erweitert D g₀` is `D` with one more
  function outside `D` (`Sum.inr ()`): it has `g₀`'s signature and conforms to every pointer type
  `g₀` conforms to, so it can be handed to `D` as a callback with `g₀` as its head. Everything else
  is `D`'s. `einE` embeds `D`, `programmE` extends a program of `D` by the callback, whose body and
  contract are the images of `g₀`'s. `uebernahmeE` proves every link condition, `RueckVertrag`
  included, for every library; `einbettung_zeuge` is `logikPflicht_E` on it, with the callback real
  (`rueckruf_echt`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable (D : Deklaration) (g₀ : D.Fn)

/-- Conformance in the extension: a function of `D` as in `D`, the callback where `g₀` conforms. -/
def passtE : D.Fn ⊕ Unit → Nat → Bool
  | .inl f, n => D.passt f n
  | .inr _, n => D.passt g₀ n

/-- A value of the extension back in `D`: the callback stands for `g₀`. -/
def zurueck : (τ : Ty) → Val (D.Fn ⊕ Unit) (passtE D g₀) τ → Wert D τ
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum _, v => v
  | .why _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr _, ⟨.inl f, h⟩ => ⟨f, h⟩
  | .fnptr _, ⟨.inr _, h⟩ => ⟨g₀, h⟩
  | .ptr _ _, v => v
  | .ref _, v => v

/-- **The extension**: `D` and one callback outside it. -/
def erweitert : Deklaration where
  Tab := D.Tab
  decTab := D.decTab
  count := D.count
  offen := D.offen
  Feld := D.Feld
  decFeld := D.decFeld
  typ := D.typ
  erlaubt := D.erlaubt
  tabNr := D.tabNr
  Glob := D.Glob
  decGlob := D.decGlob
  gtyp := D.gtyp
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
  Fn := D.Fn ⊕ Unit
  sig := fun f => match f with | .inl f => D.sig f | .inr _ => D.sig g₀
  sigNr := D.sigNr
  passt := passtE D g₀
  passt_ok := fun f n h => by
    cases f with
    | inl f => exact D.passt_ok f n h
    | inr _ => exact D.passt_ok g₀ n h
  eigner_nie_erzeugt := D.eigner_nie_erzeugt
  Inv := D.Inv
  traeger := D.traeger
  invs := D.invs
  Ax := D.Ax
  aparams := D.aparams
  aerg := D.aerg
  aschreibt := D.aschreibt
  agschreibt := D.agschreibt
  agruende := D.agruende
  anbieter := D.anbieter
  anbieter_passt := D.anbieter_passt
  Reg := D.Reg
  rtyp := D.rtyp
  rklasse := D.rklasse
  spiegel := D.spiegel
  rzusage := fun r v => D.rzusage r (zurueck D g₀ (D.rtyp r) v)
  rtraeger := D.rtraeger
  Annahme := D.Annahme
  a10 := D.a10
  geteilt_bewacht := D.geteilt_bewacht
  invarianten_gehalten := D.invarianten_gehalten
  ggeteilt_bewacht := D.ggeteilt_bewacht
  geist := D.geist
  ggeist := D.ggeist

theorem tyN_id (τ : Ty) : tyN (fun n => n) (fun n => n) τ = τ := by cases τ <;> rfl

/-- **`D` inside its extension.** -/
def einE : Einbettung D (erweitert D g₀) where
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
  typ := fun t f => (tyN_id (D.typ t f)).symm
  erlaubt := fun _ _ => rfl
  geteilt := fun _ => rfl
  geist := fun _ => rfl
  glob := fun g => g
  globZ := some
  globZ_glob := fun _ => rfl
  glob_globZ := fun _ _ h => (Option.some.inj h).symm
  gtyp := fun g => (tyN_id (D.gtyp g)).symm
  nutzlast := fun _ => by simp [erweitert]
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
    show D.braucht t = _
    conv => lhs; rw [← List.map_id (D.braucht t)]
    congr 1
    funext w
    rcases w with L | ⟨m, s⟩ <;> rfl
  gbraucht := fun g => by
    show D.gbraucht g = _
    conv => lhs; rw [← List.map_id (D.gbraucht g)]
    congr 1
    funext w
    rcases w with L | ⟨m, s⟩ <;> rfl
  eigner := fun _ => by simp [erweitert]
  fn := Sum.inl
  fnZ := fun f => match f with | .inl f => some f | .inr _ => none
  fnZ_fn := fun _ => rfl
  fn_fnZ := fun f' f h => by
    cases f' with
    | inl f'' => exact congrArg Sum.inl (Option.some.inj h).symm
    | inr _ => cases h
  inv := fun i => i
  invZ := some
  invZ_inv := fun _ => rfl
  inv_invZ := fun _ _ h => (Option.some.inj h).symm
  traeger := fun _ => by simp [erweitert]
  invs := fun _ => Iff.rfl
  ax := fun a => a
  axZ := some
  axZ_ax := fun _ => rfl
  ax_axZ := fun _ _ h => (Option.some.inj h).symm
  aparams := fun a => by
    show D.aparams a = _
    conv => lhs; rw [← List.map_id (D.aparams a)]
    congr 1
    funext τ
    exact (tyN_id τ).symm
  aerg := fun a => by
    show D.aerg a = _
    cases D.aerg a with
    | none => rfl
    | some τ => exact congrArg some (tyN_id τ).symm
  agruende := fun _ => rfl
  aschreibt := fun _ _ => rfl
  agschreibt := fun _ _ => rfl
  anbieter := fun _ => by simp [erweitert]
  reg := fun r => r
  regZ := some
  regZ_reg := fun _ => rfl
  reg_regZ := fun _ _ h => (Option.some.inj h).symm
  rtyp := fun r => (tyN_id (D.rtyp r)).symm
  rklasse := fun _ => rfl
  spiegel := fun _ => by simp [erweitert]
  rtraeger := fun r => by
    show D.rtraeger r = _
    conv => lhs; rw [← List.map_id (D.rtraeger r)]
    congr 1
    funext c
    rcases c with t | g <;> rfl
  annahme := fun a => a
  a10 := rfl
  tabNr := fun n => by simp [erweitert]
  sig := fun _ => rfl
  passt := fun _ _ => rfl

theorem map_prod_id {α β : Type} (l : List (α × β)) : l.map (Prod.map (fun m => m) id) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, ih]; cases x; rfl

theorem sigE_einE (S : Signatur D.Tab D.Glob D.Lock D.Marke) : (einE D g₀).sigE S = S := by
  cases S with
  | mk params erg gruende haelt schreibt gschreibt konsumiert produziert boden =>
    simp only [Einbettung.sigE]
    congr 1
    · conv => rhs; rw [← List.map_id params]
      congr 1; funext τ; exact tyN_id τ
    · cases erg with
      | none => rfl
      | some τ => exact congrArg some (tyN_id τ)
    · exact List.map_id' haelt
    · exact map_prod_id konsumiert
    · exact map_prod_id produziert

theorem zurueck_cast (τ : Ty) (h : (einE D g₀).tyE τ = τ) (v : Wert D τ) :
    zurueck D g₀ τ (h ▸ (einE D g₀).valE τ v) = v := by
  cases τ <;> rfl

theorem sigTreu_einE : (einE D g₀).SigTreu where
  sigNr := fun n => (sigE_einE D g₀ (D.sigNr n)).symm
  rzusage := fun r v => by
    exact congrArg (D.rzusage r) (zurueck_cast D g₀ (D.rtyp r) ((einE D g₀).rtyp r).symm v)

/-! ## The head, the program, what the link keeps -/

/-- **The head of the callback**: `g₀` for every signature `g₀` conforms to. -/
def rueckE (hA : Einbettung.AntwortFrei D) : (einE D g₀).Rueck where
  rep := fun n => if D.passt g₀ n = true then some g₀ else none
  rep_passt := fun n g h => by
    by_cases hp : D.passt g₀ n = true
    · simp only [hp, ite_true, Option.some.injEq] at h; subst h; exact hp
    · simp only [hp, ite_false, reduceCtorEq] at h
  voll := fun n f' h hz => by
    cases f' with
    | inl f => cases hz
    | inr _ =>
        have hp : D.passt g₀ n = true := h
        simp [hp]
  frei := hA

/-- **The program of the extension**: the images of `P`'s functions, and the callback with the
    image of `g₀`'s body and contract. -/
def programmE (P : Programm D) : Programm (erweitert D g₀) where
  invariante := fun i => (einE D g₀).invarianteE P i
  requires := fun f => match f with
    | .inl f => (einE D g₀).requiresE (sigTreu_einE D g₀) P f
    | .inr _ => (einE D g₀).requiresE (sigTreu_einE D g₀) P g₀
  ensures := fun f => match f with
    | .inl f => (einE D g₀).ensuresE (sigTreu_einE D g₀) P f
    | .inr _ => (einE D g₀).ensuresE (sigTreu_einE D g₀) P g₀
  rumpf := fun f => match f with
    | .inl f => (einE D g₀).rumpfE (sigTreu_einE D g₀) P f
    | .inr _ => (einE D g₀).rumpfE (sigTreu_einE D g₀) P g₀
  unterbricht := fun f => match f with
    | .inl f => P.unterbricht f
    | .inr _ => false

theorem fort_einE (P : Programm D) :
    (einE D g₀).Fortsetzung (sigTreu_einE D g₀) P (programmE D g₀ P) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable (hA : Einbettung.AntwortFrei D)

/-- The lock invariants of the extension: `S`'s, on the restricted memory. -/
def sperrE (S : SperrInv D) : SperrInv (erweitert D g₀) :=
  ⟨fun L => (S.orte L).map (einE D g₀).ortE, fun L s' => S.inv L ((einE D g₀).speicherZ (rueckE D g₀ hA) s')⟩

/-- The axiom ensures of the extension: `Q`'s, on the restricted answer. -/
def axE (Q : AxEns D) : AxEns (erweitert D g₀) := fun a W' v' =>
  Q a (((einE D g₀).speicherZ (rueckE D g₀ hA) W'.speicher).welt [])
    ((einE D g₀).ergZ (rueckE D g₀ hA) (D.aerg a) (castV ((einE D g₀).aerg a) v'))

theorem castV_rund {D₀ : Deklaration} {a b : Option Ty} (h : a = b) (h' : b = a) (v : ErgVal D₀ a) :
    castV h' (castV h v) = v := by subst h; rfl

theorem ergZ_ergE (K : (einE D g₀).Rueck) : ∀ (e : Option Ty) (v : ErgVal D e),
    (einE D g₀).ergZ K e ((einE D g₀).ergE e v) = v
  | none, _ => rfl
  | some τ, v => (einE D g₀).valZ_vrel K τ ((einE D g₀).vrel_valE K τ v)

/-- **What the link keeps**, for every program, lock family, axiom ensures and atomic rely. -/
theorem uebernahmeE (P : Programm D) (S : SperrInv D) (Q : AxEns D) (T : D.Tab ⊕ D.Glob → Prop)
    (T' : (erweitert D g₀).Tab ⊕ (erweitert D g₀).Glob → Prop)
    (hT : ∀ c, T' ((einE D g₀).ortE c) → T c) :
    (einE D g₀).Uebernahme (rueckE D g₀ hA) (sigTreu_einE D g₀) P S Q T (programmE D g₀ P)
      (sperrE D g₀ hA S) (axE D g₀ hA Q) T' where
  fort := fort_einE D g₀ P
  orte := fun _ => rfl
  inv := fun _ _ => rfl
  atom := hT
  ax := fun a W' v => by
    show Q a _ _ = _
    erw [castV_rund]
    exact congrArg _ (ergZ_ergE D g₀ (rueckE D g₀ hA) (D.aerg a) v)
  invBild := fun i' _ _ _ => ⟨i', rfl⟩
  rueck := fun pad n g f' hz hr hp => by
    cases f' with
    | inl f => cases hz
    | inr u =>
        have hg : g = g₀ := by
          by_cases hp0 : D.passt g₀ n = true
          · simp only [rueckE, hp0, ite_true, Option.some.injEq] at hr; exact hr.symm
          · simp only [rueckE, hp0, ite_false, reduceCtorEq] at hr
        subst g
        refine ⟨fun t ht => ht, fun x hx => hx, fun σ σ' ρ a' h hr' => ⟨?_, fun W v' he => ?_⟩⟩
        · exact (einE D g₀).req_E (rueckE D g₀ hA) (sigTreu_einE D g₀) (fort_einE D g₀ P) h g₀ ρ a' hr'
        · unfold EnsAmRueck at he ⊢
          exact ((einE D g₀).ens_E (rueckE D g₀ hA) (sigTreu_einE D g₀) (fort_einE D g₀ P) h
            ((einE D g₀).treu_antwortWelt (rueckE D g₀ hA) pad σ W) g₀ ρ a' hr' _ v'
            ((einE D g₀).ergRel_ergZ (rueckE D g₀ hA) _ _)).symm.trans he

/-! ## Locality carries over -/

theorem speicherZ_slots_einE {s s' : Speicher (erweitert D g₀)} {t : D.Tab} (h : s.slots t = s'.slots t) :
    ((einE D g₀).speicherZ (rueckE D g₀ hA) s).slots t = ((einE D g₀).speicherZ (rueckE D g₀ hA) s').slots t := by
  funext k f
  show (einE D g₀).valZ (rueckE D g₀ hA) _ (castW _ (s.slots t k f)) =
    (einE D g₀).valZ (rueckE D g₀ hA) _ (castW _ (s'.slots t k f))
  rw [h]

theorem speicherZ_globs_einE {s s' : Speicher (erweitert D g₀)} {g : D.Glob} (h : s.globs g = s'.globs g) :
    ((einE D g₀).speicherZ (rueckE D g₀ hA) s).globs g = ((einE D g₀).speicherZ (rueckE D g₀ hA) s').globs g := by
  show (einE D g₀).valZ (rueckE D g₀ hA) _ (castW _ (s.globs g)) =
    (einE D g₀).valZ (rueckE D g₀ hA) _ (castW _ (s'.globs g))
  rw [h]

/-- A lock invariant that reads only its carriers still does in the extension. -/
theorem sperrE_lokal {S : SperrInv D} (hSL : SperrInvLokal S) : SperrInvLokal (sperrE D g₀ hA S) := by
  intro L s s' h
  apply hSL L
  intro c hc
  have h' := h ((einE D g₀).ortE c) (List.mem_map_of_mem hc)
  cases c with
  | inl t => exact speicherZ_slots_einE D g₀ hA h'
  | inr g => exact speicherZ_globs_einE D g₀ hA h'

/-- An axiom ensures that reads only the axiom's frame still does in the extension. -/
theorem axE_lokal {Q : AxEns D} (hQL : AxEnsLokal Q) : AxEnsLokal (axE D g₀ hA Q) := by
  intro a σ σ' v h1 h2
  apply hQL a
  · intro t ht; exact speicherZ_slots_einE D g₀ hA (h1 t ht)
  · intro g hg; exact speicherZ_globs_einE D g₀ hA (h2 g hg)

/-! ## The witness -/

/-- **Every library with a neutral trace piece keeps its proof in the program that adds a callback,
    with nothing proved anew.** -/
theorem einbettung_zeuge {P : Programm D} {S : SperrInv D} {Q : AxEns D} {T : D.Tab ⊕ D.Glob → Prop}
    {pad : List (Ereignis D)} (hp : Einbettung.PadOk pad) (hL : LogikPflichtA P S Q T) :
    ∀ (passes : Nat) (f : D.Fn),
      KoerperGutSA (programmE D g₀ P) passes (axE D g₀ hA Q) (sperrE D g₀ hA S)
          (fun c => T (Sum.map (fun t => t) (fun g => g) c)) (.inl f) ∧
        InvGutSA (programmE D g₀ P) passes (axE D g₀ hA Q) (sperrE D g₀ hA S)
          (fun c => T (Sum.map (fun t => t) (fun g => g) c)) (.inl f) ∧
        InvGutGrundA (programmE D g₀ P) passes (axE D g₀ hA Q) (sperrE D g₀ hA S)
          (fun c => T (Sum.map (fun t => t) (fun g => g) c)) (.inl f) :=
  (einE D g₀).logikPflicht_E (rueckE D g₀ hA) (sigTreu_einE D g₀)
    (uebernahmeE D g₀ hA P S Q T _ (fun c h => by cases c <;> exact h)) hp hL

/-- **The callback is real**: outside the image of `D`, conforming wherever `g₀` conforms, with
    `g₀` as its head -- so `RueckVertrag` is used, not vacuous. -/
theorem rueckruf_echt (n : Nat) (h : D.passt g₀ n = true) :
    (einE D g₀).fnZ (.inr ()) = none ∧ (erweitert D g₀).passt (.inr ()) n = true ∧
      (rueckE D g₀ hA).rep n = some g₀ :=
  ⟨rfl, h, by simp [rueckE, h]⟩



#print axioms Gabbro.Grammatik.Einbettung.einbettung_zeuge
#print axioms Gabbro.Grammatik.Einbettung.rueckruf_echt
end Gabbro.Grammatik.Einbettung
