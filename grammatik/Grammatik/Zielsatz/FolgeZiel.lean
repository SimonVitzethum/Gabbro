/-
  File:      Grammatik/Zielsatz/FolgeZiel.lean
  Subject:   THE ORDER LEG FOR THE USER'S OWN FUNCTIONS (Opus agent G, 2026-09-26, OFFEN O1).

  `GabbroZiel` speaks about `E.P.mitRuhe`, the program with the runtime's idle root `none`
  (MitRuhe.lean). An order specification the user writes is over `D`: `Φ.mitRuhe` lifts it
  (`none` in no set; signature `n` of `D` is `n + 1` of `D.mitRuhe`), and the check commutes
  with the translation of the bodies (`ruEnd_fE`, a structural induction over the syntax, the
  twin of `ruEnd_gOk`, MitRuheStatisch.lean). So `folgeOk_mitRuhe`: a program that passes the
  check for `Φ` passes it for `Φ.mitRuhe`, and `gabbro_ziel_folge` reads the leg `folge` of the
  goal statement off for every `Φ` over the user's own declaration: on every reachable thread
  machine every thread's call log is ordered by `Φ` -- the entries and returns of the user's
  functions, as `some f`.
-/
import Grammatik.Zielsatz.Beweis
import Grammatik.MitRuheStatisch

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- An order specification over `D`, lifted to `D.mitRuhe`: the idle root is in no set. -/
def Folge.mitRuhe (Φ : Folge D) : Folge D.mitRuhe where
  vor := fun g => match g with | none => false | some f => Φ.vor f
  ruf := fun g => match g with | none => false | some f => Φ.ruf f
  ind := fun n => match n with | 0 => false | n + 1 => Φ.ind n
  ende := fun g => match g with | none => false | some f => Φ.ende f

section Um

variable (Φ : Folge D) {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem fNach_nachΛ {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (w : Bool)
    (s : Stmt D V l Γ Λ Λ₁) : fNach Φ w (Stmt.nachΛ h s) = fNach Φ w s := by subst h; rfl
theorem fS_nachΛ {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (e w : Bool)
    (s : Stmt D V l Γ Λ Λ₁) : fS Φ e w (Stmt.nachΛ h s) = fS Φ e w s := by subst h; rfl
theorem fB_vorΛ {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂) (e w : Bool)
    (b : Block D V l Γ Λ₁ Λ') : fB Φ e w (Block.vorΛ h b) = fB Φ e w b := by subst h; rfl
theorem fE_umΛ {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (e w : Bool)
    (b : Endblock D V l Γ Λ₁) : fE Φ e w (Endblock.umΛ h b) = fE Φ e w b := by subst h; rfl

end Um

/-- The armed bit after a translated statement is the bit after the statement. -/
theorem ruS_fNach (Φ : Folge D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (w : Bool) : (s : Stmt D V l Γ Λ Λ') → fNach Φ.mitRuhe w (ruS s) = fNach Φ w s
  | .call .. => fNach_nachΛ _ _ _ _
  | .callInd .. => fNach_nachΛ _ _ _ _
  | .advances .. => fNach_nachΛ _ _ _ _
  | .retires .. => fNach_nachΛ _ _ _ _
  | .assignSlot .. => rfl
  | .assignDurch .. => rfl
  | .assignGlob .. => rfl
  | .schreibBytes .. => rfl
  | .assignVar .. => rfl
  | .uebergang .. => rfl
  | .ite .. => rfl
  | .onOption .. => rfl
  | .onTag .. => rfl
  | .onGrund .. => rfl
  | .locks .. => rfl
  | .breaking .. => rfl
  | .traverse .. => rfl
  | .retry .. => rfl
  | .forever .. => rfl
  | .axiomCall .. => rfl
  | .regSchreib .. => rfl
  | .transition .. => rfl
  | .publish .. => rfl
  | .ret .. => rfl
  | .retGrund .. => rfl
  | .leave _ => rfl
  | .next _ => rfl

mutual

theorem ruS_fS (Φ : Folge D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e w : Bool) (s : Stmt D V l Γ Λ Λ'), fS Φ.mitRuhe e w (ruS s) = fS Φ e w s
  | _, _, _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, _, _, .assignDurch .. => rfl
  | _, _, _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, _, _, .schreibBytes .. => rfl
  | _, _, _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, _, _, .uebergang .. => rfl
  | _, _, _, _, e, _, .ite _ t f =>
      kongr₂ (· && ·) (ruB_fB Φ e false t) (ruB_fB Φ e false f)
  | _, _, _, _, e, _, .onOption _ p a =>
      kongr₂ (· && ·) (ruB_fB Φ e false p) (ruB_fB Φ e false a)
  | _, _, _, _, e, _, .onTag _ arms => ruArms_fArms Φ e arms
  | _, _, _, _, e, _, .onGrund _ arms => ruGArms_fGArms Φ e arms
  | _, _, _, _, _, _, .call .. => fS_nachΛ _ _ _ _ _
  | _, _, _, _, _, _, .callInd .. => fS_nachΛ _ _ _ _ _
  | _, _, _, _, e, _, .locks _ _ body => ruB_fB Φ e false body
  | _, _, _, _, e, _, .breaking _ body => ruB_fB Φ e false body
  | _, _, _, _, e, _, .traverse _ _ body => ruB_fB Φ e false body
  | _, _, _, _, e, _, .retry _ _ body ueber =>
      kongr₂ (· && ·) (ruB_fB Φ e false body) (ruB_fB Φ e false ueber)
  | _, _, _, _, e, _, .forever _ _ body => ruB_fB Φ e false body
  | _, _, _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, _, _, .regSchreib .. => rfl
  | _, _, _, _, _, _, .transition .. => rfl
  | _, _, _, _, _, _, .publish .. => rfl
  | _, _, _, _, _, _, .advances .. => fS_nachΛ _ _ _ _ _
  | _, _, _, _, _, _, .retires .. => fS_nachΛ _ _ _ _ _
  | _, _, _, _, _, _, .ret .. => rfl
  | _, _, _, _, _, _, .retGrund .. => rfl
  | _, _, _, _, _, _, .leave _ => rfl
  | _, _, _, _, _, _, .next _ => rfl

theorem ruB_fB (Φ : Folge D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e w : Bool) (b : Block D V l Γ Λ Λ'), fB Φ.mitRuhe e w (ruB b) = fB Φ e w b
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, e, w, .cons s rest => by
      show (fS Φ.mitRuhe e w (ruS s) && fB Φ.mitRuhe e (fNach Φ.mitRuhe w (ruS s)) (ruB rest)) =
        (fS Φ e w s && fB Φ e (fNach Φ w s) rest)
      rw [ruS_fS Φ e w s, ruS_fNach Φ w s, ruB_fB Φ e _ rest]
  | _, _, _, _, e, w, .bind _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .bindCall g _ _ _ _ rest => by
      show ((!Φ.ruf g || w) && fB Φ.mitRuhe e (Φ.vor g) (Block.vorΛ _ (ruB rest))) = _
      rw [fB_vorΛ, ruB_fB Φ e _ rest]; rfl
  | _, _, _, _, e, w, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (fun x => (!Φ.ind n || w) && x)
        ((fB_vorΛ Φ.mitRuhe _ e false (ruB rest)).trans (ruB_fB Φ e false rest))
  | _, _, _, _, e, w, .bindCallElse g _ _ _ _ err rest => by
      show ((!Φ.ruf g || w) && fE Φ.mitRuhe e false (Endblock.umΛ _ (ruEnd err)) &&
        fB Φ.mitRuhe e (Φ.vor g) (Block.vorΛ _ (ruB rest))) = _
      rw [fE_umΛ, fB_vorΛ, ruEnd_fE Φ e _ err, ruB_fB Φ e _ rest]; rfl
  | _, _, _, _, e, w, .bindAxiom _ _ _ _ _ _ _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .regLies _ _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .regLiesElse _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_fE Φ e false sonst) (ruB_fB Φ e w rest)
  | _, _, _, _, e, w, .awaits _ _ _ _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .exchange _ _ _ _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .narrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_fE Φ e false sonst) (ruB_fB Φ e w rest)
  | _, _, _, _, e, w, .pruefung _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_fE Φ e false sonst) (ruB_fB Φ e w rest)
  | _, _, _, _, e, w, .gleit _ _ _ _ _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .gleitLit _ _ _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .gleitVon _ _ _ rest => ruB_fB Φ e w rest
  | _, _, _, _, e, w, .gleitNarrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_fE Φ e false sonst) (ruB_fB Φ e w rest)

theorem ruEnd_fE (Φ : Folge D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e w : Bool) (b : Endblock D V l Γ Λ), fE Φ.mitRuhe e w (ruEnd b) = fE Φ e w b
  | _, _, _, _, _, .ret .. => rfl
  | _, _, _, _, _, .retGrund .. => rfl
  | _, _, _, _, _, .leave _ => rfl
  | _, _, _, _, _, .next _ => rfl
  | _, _, _, e, w, .cons s rest => by
      show (fS Φ.mitRuhe e w (ruS s) && fE Φ.mitRuhe e (fNach Φ.mitRuhe w (ruS s)) (ruEnd rest)) =
        (fS Φ e w s && fE Φ e (fNach Φ w s) rest)
      rw [ruS_fS Φ e w s, ruS_fNach Φ w s, ruEnd_fE Φ e _ rest]
  | _, _, _, e, w, .bind _ rest => ruEnd_fE Φ e w rest

theorem ruArms_fArms (Φ : Folge D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (e : Bool)
    (arms : Arms D V l Γ Λ Λ' cs), fArms Φ.mitRuhe e (ruArms arms) = fArms Φ e arms
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, e, .cons (c := none) b rest =>
      kongr₂ (· && ·) (ruB_fB Φ e false b) (ruArms_fArms Φ e rest)
  | _, _, _, _, _, e, .cons (c := some (_, _)) b rest =>
      kongr₂ (· && ·) (ruB_fB Φ e false b) (ruArms_fArms Φ e rest)

theorem ruGArms_fGArms (Φ : Folge D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (e : Bool) (arms : GrundArms D V l Γ Λ Λ' n),
    fGArms Φ.mitRuhe e (ruGArms arms) = fGArms Φ e arms
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, e, .cons b rest =>
      kongr₂ (· && ·) (ruB_fB Φ e false b) (ruGArms_fGArms Φ e rest)

end

/-- **The check survives the idle root.** -/
theorem folgeOk_mitRuhe {P : Programm D} {Φ : Folge D} (h : FolgeOk P Φ) :
    FolgeOk P.mitRuhe Φ.mitRuhe := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · cases g with
    | none => rfl
    | some f =>
        exact (fE_umΛ Φ.mitRuhe (anfang_map (D.signatur f)) (Φ.ende f) false
          (ruEnd (P.rumpf f))).trans ((ruEnd_fE Φ _ _ _).trans (h.1 f))
  · cases g with
    | none => exact absurd hg Bool.false_ne_true
    | some f => exact h.2 f hg

namespace Zielsatz

/-- **THE ORDER LEG FOR THE USER'S OWN FUNCTIONS, READ OFF `GabbroZiel`.** Under the premises
    of the goal statement, for every order specification `Φ` over the user's declaration that
    the program passes, on every reachable thread machine every thread's call log is ordered by
    `Φ.mitRuhe`, and a finished thread started in an `ende` function ended directly behind a
    return of a `vor` function. -/
theorem gabbro_ziel_folge (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflicht E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe)
    (hK : FadenErreichbar E.P.mitRuhe O.mitRuhe passes (FadenStart E.P.mitRuhe sp init lebt0) K)
    (Φ : Folge D) (hΦ : FolgeOk E.P Φ) (t : Faden) :
    FolgeLog Φ.mitRuhe (K.m.faeden t).log ∧
    ((K.m.faeden t).stapel = [] → (K.m.faeden t).kopf.rest.2.2.2.2.anRueck = true →
      Φ.mitRuhe.ende (K.m.faeden t).kopf.f = true → Armiert Φ.mitRuhe (K.m.faeden t).log = true) :=
  (gabbro_ziel C D E fs ls cs hC hN O hH passes sp init hL lebt0 K hK).g.folge Φ.mitRuhe
    (folgeOk_mitRuhe hΦ) t

end Zielsatz

#print axioms Gabbro.Grammatik.folgeOk_mitRuhe
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_folge

end Gabbro.Grammatik
