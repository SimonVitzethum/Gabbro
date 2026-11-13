module

public import Gabbro.Sicherheit.Ausdruck
public import Gabbro.Sicherheit.Anweisung.Teil1

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

mutual

/-- **Der Pruefer.** `erg` ist die erklaerte Antwortgestalt der Funktion, in der die
    Anweisung steht -- ein `return e` muss sie treffen. -/
def pruefe (P : Programm) (erg : Option Shape) : Umgebung → Stmt → Option Umgebung
  | Δ, .assign c i f e =>
      match schluss P.D (formen Δ) i, schluss P.D (formen Δ) e with
      | some (.intIn lo hi), some sh =>
          if 0 ≤ lo ∧ hi < P.D.count c ∧ passtIn sh (P.D.slot c f) then some Δ else none
      | _, _ => none
  | Δ, .assignField c f e =>
      match schluss P.D (formen Δ) e with
      | some sh => if passtIn sh (P.D.feld c f) then some Δ else none
      | none => none
  | Δ, .assignGlobal g e =>
      match schluss P.D (formen Δ) e with
      | some sh => if passtIn sh (P.D.global g) then some Δ else none
      | none => none
  | Δ, .bindName n e =>
      match schluss P.D (formen Δ) e with
      | some sh => binde Δ n (.form sh)
      | none => none
  | Δ, .ite c t e =>
      match schluss P.D (formen Δ) c, pruefeBlock P erg (verfeinere Δ c true) t,
        pruefeBlock P erg (verfeinere Δ c false) e with
      | some .bool, some Δt, some Δe => some (vereinige Δ Δt Δe)
      | _, _, _ => none
  | Δ, .onOption g bn onP onA =>
      match schluss P.D (formen Δ) g, binde Δ bn (.form .int) with
      | some .opt, some ΔP =>
          match pruefeBlock P erg ΔP onP, pruefeBlock P erg Δ onA with
          | some _, some _ => some Δ
          | _, _ => none
      | _, _ => none
  | Δ, .call f ps as pre =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S => if S.gruende = [] then some Δ else none
      | none => none
  | Δ, .bindCall n f ps as pre =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S =>
          match S.ergebnis with
          | some sh => if S.gruende = [] then binde Δ n (.form sh) else none
          | none => none
      | none => none
  | Δ, .bindCallElse n f ps as pre err onErr =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S =>
          if S.gruende = [] then none else
          if !endetMitAusgang P.sig onErr then none else
          match binde Δ err (.why S.gruende) with
          | some ΔE =>
              match pruefeBlock P erg ΔE onErr with
              | some _ =>
                  match S.ergebnis with
                  | some sh => binde Δ n (.form sh)
                  -- `fn f() or R` ohne Wert: die Bindung bekommt `absent`, also `.opt`.
                  | none => binde Δ n (.form .opt)
              | none => none
          | none => none
      | none => none
  | Δ, .onReason (.name g) arms =>
      match such Δ g with
      | some (.why cs) =>
          if alleGruendeHabenArm arms cs then pruefeArme P erg Δ arms else none
      | _ => none
  | _, .onReason _ _ => none
  | Δ, .onTag g arms =>
      match schluss P.D (formen Δ) g with
      | some (.sum cs) =>
          if namenEindeutig cs && alleFaelleHabenArm arms cs then pruefeTags P erg Δ cs arms
          else none
      | _ => none
  | Δ, .retCall f ps as pre =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S =>
          if gruendePassen S.gruende P.ruferR && antwortGestaltPasst erg S.ergebnis then some Δ else none
      | none => none
  | Δ, .loop id inv body =>
      match P.schleife id, schluss P.D (formen Δ) inv with
      | some ΔS, some .bool =>
          -- Der registrierte Sichtbereich ist genau der hier gueltige (U2).
          if ΔS = Δ then
            match pruefeBlock P erg Δ body with
            | some _ => some Δ
            | none => none
          else none
      | _, _ => none
  | Δ, .locked _ b => match pruefeBlock P erg Δ b with | some _ => some Δ | none => none
  | Δ, .breaking _ b => match pruefeBlock P erg Δ b with | some _ => some Δ | none => none
  | Δ, .publish a e _ =>
      match schluss P.D (formen Δ) e with
      | some sh => if passtIn sh (P.D.global a) then some Δ else none
      | none => none
  | Δ, .awaitLoad n a _ =>
      -- Ein `atomic` ohne erklaerte Gestalt kennt das Modell nicht: Absage.
      match P.D.global a with
      | some sh => binde Δ n (.form sh)
      | none => none
  | Δ, .exchangeWith n a e =>
      match schluss P.D (formen Δ) e, P.D.global a with
      | some sh, some za => if passt sh za then binde Δ n (.form za) else none
      | _, _ => none
  | Δ, .ret none => if erg = none then some Δ else none
  | Δ, .ret (some e) =>
      match schluss P.D (formen Δ) e, erg with
      | some sh, some z => if passt sh z then some Δ else none
      | _, _ => none
  | Δ, .exit => some Δ
  | Δ, .leave => some Δ
  -- Finite traversal is discharged by the source bridge's generic simulation.
  -- This independent Body shape checker has no iteration typing rule yet.
  | _, .forEach .. => none
  | _, .retry .. => none

def pruefeBlock (P : Programm) (erg : Option Shape) : Umgebung → List Stmt → Option Umgebung
  | Δ, [] => some Δ
  | Δ, a :: rest =>
      match pruefe P erg Δ a with
      | some Δ' => pruefeBlock P erg Δ' rest
      | none => none

def pruefeArme (P : Programm) (erg : Option Shape) (Δ : Umgebung) :
    List (String × List Stmt) → Option Umgebung
  | [] => some Δ
  | (_, b) :: rest =>
      match pruefeBlock P erg Δ b with
      | some _ => pruefeArme P erg Δ rest
      | none => none

/-- Jeder Arm nennt einen Fall des Typs, sein Binder passt zur Nutzlast des Falls, und sein
    Rumpf geht unter dem Binder durch. -/
def pruefeTags (P : Programm) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    List (String × Option String × List Stmt) → Option Umgebung
  | [] => some Δ
  | (t, bd, b) :: rest =>
      match suchFall cs t with
      | some pl =>
          match nutzlastGestalt pl with
          | some sh =>
              match bd with
              | some v =>
                  match binde Δ v (.form sh) with
                  | some Δ' =>
                      match pruefeBlock P erg Δ' b with
                      | some _ => pruefeTags P erg Δ cs rest
                      | none => none
                  | none => none
              | none => none
          | none =>
              match bd with
              | none =>
                  match pruefeBlock P erg Δ b with
                  | some _ => pruefeTags P erg Δ cs rest
                  | none => none
              | some _ => none
      | none => none

end

/-! ## 3. Die LOGIK-Stellen -- wo das Modell aus einem Grund stecken bleibt, den kein Pass
    tragen kann. Jeder Konstruktor ohne Rekursion nennt eine Klausel des Schreibers. -/

/-- Der Eintrittszustand eines Gerufenen. -/
def eintritt (s : State) (ps : List String) (vs : List Value) : State :=
  { world := s.world, local' := bindAll ps vs (fun _ => .absent) }

mutual

inductive LogikS (ρ : Env) : Stmt → State → Prop
  /-- `requires` des Gerufenen gilt nicht an der Rufstelle -- `ownRequires`. -/
  | ruf {f ps as pre s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.call f ps as pre) s
  | rufGebunden {n f ps as pre s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.bindCall n f ps as pre) s
  | rufSonst {n f ps as pre err onErr s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.bindCallElse n f ps as pre err onErr) s
  | rufZurueck {f ps as pre s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.retCall f ps as pre) s
  /-- Die `invariant` gilt beim Eintritt in die Schleife nicht -- `ownInvariant`. -/
  | invariante {id inv body s} :
      eval s inv ≠ some (.bool true) → LogikS ρ (.loop id inv body) s
  -- Die Weitergabe: die Stelle liegt in einem Unterblock.
  | dann {c t e s} : eval s c = some (.bool true) → LogikB ρ t s → LogikS ρ (.ite c t e) s
  | sonst {c t e s} : eval s c = some (.bool false) → LogikB ρ e s → LogikS ρ (.ite c t e) s
  | vorhanden {g bn onP onA s k} : eval s g = some (.present k) →
      LogikB ρ onP { s with local' := bindLocal s.local' bn (.int k) } →
      LogikS ρ (.onOption g bn onP onA) s
  | abwesend {g bn onP onA s} : eval s g = some .absent → LogikB ρ onA s →
      LogikS ρ (.onOption g bn onP onA) s
  | fehlerzweig {n f ps as pre err onErr s vs x} :
      evalAll s as = some vs → (ρ f (eintritt s ps vs)).2 = some (.reason x) →
      LogikB ρ onErr { world := (ρ f (eintritt s ps vs)).1.world,
                       local' := bindLocal s.local' err (.reason x) } →
      LogikS ρ (.bindCallElse n f ps as pre err onErr) s
  | grundArm {g arms s x} : eval s g = some (.reason x) → LogikA ρ arms x s →
      LogikS ρ (.onReason g arms) s
  | fallArm {g arms s x p} : eval s g = some (.tagged x p) → LogikT ρ arms x p s →
      LogikS ρ (.onTag g arms) s
  | gesperrt {l b s} : LogikB ρ b s → LogikS ρ (.locked l b) s
  | ausgesetzt {i b s} : LogikB ρ b s → LogikS ρ (.breaking i b) s

inductive LogikB (ρ : Env) : List Stmt → State → Prop
  | kopf {a rest s} : LogikS ρ a s → LogikB ρ (a :: rest) s
  | widen {a rest s s'} : step ρ a s = .running s' → LogikB ρ rest s' → LogikB ρ (a :: rest) s

inductive LogikA (ρ : Env) : List (String × List Stmt) → String → State → Prop
  | here {n b rest x s} : n = x → LogikB ρ b s → LogikA ρ ((n, b) :: rest) x s
  | there {n b rest x s} : n ≠ x → LogikA ρ rest x s → LogikA ρ ((n, b) :: rest) x s

inductive LogikT (ρ : Env) : List (String × Option String × List Stmt) → String → Option Int →
    State → Prop
  | hierMit {n v b rest x k s} : n = x →
      LogikB ρ b { s with local' := bindLocal s.local' v (.int k) } →
      LogikT ρ ((n, some v, b) :: rest) x (some k) s
  | hierOhne {n b rest x p s} : n = x → LogikB ρ b s → LogikT ρ ((n, none, b) :: rest) x p s
  | there {n bd b rest x p s} : n ≠ x → LogikT ρ rest x p s → LogikT ρ ((n, bd, b) :: rest) x p s

end

/-! ## 4. Die Praemissen ueber die UMGEBUNG -- (U1) und (U2) -/

/-- Die Welt, wie beide Haelften sie brauchen. -/
def Welt (D : Deklaration) (Γ : Typing) (σ : World) : Prop :=
  WF Γ σ ∧ KettenWohlgeformt D σ

/-- **(U5)** Kein erklaerter Gerufener divergiert. Der Fehlerzweig haelt einen Ruf, der
    nicht zurueckkehrt, nur ueber `endetMitAusgang` -- `step` aber kehrt von jedem Ruf
    zurueck. Ohne diese Klausel waere der Zweig im Modell erreichbar und die Fortsetzung
    liefe mit ungebundener Bindung; mit ihr ist der Satz fuer Programme, die einen
    divergierenden Gerufenen erklaeren, leer. Das ist Schuldigkeit, kein Befund: was
    faellig ist, ist ein `step`, das einen divergierenden Ruf nicht zurueckkehren laesst
    (`Body.lean`), und der Erzeuger, der `divergiert` aus `Typ::Nie` setzt (`lean.rs`). -/
def DivergenzOK (sig : String → Option Signatur) : Prop :=
  ∀ f S, sig f = some S → S.divergiert = false

/-- **(U1)** Jeder erklaerte Gerufene haelt die Welt und antwortet gemaess Signatur. -/
def UmgebungOK (P : Programm) (Γ : Typing) (ρ : Env) : Prop :=
  ∀ f S, P.sig f = some S → ∀ t, Welt P.D Γ t.world →
    Welt P.D Γ (ρ f t).1.world ∧
    (match S.ergebnis with
     | some sh => ∃ v, (ρ f t).2 = some v ∧ (v.hasShape sh = true ∨ ∃ r, r ∈ S.gruende ∧ v = .reason r)
     | none => (ρ f t).2 = none ∨ ∃ r, r ∈ S.gruende ∧ (ρ f t).2 = some (.reason r)) ∧
    DivergenzOK P.sig

/-- **(U2)** Jede registrierte Schleife haelt die Welt und ihren Sichtbereich. -/
def SchleifenOK (P : Programm) (Γ : Typing) (ρ : Env) : Prop :=
  ∀ id Δ, P.schleife id = some Δ → ∀ t, Welt P.D Γ t.world → WFU Δ t.local' →
    Welt P.D Γ (ρ id t).1.world ∧ WFU Δ (ρ id t).1.local'

/-! ## 5. Hilfssaetze -/

theorem Welt_store {D : Deklaration} {Γ : Typing} {σ : World} (_hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (p : Place) (v : Value)
    (hv : ∀ sh, Γ p = some sh → v.hasShape sh = true)
    (hk : ∀ c k via, p = .slot c k via → D.slot c via = some .opt → v.hasShape .opt = true) :
    Welt D Γ (store σ p v) := by
  refine ⟨WF_store Γ σ p v hw.1 hv, ?_⟩
  intro c via k hvia
  simp only [store]
  split
  · rename_i h; exact hk c k via h.symm hvia
  · exact hw.2 c via k hvia

/-- Ein Wert, der in eine Slotstelle passt, haelt beide Haelften der Welt. -/
theorem Welt_store_slot {D : Deklaration} {Γ : Typing} {σ : World} (hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (c : String) (k : Int) (f : String) (v : Value) (sh : Shape)
    (hk0 : 0 ≤ k) (hk1 : k < D.count c) (hvs : v.hasShape sh = true)
    (hp : passtIn sh (D.slot c f) = true) :
    Welt D Γ (store σ (.slot c k f) v) := by
  apply Welt_store hD hw
  · intro sh' hΓ
    rw [hD.1 c k f hk0 hk1] at hΓ
    unfold passtIn at hp; rw [hΓ] at hp
    exact passt_hasShape hp hvs
  · intro c' k' via heq hvia
    cases heq
    unfold passtIn at hp; rw [hvia] at hp
    exact passt_hasShape hp hvs

theorem Welt_store_field {D : Deklaration} {Γ : Typing} {σ : World} (hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (c f : String) (v : Value) (sh : Shape)
    (hvs : v.hasShape sh = true) (hp : passtIn sh (D.feld c f) = true) :
    Welt D Γ (store σ (.field c f) v) := by
  apply Welt_store hD hw
  · intro sh' hΓ
    rw [hD.2.1 c f] at hΓ
    unfold passtIn at hp; rw [hΓ] at hp
    exact passt_hasShape hp hvs
  · intro _ _ _ heq; cases heq

theorem Welt_store_global {D : Deklaration} {Γ : Typing} {σ : World} (hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (g : String) (v : Value) (sh : Shape)
    (hvs : v.hasShape sh = true) (hp : passtIn sh (D.global g) = true) :
    Welt D Γ (store σ (.global g) v) := by
  apply Welt_store hD hw
  · intro sh' hΓ
    rw [hD.2.2 g] at hΓ
    unfold passtIn at hp; rw [hΓ] at hp
    exact passt_hasShape hp hvs
  · intro _ _ _ heq; cases heq

/-- Ein angenommener Ausdruck unter dem Sichtbereich: die Form, die unten gebraucht wird. -/
theorem schluss_sicher' {P : Programm} {Γ : Typing} (hD : Deklariert P.D Γ) {Δ : Umgebung}
    {s : State} {e : Expr} {sh : Shape} (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local')
    (h : schluss P.D (formen Δ) e = some sh) :
    ∃ v, eval s e = some v ∧ v.hasShape sh = true :=
  schluss_sicher P.D Γ hD e (formen Δ) s sh hw.1 (WFU_formen hl) hw.2 h

/-- Die Argumente werten aus, und die Parameter liegen danach in ihrem Sichtbereich. -/
theorem argumente_sicher {P : Programm} {Γ : Typing} (hD : Deklariert P.D Γ) {Δ : Umgebung}
    {s : State} (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local') :
    ∀ (params : List (String × Option Shape)) (as : List Expr) (β : Binding),
      namenFrei (params.map (·.1)) = true →
      argumentePassen P (formen Δ) params as = true →
      ∃ vs, evalAll s as = some vs ∧
        WFU (paramUmgebung params) (bindAll (params.map (·.1)) vs β) := by
  intro params
  induction params with
  | nil =>
      intro as β _ h
      cases as with
      | nil => exact ⟨[], rfl, fun n g hn => by simp only [paramUmgebung, such, reduceCtorEq] at hn⟩
      | cons _ _ => simp only [argumentePassen, Bool.false_eq_true] at h
  | cons p ps ih =>
      intro as β hfrei h
      cases as with
      | nil => simp only [argumentePassen, Bool.false_eq_true] at h
      | cons e es =>
          obtain ⟨n, ziel⟩ := p
          simp only [argumentePassen] at h
          split at h
          · rename_i sh hsh
            simp only [Bool.and_eq_true] at h
            obtain ⟨hp, hrest⟩ := h
            simp only [List.map, namenFrei, Bool.and_eq_true, Bool.not_eq_true'] at hfrei
            obtain ⟨hnin, hfrei'⟩ := hfrei
            have hnin' : n ∉ ps.map (·.1) := fun hmem => by
              have h := List.contains_iff_mem.mpr hmem
              rw [h] at hnin; cases hnin
            obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hsh
            obtain ⟨vs, hvs', hrec⟩ := ih es (bindLocal β n v) hfrei' hrest
            refine ⟨v :: vs, by simp only [evalAll, hv, hvs'], ?_⟩
            intro m g hm
            cases ziel with
            | none =>
                simp only [paramUmgebung] at hm
                simpa [List.map, bindAll] using hrec m g hm
            | some z =>
                simp only [paramUmgebung, such] at hm
                split at hm
                · rename_i hmn; subst hmn; cases hm
                  simp only [List.map, bindAll]
                  rw [bindAll_fremd _ vs _ n hnin']
                  simp only [bindLocal_here]
                  show Value.hasShape _ _ = true
                  exact passt_hasShape (by unfold passtIn at hp; simpa using hp) hvs
                · rename_i hmn
                  simpa [List.map, bindAll] using hrec m g hm
          · cases h



/-! ## 6. Der Sicherheitssatz fuer Anweisungen -/

/-- Passt die Antwort zur erklaerten Antwortgestalt -- oder ist sie ein Grund an den
    Rufer? `R` ist der Fehlerkanal des Rufers (`P.ruferR`): ein Wert muss die Gestalt
    treffen, ein Grund in `R` liegen (F6). -/
def AntwortPasst : Option Shape → List String → Option Value → Prop
  | some sh, R, some v => v.hasShape sh = true ∨ ∃ r, r ∈ R ∧ v = .reason r
  | none, R, none => True
  | none, R, some v => ∃ r, r ∈ R ∧ v = .reason r
  | _, _, _ => False

/-- **Was nach einem Schritt gilt** -- je Ausgang. `Δ0` ist der Sichtbereich beim Eintritt,
    `Δ'` der nach der Anweisung; ein Ausgang aus einem Block (`return`, `next`, `leave`)
    traegt den beim Eintritt, weil ein Block Namen nur HINZUFUEGT (U3). `stuck` ist FALSCH:
    das ist die Aussage. -/
def Ergebnis (P : Programm) (Γ : Typing) (erg : Option Shape) (Δ0 Δ' : Umgebung) :
    Outcome → Prop
  | .running s' => Welt P.D Γ s'.world ∧ WFU Δ' s'.local'
  | .returned s' v => Welt P.D Γ s'.world ∧ WFU Δ0 s'.local' ∧ AntwortPasst erg P.ruferR v
  | .exited s' => Welt P.D Γ s'.world ∧ WFU Δ0 s'.local'
  | .left s' => Welt P.D Γ s'.world ∧ WFU Δ0 s'.local'
  | .stuck => False

theorem Ergebnis_schwaecher {P : Programm} {Γ : Typing} {erg : Option Shape}
    {Δ0 Δ1 Δ' Δ'' : Umgebung} {o : Outcome} (h0 : erweitert Δ0 Δ1) (h1 : erweitert Δ' Δ'')
    (h : Ergebnis P Γ erg Δ1 Δ'' o) : Ergebnis P Γ erg Δ0 Δ' o := by
  cases o <;> simp only [Ergebnis] at h ⊢
  · exact ⟨h.1, WFU_erweitert h1 h.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2.1, h.2.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_assign (P : Programm) (erg : Option Shape)
    (c)
    (i)
    (f)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.assign c i f e : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h; exact erweitert_refl _
    · cases h
  · cases h

set_option linter.unusedSectionVars false in
theorem pruefe_erweitert_assignField (P : Programm) (erg : Option Shape)
    (c)
    (f)
    (e)
    (Δ : Umgebung)
    (Δ' : Umgebung)
    (h : pruefe P erg Δ (.assignField c f e : Stmt) = some Δ')
    : erweitert Δ Δ' :=
  by
  simp only [pruefe] at h; split at h
  · split at h
    · cases h; exact erweitert_refl _
    · cases h
  · cases h

end Gabbro.Sicherheit
