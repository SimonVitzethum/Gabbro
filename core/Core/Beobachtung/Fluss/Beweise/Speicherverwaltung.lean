module

public import Core.Beobachtung.Speicherverwaltung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.LowLevel (MemInstruction MemState memSetup medium image MemFrame memProgram memHead)

variable (k : Katalog) (code : List MemInstruction)

/-- The selected loader row yields the canonical initial state of a memory program. -/
private theorem mem_geladen {h : Umgebung} {s : AussenStart}
    (hardware : Hardware (memProgram k code).katalog h)
    (zul : (memProgram k code).ZulStart h s) :
    (memProgram k code).laden s (h.lade image) = some (I.start (memProgram k code) s).2 := by
  have gueltig : image.gueltig h.ziel := hardware.ziel.symm ▸ zul.1
  have zeile := hardware.lader image gueltig
  have start : (h.lade image).starts 0 = some 0 := lader_start zeile 0
  have byte : (h.lade image).bytes 0 = some 0 := (zeile.2.1 0 0 rfl).2
  change (if (h.lade image).starts 0 = some 0 ∧ (h.lade image).bytes 0 = some 0 then
      some (Zustand.start _ _ _ _ memSetup.initial (.leer (medium s))) else none) = _
  rw [if_pos ⟨start, byte⟩]
  rfl

/-- Admitted memory-program runs always have a state. -/
private theorem mem_zustand_some {h : Umgebung} {ρ : Lauf (memProgram k code)}
    (lauf : Laeufe (memProgram k code) h ρ) (t : Nat) : ∃ s, ρ.zeit.zustand t = some s := by
  induction t with
  | zero =>
    refine ⟨(I.start (memProgram k code) ρ.start).2, ?_⟩
    rw [lauf.2.2.2]
    change (memProgram k code).laden ρ.start (h.lade image) = _
    exact mem_geladen k code lauf.1 lauf.2.2.1
  | succ t ih =>
    obtain ⟨s, hs⟩ := ih
    have ht := ρ.zeit.takt t
    rw [hs] at ht
    cases ht with
    | wartet _ gleich _ => exact ⟨s, gleich⟩
    | schritt _ step =>
      cases step with
      | schritt impl =>
        rename_i n
        exact ⟨n, rfl⟩

/-- The rule of a memory form determines one frame and the fixed private plan. -/
private theorem mem_regel_aus {c : Kontext} {s u : MemState} {w : PUnit} {p : Ast.LowLevel.Plan}
    (regel : (memProgram k code).system.ImplSchritt c s w [p] u) :
    ∃ f frame, (memProgram k code).system.kopf s c = some f ∧
      MemInstruction.evaluate k.plattform.ziel f s c = some frame ∧
      p = Ast.LowLevel.plan ∧ u = frame.advance c s := by
  rcases regel with ⟨f, kopf, impl⟩
  change MemInstruction.step k.plattform.ziel f c s w [p] u at impl
  rcases impl with ⟨frame, eval, planEq, uEq⟩
  refine ⟨f, frame, kopf, eval, ?_, uEq⟩
  exact (List.cons.inj planEq).1

/-- A memory-program context step appends no low event: the fixed private plan has no
    accesses, no outside action and no journal or time declaration, and the acting frame
    only advances its local state. -/
private theorem mem_kontext_still {ρ : Lauf (memProgram k code)} {predictor t c w spur}
    (tick : ρ.zeit.spur t = some (.kontext c w, spur)) :
    schrittBeob ρ predictor t = [] := by
  classical
  have recorded := ρ.zeit.takt t
  rw [tick] at recorded
  generalize hS : ρ.zeit.zustand t = sOpt at recorded
  generalize hN : ρ.zeit.zustand (t + 1) = nOpt at recorded
  cases recorded with
  | wartet label _ _ => cases label
  | schritt label transition =>
    injection label with evEq
    subst evEq
    cases sOpt with
    | none => cases transition
    | some s =>
      cases nOpt with
      | none => cases transition
      | some n =>
        cases transition with
        | schritt impl =>
          cases impl with
          | kontext _ _ regel aus =>
            obtain ⟨f, frame, kopf, _, planEq, uEq⟩ := mem_regel_aus k code regel
            rw [uEq] at aus
            rw [planEq] at aus
            unfold FuehrtSchrittAus at aus
            rcases aus with ⟨_, _, sperren, v, fuehrtAus, speicherfolge, nEqState⟩
            change FuehrtAus memSetup t c s (frame.advance c s) .intern sperren spur.aussen v at fuehrtAus
            cases fuehrtAus
            have hSpur : spur.speicher = [] := by
              have folge := speicherfolge
              simp only [List.nil_append, List.append_nil, List.map_nil, List.filter_nil,
                Ast.LowLevel.plan, schreibEreignisse] at folge
              cases folge
              rfl
            have hGraph : n.graph = s.graph := by
              have folge := speicherfolge
              simp only [List.nil_append, List.append_nil, List.map_nil, List.filter_nil,
                Ast.LowLevel.plan, schreibEreignisse] at folge
              cases folge
              rfl
            have hBuchung : n.buchung = s.buchung := by
              rw [nEqState]
              rfl
            have hStatus : n.status = s.status := by
              rw [nEqState]
              rfl
            have hCommit : commitBeob (Form := MemInstruction) k.plattform s n = [] := by
              rw [commitBeob, hBuchung, List.drop_length, List.filterMap_nil]
            have hAusgabe : ausgabeBeob (memProgram k code) c (s.lokal c) (n.lokal c) = [] := by
              rfl
            have hZeit : zeitBeob ρ c (s.lokal c) (n.lokal c) = [] := by
              rfl
            have hKontext : kontextBeob ρ predictor t c s n ⟨[], []⟩ = [] := by
              rw [kontextBeob]
              dsimp only
              rw [hCommit, hAusgabe, hZeit, kopf]
              have hSpek : k.plattform.spekulationshuelle.zugriffe
                  ((memProgram k code).fluss.spekulativ f (s.lokal c) predictor) = [] := by
                cases k.plattform <;> rfl
              have hKonstant : (memProgram k code).fluss.konstantzeit f = false := by rfl
              simp only [hSpek, hKonstant, Bool.false_eq_true, if_false, List.map_nil,
                List.nil_append, List.append_nil]
            have hEnde : ∀ d, (neuBeendet s n (memProgram k code).etiketten d).isSome = false := by
              intro d
              rw [neuBeendet, hStatus d]
              cases hst : s.status d <;> rfl
            have hKeinEnde : ¬ ∃ d, (neuBeendet s n (memProgram k code).etiketten d).isSome = true := by
              rintro ⟨d, hd⟩
              rw [hEnde d] at hd
              cases hd
            rw [schrittBeob, tick, hS, hN]
            simp only [hSpur, List.filterMap_nil, List.flatMap_nil, hKontext, hKeinEnde,
              if_false, List.nil_append]

/-- The observed post-state of a memory context step is the advanced frame. -/
private theorem mem_kontext_aus {hw : HwLauf} {t : Nat} {s n : MemState}
    {c : Kontext} {w : PUnit} {spur : SchrittSpur Nat UInt8}
    (step : ImplSchritt memSetup (memProgram k code).system k hw t s
      (.kontext c w, spur) n) :
    ∃ f frame, (memProgram k code).system.kopf s c = some f ∧
      MemInstruction.evaluate k.plattform.ziel f s c = some frame ∧
      n = frame.advance c s := by
  cases step with
  | kontext _ _ regel aus =>
    obtain ⟨f, frame, kopf, eval, planEq, uEq⟩ := mem_regel_aus k code regel
    rw [uEq] at aus
    rw [planEq] at aus
    unfold FuehrtSchrittAus at aus
    rcases aus with ⟨_, _, sperren, v, fuehrtAus, speicherfolge, nEqState⟩
    change FuehrtAus memSetup t c s (frame.advance c s) .intern sperren spur.aussen v at fuehrtAus
    cases fuehrtAus
    have hGraph : n.graph = s.graph := by
      have folge := speicherfolge
      simp only [List.nil_append, List.append_nil, List.map_nil, List.filter_nil,
        Ast.LowLevel.plan, schreibEreignisse] at folge
      cases folge
      rfl
    refine ⟨f, frame, kopf, eval, ?_⟩
    rw [nEqState, hGraph]
    rfl

/-- No memory form issues a question, so no cut of an admitted run has a pending question. -/
private theorem mem_schritt_fragen {hw : HwLauf} {t : Nat} {s n : MemState}
    {spur : SchrittWahl PUnit × SchrittSpur Nat UInt8}
    (step : ImplSchritt memSetup (memProgram k code).system k hw t s spur n)
    (leer : s.fragen = []) : n.fragen = [] := by
  cases step with
  | kontext _ _ regel aus =>
    obtain ⟨_, _, _, _, planEq, uEq⟩ := mem_regel_aus k code regel
    rw [uEq] at aus
    rw [planEq] at aus
    unfold FuehrtSchrittAus at aus
    rcases aus with ⟨_, _, sperren, v, fuehrtAus, _, nEqState⟩
    change FuehrtAus memSetup t c s (frame.advance c s) .intern sperren spur.aussen v at fuehrtAus
    cases fuehrtAus
    rw [nEqState]
    change s.fragen = []
    exact leer
  | antwort _ h =>
    obtain ⟨_, _, _, nEqState⟩ := h
    rw [nEqState]
    change s.fragen = []
    exact leer
  | interrupt _ h =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, nEqState⟩ := h
    rw [nEqState]
    change s.fragen = []
    exact leer
  | absturz h =>
    rw [h.genau.2]
    change s.fragen = []
    exact leer

private theorem mem_fragen_leer {h : Umgebung} {ρ : Lauf (memProgram k code)}
    (lauf : Laeufe (memProgram k code) h ρ) (t : Nat) :
    ρ.zeit.zustand t = none ∨ ∃ z, ρ.zeit.zustand t = some z ∧ z.fragen = [] := by
  induction t with
  | zero =>
    right
    refine ⟨(I.start (memProgram k code) ρ.start).2, ?_, ?_⟩
    · rw [lauf.2.2.2]
      change (memProgram k code).laden ρ.start (h.lade image) = _
      exact mem_geladen k code lauf.1 lauf.2.2.1
    · rfl
  | succ t ih =>
    cases ih with
    | inl noneq =>
      have tick := ρ.zeit.takt t
      rw [noneq] at tick
      cases tick with
      | schritt _ step => cases step
      | wartet _ eq _ => exact Or.inl eq
    | inr gefunden =>
      obtain ⟨z, atZ, fragenLeer⟩ := gefunden
      have tick := ρ.zeit.takt t
      rw [atZ] at tick
      cases tick with
      | schritt _ step =>
        cases nach : ρ.zeit.zustand (t + 1) with
        | none => cases step
        | some n =>
          right
          refine ⟨n, rfl, ?_⟩
          cases step with
          | schritt impl =>
            exact mem_schritt_fragen k code impl fragenLeer
      | wartet _ eq _ =>
        right
        exact ⟨z, eq, fragenLeer⟩

private theorem mem_fragen_leer_an {h : Umgebung} {ρ : Lauf (memProgram k code)}
    (lauf : Laeufe (memProgram k code) h ρ) (t : Nat) {z : MemState}
    (atZ : ρ.zeit.zustand t = some z) : z.fragen = [] := by
  cases mem_fragen_leer k code lauf t with
  | inl noneq => cases atZ.symm.trans noneq
  | inr gefunden =>
    obtain ⟨z', eq, leer⟩ := gefunden
    cases Option.some.inj (atZ.symm.trans eq)
    exact leer

/-- A memory step advances only the acting frame, so publicly equal pre-states have
    publicly equal post-states with the same machine fields. -/
private theorem mem_zustand_gleich {c : Kontext} {vor w₂ : MemState} {frame : MemFrame}
    (g : QuellzustandGleich (memProgram k code) vor w₂)
    (epoche : vor.epoche = w₂.epoche) (geliefert : vor.geliefert = w₂.geliefert)
    (kerne : vor.kerne = w₂.kerne) (status : vor.status = w₂.status) :
    QuellzustandGleich (memProgram k code) (frame.advance c vor) (frame.advance c w₂) ∧
      (frame.advance c vor).epoche = (frame.advance c w₂).epoche ∧
      (frame.advance c vor).geliefert = (frame.advance c w₂).geliefert ∧
      (frame.advance c vor).kerne = (frame.advance c w₂).kerne ∧
      (frame.advance c vor).status = (frame.advance c w₂).status := by
  obtain ⟨lokGleich, endeGleich, initialGleich, rechteEq, leihenEq, antwortGleich⟩ := g
  have lokEqFun : vor.lokal = w₂.lokal := by
    funext d
    exact lokGleich d ⟨0, Nat.zero_lt_one⟩ rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro d p hp
    change Function.update vor.lokal c {frame with pc := (vor.lokal c).pc + 1} d =
      Function.update w₂.lokal c {frame with pc := (w₂.lokal c).pc + 1} d
    by_cases hdc : d = c
    · subst d
      simp only [Function.update_self]
      rw [congrFun lokEqFun c]
    · rw [Function.update_of_ne hdc, Function.update_of_ne hdc]
      exact congrFun lokEqFun d
  · intro d
    change EndeSicht (memProgram k code) d (vor.status d) =
      EndeSicht (memProgram k code) d (w₂.status d)
    exact endeGleich d
  · intro x
    change sichtbar ((memProgram k code).etiketten.ort x) (vor.initial x) =
      sichtbar ((memProgram k code).etiketten.ort x) (w₂.initial x)
    exact initialGleich x
  · change vor.rechte = w₂.rechte
    exact rechteEq
  · change vor.leihen = w₂.leihen
    exact leihenEq
  · intro d
    change AntwortSicht (memProgram k code) vor d = AntwortSicht (memProgram k code) w₂ d
    exact antwortGleich d
  · change vor.epoche = w₂.epoche
    exact epoche
  · change vor.geliefert = w₂.geliefert
    exact geliefert
  · change vor.kerne = w₂.kerne
    exact kerne
  · change vor.status = w₂.status
    exact status

/-- Every context step of a memory program preserves the coupling of two admitted runs. -/
theorem speicherverwaltungNI : SpeicherverwaltungsNIAussage := by
  intro k code f flu h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor zustand kopf spurGlied kopplung
  classical
  have takt₁ := ρ₁.zeit.takt t
  rw [spurGlied, zustand] at takt₁
  generalize hN₁ : ρ₁.zeit.zustand (t + 1) = nOpt₁ at takt₁
  cases takt₁ with
  | wartet label _ _ => cases label
  | schritt label step₁ =>
    injection label with evEq
    subst evEq
    cases nOpt₁ with
    | none => cases step₁
    | some nach₁ =>
      cases step₁ with
      | schritt impl₁ =>
        have kopfFrame := mem_kontext_aus k code impl₁
        cases impl₁ with
        | kontext keinAbsturz₁ bereit₁ regel₁ aus₁ =>
          obtain ⟨f₁, frame₁, kopf₁, eval₁, _, hNach₁⟩ := kopfFrame
          have hf : f = f₁ := Option.some.inj (kopf.symm.trans kopf₁)
          subst f₁
          obtain ⟨k₁, geleg₁, kern₁, stat₁⟩ := bereit₁
          have core₁ : (ρ₁.hw.angebot t).core = some k₁ := geleg₁
          have crashEq : (ρ₁.hw.angebot t).crash = (ρ₂.hw.angebot t).crash :=
            congrArg (fun pr => (pr.1 t).2.2.2.2.2.1) vergleich.politik
          have coreEq : (ρ₁.hw.angebot t).core = (ρ₂.hw.angebot t).core :=
            congrArg (fun pr => (pr.1 t).1) vergleich.politik
          have signaleEq : (ρ₁.hw.angebot t).interrupts = (ρ₂.hw.angebot t).interrupts :=
            congrArg (fun pr => (pr.1 t).2.2.1) vergleich.politik
          have auswahlEq : (ρ₁.hw.angebot t).interruptAuswahl =
              (ρ₂.hw.angebot t).interruptAuswahl := by
            simp only [Gelegenheit.interruptAuswahl, signaleEq]
          have crash₂ : (ρ₂.hw.angebot t).crash = false := by
            rw [← crashEq]
            exact keinAbsturz₁
          have auswahl₁none : (ρ₁.hw.angebot t).interruptAuswahl = none := by
            cases haus : (ρ₁.hw.angebot t).interruptAuswahl with
            | some _ =>
              have res := (vergleich.links.2.1.2 t).interrupt_reserviert haus
              rw [res.2.1] at core₁
              cases core₁
            | none => rfl
          have auswahl₂none : (ρ₂.hw.angebot t).interruptAuswahl = none := by
            rw [← auswahlEq]
            exact auswahl₁none
          obtain ⟨w₂, zustand₂⟩ := mem_zustand_some k code vergleich.rechts t
          obtain ⟨⟨lokGleich, endeGleich, initialGleich, rechteEq, leihenEq, antwortGleich⟩,
            epocheEq, geliefertEq, kerneEq, statusEq⟩ := kopplung.2.1 vor w₂ zustand zustand₂
          have lokEqFun : vor.lokal = w₂.lokal := by
            funext d
            exact lokGleich d ⟨0, Nat.zero_lt_one⟩ rfl
          have sysKopf : ∀ s d, (memProgram k code).system.kopf s d =
              memHead k.plattform.ziel code s d := fun _ _ => rfl
          have kopf₂ : (memProgram k code).system.kopf w₂ c = some f := by
            have hHead : memHead k.plattform.ziel code w₂ c = memHead k.plattform.ziel code vor c := by
              simp only [memHead, lokEqFun.symm, statusEq.symm]
            rw [sysKopf, hHead, ← sysKopf]
            exact kopf
          have e₁ : NiedrigeBeob (memProgram k code) ρ₁ predictor (t + 1) =
              NiedrigeBeob (memProgram k code) ρ₁ predictor t := by
            change NiedrigeBeob (memProgram k code) ρ₁ predictor t ++ schrittBeob ρ₁ predictor t = _
            rw [mem_kontext_still k code t (c := c) (w := w) (spur := spur) spurGlied, List.append_nil]
          have takt₂ := ρ₂.zeit.takt t
          rw [zustand₂] at takt₂
          generalize hN₂ : ρ₂.zeit.zustand (t + 1) = nOpt₂ at takt₂
          cases takt₂ with
          | wartet label gleich₂ _ =>
            cases nOpt₂ with
            | none => cases gleich₂
            | some nach₂ =>
              have e₂ : NiedrigeBeob (memProgram k code) ρ₂ predictor (t + 1) =
                  NiedrigeBeob (memProgram k code) ρ₂ predictor t := by
                rw [beob_pause ρ₂ predictor t label]
              have hNach₂Pause : nach₂ = w₂ := Option.some.inj gleich₂
              have zustandGleich := mem_zustand_gleich k code (c := c) (vor := vor) (w₂ := w₂)
                (frame := frame₁) ⟨lokGleich, endeGleich, initialGleich, rechteEq, leihenEq, antwortGleich⟩
                epocheEq geliefertEq kerneEq statusEq
              refine ⟨?_, ?_, ?_⟩
              · rw [e₁, e₂]
                exact kopplung.1
              · intro a b ha hb
                rw [hN₁] at ha
                rw [hN₂] at hb
                obtain rfl := Option.some.inj ha
                obtain rfl := Option.some.inj hb
                rw [hNach₁, hNach₂Pause]
                exact zustandGleich
              · rw [e₁, e₂]
                exact kopplung.2.2
          | schritt label₂ step₂ =>
            cases nOpt₂ with
            | none => cases step₂
            | some nach₂ =>
              cases step₂ with
              | schritt impl₂ =>
                have stepCopy := impl₂
                cases impl₂ with
                | kontext _ bereit₂' regel₂' aus₂' =>
                  obtain ⟨k₂, geleg₂, kern₂, stat₂⟩ := bereit₂'
                  have core₂ : (ρ₂.hw.angebot t).core = some k₂ := geleg₂
                  have kk : k₁ = k₂ := Option.some.inj (core₁.symm.trans (coreEq.trans core₂))
                  have gleich : (w₂.kerne k₂).laeuft = some c := by
                    rw [← kk, ← kerneEq]
                    exact kern₁
                  have c_eq : c₂ = c := Option.some.inj (kern₂.symm.trans gleich)
                  subst c₂
                  obtain ⟨f₂, frame₂, kopf₂', eval₂, hNach₂⟩ := mem_kontext_aus k code stepCopy
                  have hf₂ : f = f₂ := Option.some.inj (kopf₂.symm.trans kopf₂')
                  subst f₂
                  have evalEq := MemInstruction.evaluate_congr f k.plattform.ziel c
                    lokEqFun rechteEq leihenEq
                  have frameEq : frame₁ = frame₂ :=
                    Option.some.inj (eval₁.symm.trans (evalEq.trans eval₂))
                  rw [← frameEq] at hNach₂
                  have e₂ : NiedrigeBeob (memProgram k code) ρ₂ predictor (t + 1) =
                      NiedrigeBeob (memProgram k code) ρ₂ predictor t := by
                    change NiedrigeBeob (memProgram k code) ρ₂ predictor t ++
                      schrittBeob ρ₂ predictor t = _
                    rw [mem_kontext_still k code t label₂, List.append_nil]
                  have zustandGleich := mem_zustand_gleich k code (c := c) (vor := vor) (w₂ := w₂)
                    (frame := frame₁) ⟨lokGleich, endeGleich, initialGleich, rechteEq, leihenEq, antwortGleich⟩
                    epocheEq geliefertEq kerneEq statusEq
                  refine ⟨?_, ?_, ?_⟩
                  · rw [e₁, e₂]
                    exact kopplung.1
                  · intro a b ha hb
                    rw [hN₁] at ha
                    rw [hN₂] at hb
                    obtain rfl := Option.some.inj ha
                    obtain rfl := Option.some.inj hb
                    rw [hNach₁, hNach₂]
                    exact zustandGleich
                  · rw [e₁, e₂]
                    exact kopplung.2.2
                | antwort _ h =>
                  obtain ⟨angebot, _, _, _⟩ := h
                  obtain ⟨_, _, _, present, _⟩ := angebot
                  obtain ⟨q, hq, _⟩ := present
                  have leer := mem_fragen_leer_an k code vergleich.rechts t zustand₂
                  rw [leer] at hq
                  cases hq
                | interrupt _ h =>
                  obtain ⟨_, _, _, _, _, pending₂, _, _, _, _, _⟩ := h
                  have contra := pending₂.2.2.2.2
                  rw [auswahl₂none] at contra
                  cases contra
                | absturz h =>
                  obtain ⟨offer₂, _, _⟩ := h
                  rw [offer₂.2] at crash₂
                  cases crash₂

end Gabbro.Core.Beobachtung
