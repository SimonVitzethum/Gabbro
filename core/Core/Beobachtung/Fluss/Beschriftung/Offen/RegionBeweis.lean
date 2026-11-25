module

public import Core.Ast.LowLevel.Execution
public import Core.Ast.LowLevel.Proofs.Preservation
public import Core.Beobachtung.Fluss.Beschriftung.Offen.Region
public import Core.Beobachtung.Review.Spur
public import Core.Beobachtung.Nichtinterferenz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.LowLevel (Instruction unit)

/-- Every source place of the low-level unit is public, so source-state equality is equality
    of the local stores. -/
private theorem qsg_lokal {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.lokal = u.lokal := by
  unfold QuellzustandGleich LokaleGleich at h
  dsimp [unit, Flussdaten.leer, LokaleEtiketten.ganz, LokaleEtiketten.gleich, Etiketten.leer] at h
  funext c
  exact h.1 c ⟨0, Nat.zero_lt_one⟩ (by decide)

private theorem qsg_rechte {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.rechte = u.rechte := by
  unfold QuellzustandGleich at h
  exact h.2.2.2.1

private theorem qsg_leihen {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.leihen = u.leihen := by
  unfold QuellzustandGleich at h
  exact h.2.2.2.2.1

private theorem qsg_initial {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) : v.initial = u.initial := by
  unfold QuellzustandGleich at h
  have hx := h.2.2.1
  funext x
  exact Option.some.inj (by
    simpa only [unit, Etiketten.leer, sichtbar, oeffentlich, decide_true, if_true] using hx x)

private theorem frage_leer {Ort : Type} (e : Etiketten Ort)
    (ho : ∀ o, e.objekt o = ∅) (hp : ∀ p, e.endpunkt p = ∅) (q : Frage) : e.frage q = ∅ := by
  unfold Etiketten.frage
  rw [hp q.endpoint]
  induction q.zugriffe with
  | nil => rfl
  | cons t ts ih =>
      rw [List.map_cons, List.foldl_cons, ho t.handle.origin.object, Finset.empty_union]
      exact ih

private theorem etiketten_leer_frage {Ort : Type} (q : Frage) : (Etiketten.leer : Etiketten Ort).frage q = ∅ :=
  frage_leer (Etiketten.leer : Etiketten Ort) (fun _ => rfl) (fun _ => rfl) q

private theorem bind_some {α : Type} (x : Option α) : x.bind some = x := by
  cases x <;> rfl

private theorem qsg_antwort {k : Katalog} (op : Instruction k) {v u : Ast.LowLevel.State k}
    (h : QuellzustandGleich (unit op) v u) (c : Kontext) : v.naechsteAntwort c = u.naechsteAntwort c := by
  unfold QuellzustandGleich at h
  have hx := h.2.2.2.2.2 c
  simpa only [unit, Flussdaten.leer, AntwortSicht, sichtbar, oeffentlich,
    decide_true, if_true, etiketten_leer_frage, bind_some] using hx

private theorem zustand_nach {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {ρ : Lauf E} {t : Nat} (h : ρ.zeit.zustand t = none) : ρ.zeit.zustand (t + 1) = none := by
  have tak := ρ.zeit.takt t
  rw [h] at tak
  cases tak with
  | wartet _ eq _ => exact eq
  | schritt _ step => cases step

private theorem held_gleich {k : Katalog} {v u : Ast.LowLevel.State k} {c : Kontext} {slot : Nat}
    (hl : v.lokal = u.lokal) (hre : v.rechte = u.rechte) (hle : v.leihen = u.leihen) :
    Ast.LowLevel.heldRegion v c slot = Ast.LowLevel.heldRegion u c slot := by
  unfold Ast.LowLevel.heldRegion
  rw [hl, hre, hle]

/-- Whether evaluation succeeds is decided by the public frame, rights and loans. -/
private theorem evaluate_isSome_gleich {k : Katalog} (op : Instruction k)
    {v u : Ast.LowLevel.State k} {c : Kontext}
    (hl : v.lokal = u.lokal) (hre : v.rechte = u.rechte) (hle : v.leihen = u.leihen) :
    (op.evaluate v c).isSome = (op.evaluate u c).isSome := by
  cases op with
  | denoteAddress _ _ _ => rfl
  | selectEnvironment _ _ _ _ => rfl
  | projectAddress slot =>
      simp only [Instruction.evaluate, held_gleich hl hre hle]
  | borrowView slot shape =>
      simp only [Instruction.evaluate, held_gleich hl hre hle]

/-- Inverting the low-level head: only the instruction itself runs at the entry, once. -/
private theorem kopf_heraus {k : Katalog} (op : Instruction k) {v : Ast.LowLevel.State k}
    {c : Kontext} {f : Instruction k} (hv : (unit op).system.kopf v c = some f) :
    f = op ∧ c = Ast.LowLevel.entryContext ∧ (v.lokal c).pc = 0 ∧
      (op.evaluate v c).isSome = true ∧ v.status c = .laeuft := by
  simp only [unit, Ast.LowLevel.system] at hv
  unfold Ast.LowLevel.head at hv
  cases hs : v.status c with
  | ruht =>
      rw [hs] at hv
      cases hv
  | beendet _ =>
      rw [hs] at hv
      cases hv
  | laeuft =>
      rw [hs] at hv
      by_cases hcond : c = Ast.LowLevel.entryContext ∧ (v.lokal c).pc = 0 ∧
          (op.evaluate v c).isSome = true
      · rw [if_pos hcond] at hv
        exact ⟨(Option.some.inj hv).symm, hcond.1, hcond.2.1, hcond.2.2, rfl⟩
      · rw [if_neg hcond] at hv
        cases hv

/-- The low-level unit never issues a question, so no reached state carries a pending one. -/
private theorem unit_fragen_leer_an {k : Katalog} (op : Instruction k) {h : Umgebung}
    {ρ : Lauf (unit op)} (lauf : Laeufe (unit op) h ρ)
    (t : Nat) (s : Ast.LowLevel.State k) (hs : ρ.zeit.zustand t = some s) : s.fragen = [] := by
  induction t generalizing s with
  | zero =>
      rw [lauf.2.2.2] at hs
      simp only [unit] at hs
      unfold Ast.LowLevel.loaded at hs
      split at hs
      · have eqs := Option.some.inj hs
        rw [← eqs]
        rfl
      · cases hs
  | succ t ih =>
      have tak := ρ.zeit.takt t
      cases hv : ρ.zeit.zustand t with
      | none =>
          rw [hv] at tak
          cases tak with
          | wartet _ eq _ => rw [eq] at hs; cases hs
          | schritt _ laufstep => cases laufstep
      | some s0 =>
          have ihs := ih s0 hv
          rw [hv, hs] at tak
          cases tak with
          | wartet label eq _ =>
              have ss : s = s0 := Option.some.inj eq
              subst s
              exact ihs
          | schritt _ laufstep =>
              cases laufstep with
              | schritt impl =>
                  cases impl with
                  | kontext _ _ regel aus =>
                      obtain ⟨_, _, implI⟩ := regel
                      obtain ⟨transfer, _, planEq, hu⟩ := Instruction.implTransfer implI
                      cases (List.cons.inj planEq).1
                      simp only [unit] at aus
                      obtain ⟨_, nextEq⟩ := Instruction.genauInternal aus
                      rw [nextEq, hu]
                      exact ihs
                  | antwort _ hantwort =>
                      obtain ⟨_, _, _, nextEq⟩ := hantwort
                      rw [nextEq]
                      exact ihs
                  | interrupt _ hinterrupt =>
                      obtain ⟨_, _, _, _, _, _, _, _, _, _, nextEq⟩ := hinterrupt
                      rw [nextEq]
                      exact ihs
                  | absturz habsturz =>
                      obtain ⟨_, nextEq⟩ := AbsturzSchritt.genau habsturz
                      rw [nextEq]
                      unfold Zustand.wiederanlauf
                      rw [ihs]

private theorem unit_keine_antwort {k : Katalog} (op : Instruction k) {h : Umgebung}
    {ρ : Lauf (unit op)} (lauf : Laeufe (unit op) h ρ)
    (t : Nat) (a : AntwortEreignis) (spur : SchrittSpur Nat UInt8) :
    ρ.zeit.spur t ≠ some (.antwort a, spur) := by
  intro heq
  have tak := ρ.zeit.takt t
  cases hv : ρ.zeit.zustand t with
  | none =>
      rw [hv] at tak
      cases tak with
      | wartet label _ _ => cases label.symm.trans heq
      | schritt _ laufstep => cases laufstep
  | some s0 =>
      rw [hv, heq] at tak
      generalize hN : ρ.zeit.zustand (t + 1) = nOpt at tak
      cases tak with
      | wartet label _ _ => cases label
      | schritt label laufstep =>
          cases laufstep with
          | schritt impl =>
              cases impl with
              | kontext _ _ _ _ => cases label
              | antwort _ hantwort =>
                  obtain ⟨angebot, _, _, _⟩ := hantwort
                  obtain ⟨q, hqmem, _, _⟩ := angebot.2.2.2.1
                  have leer := unit_fragen_leer_an op lauf t s0 hv
                  rw [leer] at hqmem
                  cases hqmem
              | interrupt _ _ => cases label
              | absturz _ => cases label

end Gabbro.Core.Beobachtung
