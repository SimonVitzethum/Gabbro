module

public import Core.Ast.Semantik.Kernregister
public import Core.Katalog.Erfuellbar
public import Core.Annahme.AussenLauf
public import Core.Beobachtung.Fluss.Quellfragment
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text Annahme Katalog Maschine

theorem Fragment.akzeptiert_ohne_bedarf (p : Fragment) (platform : Plattform)
    (clauses : p.klauseln = .leer) (rein : ∀ b ∈ p.code, b.Privat)
    (guard : ∀ b ∈ p.code, ∀ frame, b.guard frame = none) :
    Akzeptiert (p.einheit platform) := by
  let E := p.einheit platform
  refine ⟨⟨platform.katalog_wohlgeformt, fun b => Befehl.regelLokal p platform b, ⟨Aussen.zulassung_m2 _, ?_⟩,
    Beobachtung.fragment_fluss_lokal p platform rein, ?_, ?_, ?_⟩, ?_, ?_⟩
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur next step
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, head, transfer⟩ := rule
      obtain ⟨rfl, _, _, hfragen, hantworten, _, _, _, _, hbuchung, _, _, _, hepoch, _, _⟩ := b.vollzug_genau_privat (rein b (kopf_mem head)) (w := w) transfer execute
      obtain ⟨_, hnach⟩ := (b.impl_privat (rein b (kopf_mem head)) c s w _ _).1 transfer
      have hb : next.buchung = s.buchung := by simp only [hbuchung, hnach, Befehl.nach]
      refine ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [], ?_, fun _ mem => (List.not_mem_nil mem).elim⟩, ?_⟩
      · rw [hb]
        exact (List.append_nil _).symm
      · intro h
        have e1 : next.fragen = s.fragen := by simp only [hfragen, hnach, Befehl.nach]
        have e2 : next.antworten = s.antworten := by simp only [hantworten, hnach, Befehl.nach]
        have e3 : next.epoche = s.epoche := by simp only [hepoch, hnach, Befehl.nach]
        simp only [OffeneGriffeEigen, e1, e2, e3, hb, AussengriffeEigen] at h ⊢
        exact h
  · exact schrankenLokal_leer rfl rfl rfl
  · exact Gabbro.Core.Annahme.abschnittWartefrei_ohne_blockade _ fun _ _ _ hb => hb
  · refine ⟨Gabbro.Core.Maschine.eineTabelle_akzeptiert, fun s c i hkopf t c' sv u sv' w q spur himpl haus => ?_⟩
    have memb : i ∈ p.code := kopf_mem hkopf
    obtain ⟨rfl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := i.vollzug_genau_privat (rein i memb) (w := w) himpl haus
    exact spurRespektiert_leer _ _ _
  · intro run conforms
    change (∀ pred ∈ p.klauseln.voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ p.klauseln.invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ p.klauseln.sicher, _
    rw [clauses]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro run conforms t op args need
      obtain ⟨c, b, head, operands⟩ := need
      rw [guard b (List.mem_of_getElem? (kopf_code head))] at operands
      cases operands
    · intro run conforms t waiting
      obtain ⟨contexts, ⟨c, member⟩, blocked⟩ := waiting
      obtain ⟨_, impossible, _⟩ := blocked c member
      exact impossible
    · intro run conforms t l h _ hne
      exact (hne rfl).elim

theorem environmentUnit_erfuellbar : EnvironmentUnitErfuellbarAussage := by
  let name : Identifier := keywordName 'f' ['w'] (by decide) (by
    intro c member
    obtain rfl := List.mem_singleton.mp member
    decide)
  let entry : Decl [] [] := .function mainName mainName_direct [] none
    (fun _ h => (List.not_mem_nil h).elim) none (.braces .done) .nil (fun h => nomatch h) none
  let args : EnvironmentArgs := ⟨name, .biosInterrupt, .biosServices, [], .step entry .done⟩
  let E := environmentUnitForm.einheit .x86_64 args
  have image : E.bild.gueltig E.katalog.plattform.ziel := by
    refine ⟨List.Mem.head _, ?_, ?_⟩
    · intro a v h
      change (if a = 0 then some 0 else none) = some v at h
      split at h
      · rename_i atZero
        subst a
        exact Nat.pow_pos (Nat.zero_lt_succ _)
      · cases h
    · intro a mem
      obtain rfl := List.mem_singleton.mp mem
      exact ⟨0, rfl⟩
  obtain ⟨env, _, hardware, _⟩ := katalog_nichtLeer E.katalog Plattform.x86_64.katalog_wohlgeformt
  obtain ⟨start, allowedStart⟩ := zulStart_erfuellbar hardware image
  have allowed : zugelassen .x86_64 .unit args.unit := by
    refine ⟨?_, rfl⟩
    change ([name.val] : List RawText).Nodup ∧
      ∀ e ∈ [(name, DienstAbi.biosInterrupt, FirmwareZeile.biosServices)],
        e.2.2.zugelassen Plattform.x86_64.katalog e.2.1
    refine ⟨List.nodup_singleton _, ?_⟩
    intro e present
    obtain rfl := List.mem_singleton.mp present
    refine ⟨?_, rfl⟩
    simp only [Katalog.enthaelt, Plattform.katalog, Plattform.zeilen, Plattform.endpunkte,
      FirmwareZeile.endpunkt, List.map_cons, List.mem_append, List.mem_cons, eq_self, or_true, true_or]
  have accepted : Akzeptiert E := by
    refine Fragment.akzeptiert_ohne_bedarf _ _ rfl ?_ ?_
    · intro b present
      change b ∈ [.waehleUmgebung name .biosInterrupt .biosServices,
        .definiere mainName [] none 0 3 false [] none, .blockEnde 0, .rueckVoid, .starte mainName, .ende] at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same | same | same | same | same <;> cases same <;>
        first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
    · intro b present frame
      change b ∈ [.waehleUmgebung name .biosInterrupt .biosServices,
        .definiere mainName [] none 0 3 false [] none, .blockEnde 0, .rueckVoid, .starte mainName, .ende] at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same | same | same | same | same <;> cases same <;> rfl
  let text := Ast.print (category := .unit) args.unit
  let s := (I.start E start).2
  have reads : Ast.Parse (category := .unit) text args.unit := Ast.parse_print _
  exact ⟨.x86_64, start, args, env, text, s, environmentInUnit_printProduction args, reads,
    ⟨args.unit, reads, ⟨rfl, allowed⟩⟩, accepted, hardware, allowedStart, .start,
    environmentUnit_realisiert .x86_64 args s rfl rfl rfl rfl⟩

end Gabbro.Core.Ast.Semantik
