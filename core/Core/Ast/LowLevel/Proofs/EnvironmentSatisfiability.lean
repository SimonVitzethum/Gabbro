module

public import Core.Ast.Semantik.Kernregister
public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Text Annahme Katalog Maschine

theorem Fragment.akzeptiert_ohne_bedarf (p : Fragment) (platform : Plattform)
    (clauses : p.klauseln = .leer)
    (guard : ∀ b ∈ p.code, ∀ frame, b.guard frame = none) :
    Akzeptiert (p.einheit platform) := by
  let E := p.einheit platform
  refine ⟨⟨platform.katalog_wohlgeformt, fun b => b.lokal E rfl, Aussen.zulassung_m2 _, ?_⟩, ?_, ?_⟩
  · apply aussen_gueltig_ohne_fragen
    intro run t s w spur next step ev mem
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, _, transfer⟩ := rule
      obtain ⟨rfl, _⟩ := b.vollzug_genau (w := ()) transfer execute
      exact List.not_mem_nil mem
    | antwort _ h =>
      exact frage_absurd_mem (by rw [h.2.1] at mem; exact mem) (by intro same; cases same)
    | interrupt _ h =>
      obtain ⟨_, _, _, _, _, _, _, _, events, _, _⟩ := h
      exact frage_absurd_mem (by rw [events] at mem; exact mem) (by intro same; cases same)
    | absturz h =>
      obtain ⟨_, events, _⟩ := h
      exact frage_absurd_mem (by rw [events] at mem; exact mem) (by intro same; cases same)
  · intro run conforms
    change (∀ pred ∈ p.klauseln.voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ p.klauseln.invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ p.klauseln.sicher, _
    rw [clauses]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · constructor
    · intro run conforms t op args need
      obtain ⟨c, b, head, operands⟩ := need
      rw [guard b (List.mem_of_getElem? (kopf_code head))] at operands
      cases operands
    · intro run conforms t waiting
      obtain ⟨contexts, ⟨c, member⟩, blocked⟩ := waiting
      obtain ⟨_, impossible, _⟩ := blocked c member
      exact impossible

theorem environmentUnit_erfuellbar : EnvironmentUnitErfuellbarAussage := by
  let name : Identifier := keywordName 'f' ['w'] (by decide) (by
    intro c member
    obtain rfl := List.mem_singleton.mp member
    decide)
  let entry : Decl [] [] := .function mainName (by
    simp only [directName, ordinaryLocal, mainName, keywordName, String.reduceToList,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, List.cons.injEq,
      Char.reduceEq, false_and, and_false, false_or, or_false, not_false_eq_true, and_true]
    constructor <;> intro same
    all_goals
      have equal := (List.cons.inj same).1
      simp only [Char.reduceEq] at equal) [] none
    (fun _ h => (List.not_mem_nil h).elim) none (.braces .done) .nil (fun h => nomatch h)
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
    change ([name.val] : List RawText).Nodup ∧
      ∀ e ∈ [(name, DienstAbi.biosInterrupt, FirmwareZeile.biosServices)],
        e.2.2.zugelassen Plattform.x86_64.katalog e.2.1
    refine ⟨List.nodup_singleton _, ?_⟩
    intro e present
    obtain rfl := List.mem_singleton.mp present
    refine ⟨?_, rfl⟩
    simp [Katalog.enthaelt, Plattform.katalog, Plattform.zeilen, Plattform.endpunkte, FirmwareZeile.endpunkt]
  have accepted : Akzeptiert E := by
    apply Fragment.akzeptiert_ohne_bedarf _ _ rfl
    intro b present frame
    change b ∈ [.waehleUmgebung name .biosInterrupt .biosServices,
      .definiere mainName [] none 0 3 false [], .blockEnde 0, .rueckVoid, .starte mainName, .ende] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same | same | same | same | same <;> cases same <;> rfl
  let text := Ast.print (category := .unit) args.unit
  let s := (I.start E start).2
  have reads : Ast.Parse (category := .unit) text args.unit := Ast.parse_print _
  exact ⟨.x86_64, start, args, env, text, s, environmentInUnit_printProduction args, reads,
    ⟨args.unit, reads, ⟨rfl, allowed⟩⟩, accepted, hardware, allowedStart, .start,
    environmentUnit_realisiert .x86_64 args s rfl rfl rfl rfl⟩

end Gabbro.Core.Ast.Semantik
