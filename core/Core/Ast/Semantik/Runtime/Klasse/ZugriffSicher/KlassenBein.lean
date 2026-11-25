/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/ZugriffSicher/KlassenBein.lean
  Subject:   THE CLASS-DETERMINED LEGS OF AN ACCESS STEP (the first unit of
              `ZugriffSicherAussage`). An access command owes booking and releases, the authority
              of pending questions, device authority, committed outside operations, invariant
              preservation and the lock-window condition. The first four are exactly
              `klassenSicherheit` of the access class; the fifth is `zugriffInvariantenBein`; the
              sixth is vacuous because an access plan is the internal action. Together with the
              frame-only duty they give the per-form premise of
              `sicherheit_aus_regeln_ohne_rennen`. The race leg is deliberately absent: it is a
              run invariant in that induction. No statement is changed and nothing is weakened.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.ZugriffSicher.InvariantenBein
public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Sicherheit
public import Core.Ast.Semantik.Runtime.Atom.Klassenrein
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Sicherheit

/-- No access form touches a lock word: its class is never `sperre`. -/
theorem Zugriffsform.beruehrtSperrwort_false (z : Zugriffsform) :
    z.klasse.beruehrtSperrwort = false := by
  cases z <;> rfl

/-- **The five per-form legs of an access instruction.** The race leg is supplied by the run. -/
theorem zugriffRegelPflichten (p : Fragment) (platform : Plattform) (ps : List Praedikat)
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt) (z : Zugriffsform) :
    RegelPflichtenOhneRennen (p.sicherheitsEinheit platform) (.zugriff z) := by
  obtain ⟨speicherBein, fragenBein, registerBein, commitBein⟩ := klassenSicherheit z.klasse
  have emb : (Befehl.zugriff z).form.Eingebettet (p.sicherheitsEinheit platform).maschine (.zugriff z) :=
    Befehl.eingebettet p platform (.zugriff z)
  constructor
  · intro H ρ t c w vor zwischen nach plan spur head impl aus
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact speicherBein (Zugriffsform.beruehrtSperrwort_false z) Befehl
        (p.sicherheitsEinheit platform) (.zugriff z) (Befehl.zugriff z).form rfl emb
        ρ.hw t c w vor zwischen nach plan spur head impl aus
    · intro vorSicher
      exact zugriffInvariantenBein p platform ps tab z t c vor zwischen nach plan spur impl aus vorSicher
    · intro keinAbsturz
      obtain ⟨rahmen, _, sperren, v, aktion, folge, zustand⟩ := aus
      have intern : plan.aktion = .intern := Zugriffsform.ideal_aktion_intern (w := w) z impl
      rw [intern] at aktion
      obtain ⟨_, _, vGleich⟩ := fuehrtAus_intern_nil c (p.einheit platform).einrichtung aktion
      rw [vGleich] at zustand
      have hsperren : nach.sperren = vor.sperren := by rw [zustand, rahmen.sperren]
      intro l wechsel
      rw [hsperren] at wechsel
      exact (wechsel rfl).elim
    · exact registerBein Befehl (p.sicherheitsEinheit platform) (.zugriff z) (Befehl.zugriff z).form rfl emb
        ρ.hw t c w vor zwischen nach plan spur head impl aus
    · exact commitBein Befehl (p.sicherheitsEinheit platform) (.zugriff z) (Befehl.zugriff z).form rfl emb
        H ρ t c w vor zwischen nach plan spur head impl aus
  · exact fragenBein Befehl (p.sicherheitsEinheit platform) (.zugriff z) (Befehl.zugriff z).form rfl emb

/-- **Every form of a class-pure fragment carries the five legs and the pending-authority duty.**
    A frame-only form pays its own class; an access form pays the class legs above; a form outside
    the fragment's code never stands at a head, so its duty is vacuous. -/
theorem fragmentRegelPflichtenOhneRennen (p : Fragment) (platform : Plattform)
    (ps : List Praedikat) (klassenrein : p.KlassenRein)
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (okAll : ∀ b ∈ p.code, pruefeBefehlErhalt ps b = true) (f : Befehl) :
    RegelPflichtenOhneRennen (p.sicherheitsEinheit platform) f := by
  by_cases hmem : f ∈ p.code
  · rcases klassenrein f hmem with hpriv | ⟨z, hz⟩
    · have voll := f.sicherheitsPflichten p platform ps tab okAll hpriv
      refine ⟨?_, voll.2⟩
      intro H ρ t c w vor zwischen nach plan spur head impl aus
      exact (voll.1 H ρ t c w vor zwischen nach plan spur head impl aus).ohneRennen
    · subst hz
      exact zugriffRegelPflichten p platform ps tab z
  · constructor
    · intro H ρ t c w vor zwischen nach plan spur head
      exact absurd (kopf_mem head) hmem
    · intro t c w vor zwischen nach plan spur head
      exact absurd (kopf_mem head) hmem

end Gabbro.Core.Ast.Semantik
