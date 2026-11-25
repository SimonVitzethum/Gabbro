/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Stapel/Satz.lean
  Subject:   The pinned class stack statement (MK-03), assembled from the seven family lemmas. Every
             instruction belongs to exactly one `LokalFamilie`; its family lemma gives the frame-level
             stack effect, and the class fixes the permitted bound (zero for `lokal`, one for `ruf`).
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Klasse
public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Skalar
public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Kontrollfluss
public import Core.Ast.Semantik.Runtime.Klasse.Stapel.AufrufSchleife
public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Aggregat
public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Variante
public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Text
public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Zugriff

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- **Every instruction pays the stack effect of its class.** The seven family lemmas cover all
    constructors of `Befehl`; the class bound is `0` for a purely local step and `1` for a call. -/
theorem klassenStapel : KlassenStapelAussage := by
  intro b
  cases h : b.familie with
  | skalar => exact skalarStapel b h
  | kontrollfluss => exact kontrollflussStapel b h
  | aufrufSchleife => exact aufrufSchleifeStapel b h
  | aggregat => exact aggregatStapel b h
  | variante => exact varianteStapel b h
  | text => exact textStapel b h
  | zugriff => exact zugriffStapel b h

end Gabbro.Core.Ast.Semantik
