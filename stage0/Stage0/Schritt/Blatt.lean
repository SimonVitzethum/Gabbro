/-
  File:      stage0/Stage0/Schritt/Blatt.lean
  Subject:   The executable step, part 5: the trace facts of a leaf statement and of a foreign call, for the oracle
             stage 0 runs with.

  The machine takes a leaf in one step only if its new trace events extend the old trace and take no lock
  (`hneu`, `hkein_nimmt`). For the leaves of `BlattG` that is `BlattG.erw`; for a foreign call (`axiomCall`,
  `bindAxiom`, `bindAxiomElse`) it is a property of the oracle: **`OrakelSpurTreu`** -- the world the oracle
  answers keeps the trace it was asked in. Stage 0's oracle (the observed system-call answers) has it by
  construction: it changes declared cells only.
-/
import Stage0.Schritt.Grund

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **The oracle keeps the trace** of the world it is asked in. -/
def OrakelSpurTreu (O : Orakel D) : Prop := ∀ a σ ρ, (O.wirkt a σ ρ).1.spur = σ.spur

/-- The prefix a trace grew by, computed from the lengths. -/
def neuVon (s t : List (Ereignis D)) : List (Ereignis D) := s.take (s.length - t.length)

theorem neuVon_eq {s t x : List (Ereignis D)} (h : s = x ++ t) : s = neuVon s t ++ t := by
  subst h
  simp [neuVon]

/-- The answer of a foreign body extends the trace by its question only. -/
theorem axiomAntwort_spur {O : Orakel D} (hO : OrakelSpurTreu O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) : (axiomAntwort O a σ ρ).1.spur = .fremd (.inl a) :: σ.spur := by
  simp only [axiomAntwort]
  rw [hO]
  rfl

theorem axiomAntwortSonst_spur {O : Orakel D} (hO : OrakelSpurTreu O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) : (axiomAntwortSonst O a σ ρ).1.spur = .fremd (.inl a) :: σ.spur := by
  simp only [axiomAntwortSonst]
  rw [hO]
  rfl

/-- **A leaf that ends normally extends the trace by access events and questions only.** -/
theorem blatt_erw {O : Orakel D} (hO : OrakelSpurTreu O) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hleaf : s.istBlatt = true) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hex : execStmt O passes keinRuf s σ ρ = .ok σ' ρ') : Erw σ σ' := by
  cases s with
  | assignSlot t f i e hw hL => exact BlattG.erw O passes keinRuf (.assignSlot t f i e hw hL) σ σ' ρ ρ' hex
  | assignThru p t ht f i e hw hL => exact BlattG.erw O passes keinRuf (.assignThru _ p t ht f i e hw hL) σ σ' ρ ρ' hex
  | assignSlotRef r t ht ho f e hw hL =>
      exact BlattG.erw O passes keinRuf (.assignSlotRef _ r t ht ho f e hw hL) σ σ' ρ ρ' hex
  | assignGlob g e hw hL => exact BlattG.erw O passes keinRuf (.assignGlob g e hw hL) σ σ' ρ ρ' hex
  | putBytes t f hf n i hlo hhi e hw hL =>
      exact BlattG.erw O passes keinRuf (.putBytes t f hf n i hlo hhi e hw hL) σ σ' ρ ρ' hex
  | assignVar x e => exact BlattG.erw O passes keinRuf (.assignVar x e) σ σ' ρ ρ' hex
  | shift t f hτ i von nach hn he hw hL =>
      exact BlattG.erw O passes keinRuf (.shift t f hτ i von nach hn he hw hL) σ σ' ρ ρ' hex
  | regWrite r hk e => exact BlattG.erw O passes keinRuf (.regWrite r hk e) σ σ' ρ ρ' hex
  | transition r hk m hm hl maske bits =>
      exact BlattG.erw O passes keinRuf (.transition r hk m hm hl maske bits) σ σ' ρ ρ' hex
  | publish g e payload hp hw hL => exact BlattG.erw O passes keinRuf (.publish g e payload hp hw hL) σ σ' ρ ρ' hex
  | advances m a h hs => exact BlattG.erw O passes keinRuf (.advances m a h hs) σ σ' ρ ρ' hex
  | retires m s h a => exact BlattG.erw O passes keinRuf (.retires m s h a) σ σ' ρ ρ' hex
  | axiomCall a args h hw hg hd hgd =>
      simp only [execStmt] at hex
      split at hex
      · rename_i σa v hans
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, -⟩ := hex
        have hs := axiomAntwort_spur hO a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [hans] at hs
        refine (Erw.lese σ Λ args.orte).trans ⟨[.fremd (.inl a)], hs, ?_⟩
        intro e he; simp only [List.mem_singleton] at he; subst he; rfl
      · cases hex
  | _ => (try simp [Stmt.istBlatt] at hleaf) <;> simp [execStmt] at hex

end Gabbro.Stage0
