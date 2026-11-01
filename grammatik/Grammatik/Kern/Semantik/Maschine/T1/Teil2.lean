module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Kern.Semantik.Maschine.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

theorem genUpdate_noteq (m : Faden → List (Ereignis D)) (f g : Faden) (h : g ≠ f)
    (s : List (Ereignis D)) :
    genUpdate m f s g = m g := by
  simp only [genUpdate, h, ↓reduceIte]

/-- **One step of the generated machine.** `blatt`: thread `f` runs one leaf
    statement through `execStmt` (shared memory moves on writes); `nimmt`:
    `f` takes `L` while nobody else holds it (the lock as scheduler rule);
    `gibt`: `f` releases `L`. Every step appends its post-world to the history. -/
inductive GenSchritt (P : Programm D) (O : Orakel D) (passes : Nat) :
    GenMaschine D → Faden → GenMaschine D → Prop where
  | blatt (M : GenMaschine D) (f : Faden)
      (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hΛ : HeldGenau Λ (offen (M.spuren f)))
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
      (hneu : σ'.spur = neu ++ M.spuren f)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
      GenSchritt P O passes M f
        ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
         M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
  | nimmt (M : GenMaschine D) (f : Faden) (L : D.Lock)
      (hself : L ∉ offen (M.spuren f))
      (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
      (hfrei : GenFrei M f L) :
      GenSchritt P O passes M f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)],
         M.tiefe + 1⟩
  | gibt (M : GenMaschine D) (f : Faden) (L : D.Lock)
      (hhaelt : L ∈ offen (M.spuren f)) :
      GenSchritt P O passes M f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.gibt L],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)],
         M.tiefe + 1⟩

/-! ## 8. Computing with `Lauf.spur` on generated runs

   List-only facts about run projection: appending one step's events grows the
   acting thread's projection by exactly those events and leaves every other
   thread's projection (at any covered position) unchanged. -/

theorem gen_spur_append_le (l xs : Lauf D) (f : Faden) (j : Nat) (hj : j ≤ l.length) :
    (l ++ xs).spur f j = l.spur f j := by
  unfold Lauf.spur
  rw [List.take_append_of_le_length hj]

theorem gen_spur_length (l : Lauf D) (f : Faden) :
    l.spur f l.length =
      (l.filterMap fun s => if s.faden = f then some s.ereignis else none).reverse := by
  unfold Lauf.spur
  rw [List.take_length]

theorem genFilterMap_eigen (f : Faden) (neu : List (Ereignis D)) :
    (genEigen f neu).filterMap (fun s => if s.faden = f then some s.ereignis else none) =
      neu.reverse := by
  unfold genEigen
  induction neu.reverse with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ↓reduceIte, Option.some.injEq, List.filterMap_cons_some, ih]


end Gabbro.Grammatik
