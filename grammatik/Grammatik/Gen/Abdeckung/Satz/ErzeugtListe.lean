/-
  File:      Grammatik/Gen/Abdeckung/Satz/ErzeugtListe.lean
  Subject:   WHAT THE GENERATOR EMITS, as a list that is only a specification (never built at run time): the stream
             `Spez.erzeugeF` hands its consumer exactly the elements of `Spez.erzeugtL`, in order (`erzeugeF_eq`), and
             `erzeugeAus` emits every valid program as a `Gutes` and every refused program as
             an `Abgelehntes` (`erzeugeAus_gut`, `erzeugeAus_abgelehnt`). Nothing here runs the generator.
-/
import Grammatik.Gen.Abdeckung.Waehlen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- The contract variants of a skeleton as a list: the specification of `vertragsF`. -/
def Spez.vertragsL (z : Spez) (nc : Nat) (h : Haut z.deklaration) : List (Programm z.deklaration) :=
  letI : Zahlen := z.zahlen
  let P := h.programm
  P :: z.fnListe.flatMap fun f =>
    (List.range (nc + 1)).flatMap (fun n => (reqS f nc n).map fun e =>
      { P with requires := fun g => if hg : g = f then hg ▸ e else Expr.tru }) ++
    (List.range (nc + 1)).flatMap (fun n => (ensS f nc n).map fun e =>
      { P with ensures := fun g => if hg : g = f then hg ▸ e else Expr.tru })

/-- A program with one `requires` of size at most `nc` is one of the contract variants. -/
theorem vertragsL_req (z : Spez) (nc : Nat) (h : Haut z.deklaration) (f : z.deklaration.Fn)
    (e : Expr z.deklaration (z.deklaration.params f) (Signatur.anfang z.deklaration (z.deklaration.signatur f)) .bool)
    (hs : @groesseExpr z.deklaration z.zahlen _ _ _ e ≤ nc) (hu : @groesseExpr z.deklaration z.zahlen _ _ _ e < unendlich) :
    ({ h.programm with requires := fun g => if hg : g = f then hg ▸ e else Expr.tru } : Programm z.deklaration) ∈
      z.vertragsL nc h := by
  letI : Zahlen := z.zahlen
  unfold Spez.vertragsL
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨f, List.mem_finRange f, List.mem_append_left _ ?_⟩)
  refine List.mem_flatMap.2 ⟨groesseExpr e, List.mem_range.2 (by omega), List.mem_map.2 ⟨e, ?_, rfl⟩⟩
  exact mem_tyS (genE_vollst nc nc _ _ _ e hs hs hu)

/-- A program with one `ensures` of size at most `nc` is one of the contract variants. -/
theorem vertragsL_ens (z : Spez) (nc : Nat) (h : Haut z.deklaration) (f : z.deklaration.Fn)
    (e : Expr z.deklaration (ErgCtx (z.deklaration.params f) (z.deklaration.erg f)) (vertragVon z.deklaration f).ende .bool)
    (hs : @groesseExpr z.deklaration z.zahlen _ _ _ e ≤ nc) (hu : @groesseExpr z.deklaration z.zahlen _ _ _ e < unendlich) :
    ({ h.programm with ensures := fun g => if hg : g = f then hg ▸ e else Expr.tru } : Programm z.deklaration) ∈
      z.vertragsL nc h := by
  letI : Zahlen := z.zahlen
  unfold Spez.vertragsL
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨f, List.mem_finRange f, List.mem_append_right _ ?_⟩)
  refine List.mem_flatMap.2 ⟨groesseExpr e, List.mem_range.2 (by omega), List.mem_map.2 ⟨e, ?_, rfl⟩⟩
  exact mem_tyS (genE_vollst nc nc _ _ _ e hs hs hu)

theorem vertragsF_eq {β : Type} (z : Spez) (nc : Nat) (h : Haut z.deklaration) (b : β)
    (s : β → Programm z.deklaration → β) : z.vertragsF nc h b s = (z.vertragsL nc h).foldl s b := by
  simp only [Spez.vertragsF, Spez.vertragsL, List.foldl_cons, Strom.foldl_flatMap, List.foldl_append, List.foldl_map]

/-- **Everything the generator emits at size `k`**, as a list (the specification of the stream). -/
def Spez.erzeugtL (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f)))) (nc k : Nat) :
    List (Erzeugt z) :=
  letI : Zahlen := z.zahlen
  (hautT tbls k).flatMap fun h => (z.vertragsL nc h).flatMap fun P =>
    z.parameter.filterMap fun ws => z.erzeugeAus P ws

/-- **The stream walks exactly the list**, one program after the other. -/
theorem erzeugeF_eq {β : Type} (z : Spez) (tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f))))
    (nc k : Nat) (b : β) (s : β → Erzeugt z → β) : z.erzeugeF tbls nc β k b s = (z.erzeugtL tbls nc k).foldl s b := by
  unfold Spez.erzeugeF Spez.erzeugtL
  rw [@faltet_hautF z.deklaration z.aufz z.zahlen tbls β k b]
  simp only [Strom.foldl_flatMap, vertragsF_eq]

theorem mem_erzeugtL {z : Spez} {tbls : List (Σ f : z.deklaration.Fn, List (List (Rumpf z.deklaration f)))}
    {nc k : Nat} {e : Erzeugt z} :
    e ∈ z.erzeugtL tbls nc k ↔ ∃ h ∈ hautT tbls k, ∃ P ∈ z.vertragsL nc h, ∃ ws ∈ z.parameter,
      z.erzeugeAus P ws = some e := by
  simp [Spez.erzeugtL, List.mem_flatMap, List.mem_filterMap]

/-- A valid program is emitted as a `Gutes`. -/
theorem erzeugeAus_gut {z : Spez} {P : Programm z.deklaration} {ws : List z.deklaration.Fn}
    (hax : z.axs = []) (hb : z.bodenOk P = true) (hv : z.gutB P z.sperreMax (z.wurzelnVon P ws) = true) :
    z.erzeugeAus P ws = some (.gut ⟨P, ws, hax, hb, hv⟩) := by
  unfold Spez.erzeugeAus
  rw [dif_pos hax]
  split
  · rename_i h; rw [hb] at h; cases h
  · split
    · rfl
    · rename_i h; rw [hv] at h; cases h

/-- A refused program is emitted as an `Abgelehntes`. -/
theorem erzeugeAus_abgelehnt {z : Spez} {P : Programm z.deklaration} {ws : List z.deklaration.Fn}
    (hax : z.axs = []) (hb : z.bodenOk P = true) (hv : z.gutB P z.sperreMax (z.wurzelnVon P ws) = false) :
    z.erzeugeAus P ws = some (.abgelehnt ⟨P, ws, hax, hb, hv⟩) := by
  unfold Spez.erzeugeAus
  rw [dif_pos hax]
  split
  · rename_i h; rw [hb] at h; cases h
  · split
    · rename_i h; rw [hv] at h; cases h
    · rfl

end Gabbro.Grammatik.Gen
