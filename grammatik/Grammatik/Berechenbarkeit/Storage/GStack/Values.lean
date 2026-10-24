import Grammatik.Bausteine.Arena.Unbounded.Realization
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaLinkForm

/-! Payload-sensitive stack representation in the EXISTING G world. This
connects the heap backend's observable stack values to the executed linked-list
forms rather than treating the lists' contents as an external oracle. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open ArenaKette

variable {D : Deklaration} {A : FreiForm D}

def Represents (L : LinkFeld A) (G : LinkKopf A) (σ : World D)
    (values : List (Wert D (D.typ A.tab A.feld))) : Prop :=
  ∃ indices, KetteF (D.count A.tab) (L.wert σ) (G.st σ) indices ∧ indices.Nodup ∧
    (∀ i ∈ indices, A.Lebt σ i) ∧ indices.map (fun i => σ.slots A.tab i A.feld) = values

theorem Represents.list_ok {L : LinkFeld A} {G : LinkKopf A} {σ : World D} {values}
    (hr : Represents L G σ values) : ListOk A L G σ := by
  obtain ⟨indices, hc, hn, hl, _⟩ := hr
  exact ⟨indices, hc, hn, hl⟩

theorem Represents.unique {L : LinkFeld A} {G : LinkKopf A} {σ : World D} {xs ys}
    (hx : Represents L G σ xs) (hy : Represents L G σ ys) : xs = ys := by
  obtain ⟨is, hc, _, _, hv⟩ := hx
  obtain ⟨js, hd, _, _, hw⟩ := hy
  have he := KetteF.eindeutig hc hd
  subst js
  exact hv.symm.trans hw

theorem represents_empty {L : LinkFeld A} {G : LinkKopf A} {σ : World D}
    (hh : G.st σ = D.count A.tab) : Represents L G σ [] := by
  exact ⟨[], hh ▸ KetteF.nil, .nil, by simp, rfl⟩

/-- A non-empty observed stack has an actual in-bounds head cell. -/
theorem Represents.nonempty {L : LinkFeld A} {G : LinkKopf A} {σ : World D} {value values}
    (hr : Represents L G σ (value :: values)) : G.st σ < D.count A.tab := by
  obtain ⟨indices, hc, _, _, hv⟩ := hr
  generalize hhead : G.st σ = head at hc ⊢
  cases hc with
  | nil => simp at hv
  | cons i _ hi _ _ => exact hi

/-- Exact framing, including payloads, not merely the linked shape. -/
theorem Represents.frame {L : LinkFeld A} {G : LinkKopf A} {σ σ' : World D} {values}
    (hr : Represents L G σ values) (hh : G.st σ' = G.st σ)
    (hn : ∀ i, L.wert σ' i = L.wert σ i)
    (hl : ∀ i, Auf (D.count A.tab) (L.wert σ) (G.st σ) i → A.Lebt σ' i)
    (hp : ∀ i, Auf (D.count A.tab) (L.wert σ) (G.st σ) i →
      σ'.slots A.tab i A.feld = σ.slots A.tab i A.feld) :
    Represents L G σ' values := by
  obtain ⟨indices, hc, hnd, hlive, hvalues⟩ := hr
  refine ⟨indices, hh ▸ hc.uebertragen (fun i _ => hn i), hnd,
    fun i hi => hl i ⟨indices, hc, hi⟩, ?_⟩
  rw [← hvalues]
  apply List.map_congr_left
  intro i hi
  exact hp i ⟨indices, hc, hi⟩

theorem Represents.reads {L : LinkFeld A} {G : LinkKopf A} {σ : World D} {values}
    (hr : Represents L G σ values) (Λ : List (Res D)) (places : List (D.Tab ⊕ D.Glob)) :
    Represents L G (σ.lese Λ places) values :=
  hr.frame rfl (fun _ => rfl) (fun i hi =>
    (A.lebt_gleich (σ := σ) (σ' := σ.lese Λ places) rfl (fun _ => rfl) rfl i).mpr (hr.list_ok.lebt_auf hi))
    (fun _ _ => rfl)

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
