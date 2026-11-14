/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Karte.lean
  Subject:   THREADS RENAMED. The abstract ticket lock (Faeden/Abstrakt.lean) with its threads renamed by an
             injective map (`Abs.karte`): a draw, an enter, a give, a `Weg` and well-formedness are kept. The emitted
             lock names its threads `Fin N`; machine G and the model's ticket lock `Tkt` (Code/Conc/LockRel.lean) name
             them `Faden = Nat`; `Fin.val` is the renaming, so the threads of one emitted lock are the G threads
             `0, …, N - 1`. `bild_laenge`: the abstract queue is no longer than the ghost queue of the emitted lock.
-/
module
public import Stage0.Senke.Sperre.Faeden.Bild
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

/-- The abstract lock with its threads renamed by `f`. -/
def Abs.karte {τ σ : Type} (f : τ → σ) (a : Abs τ) : Abs σ := ⟨a.holder.map f, a.queue.map f⟩

section Karte

variable {τ σ : Type} {f : τ → σ} (hf : Function.Injective f)
include hf

theorem karte_some {x : Option τ} {u : τ} (e : x.map f = some (f u)) : x = some u := by
  cases x with
  | none => simp at e
  | some y =>
    simp only [Option.map_some, Option.some.injEq] at e
    rw [hf e]

theorem karte_mem {l : List τ} {u : τ} (h : f u ∈ l.map f) : u ∈ l := by
  obtain ⟨x, hx, e⟩ := List.mem_map.1 h
  rw [← hf e]
  exact hx

theorem Zieht.karte {u : τ} {a b : Abs τ} (h : Zieht u a b) : Zieht (f u) (a.karte f) (b.karte f) := by
  obtain ⟨hu, hh, rfl⟩ := h
  refine ⟨fun hm => hu (karte_mem hf hm), fun e => hh (karte_some hf e), ?_⟩
  simp only [Abs.karte, List.map_append, List.map_cons, List.map_nil]

theorem Tritt.karte {u : τ} {a b : Abs τ} (h : Tritt u a b) : Tritt (f u) (a.karte f) (b.karte f) := by
  obtain ⟨ha, hq, rfl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Abs.karte, ha, Option.map_none]
  · simp only [Abs.karte, List.head?_map, hq, Option.map_some]
  · simp only [Abs.karte, Option.map_some, List.map_tail]

theorem Gibt.karte {u : τ} {a b : Abs τ} (h : Gibt u a b) : Gibt (f u) (a.karte f) (b.karte f) := by
  obtain ⟨ha, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Abs.karte, ha, Option.map_some]
  · simp only [Abs.karte, Option.map_none]

theorem Opt.karte {r : Abs τ → Abs τ → Prop} {r' : Abs σ → Abs σ → Prop}
    (hr : ∀ a b, r a b → r' (a.karte f) (b.karte f)) {a b : Abs τ} (h : Opt r a b) :
    Opt r' (a.karte f) (b.karte f) := by
  rcases h with e | h
  · exact Or.inl (by rw [e])
  · exact Or.inr (hr a b h)

theorem AbsSchritt.karte {u : τ} {a b : Abs τ} (h : AbsSchritt u a b) :
    AbsSchritt (f u) (a.karte f) (b.karte f) := by
  cases h with
  | zieht h => exact .zieht (h.karte hf)
  | tritt h => exact .tritt (h.karte hf)
  | gibt h => exact .gibt (h.karte hf)

theorem AbsOK.karte {a : Abs τ} (h : AbsOK a) : AbsOK (a.karte f) := by
  refine ⟨h.nodup.map hf, fun x hx hm => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  exact h.frei y hy (karte_mem hf hm)

end Karte

/-- The threads of the emitted lock as G threads: `Fin.val` is injective. -/
theorem fin_val_inj {N : Nat} : Function.Injective (Fin.val : Fin N → Nat) := fun _ _ e => Fin.ext e

/-- The abstract queue is no longer than the ghost queue of the emitted lock. -/
theorem bild_laenge {N : Nat} (σ : Zustand N) : (bild σ).queue.length ≤ σ.q.length := by
  show (bildAus σ.pc σ.q).queue.length ≤ σ.q.length
  cases hq : σ.q with
  | nil => simp [bildAus]
  | cons u r =>
    cases hu : (σ.pc u).haelt with
    | true => simp [bildAus_ja hu]
    | false => simp [bildAus_nein hu]

end Gabbro.Stage0.Senke.Faeden
