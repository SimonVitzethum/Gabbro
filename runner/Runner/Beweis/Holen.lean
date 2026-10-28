import Runner.Beweis.Lauf

/-! # Fetching through the instruction layer, and straight-line runs

`step_code`: where `Code` holds at `rip`, the model executes the instruction placed there (`decode_enc`).
`reach_runL`: the model runs a placed list the way `runL` computes it. -/

namespace Runner.Beweis
open Runner.X86

theorem enc_len_le (i : Ins) : (enc i).length ≤ 15 := by
  cases i <;> simp [enc, memEnc, regEnc, le32]

theorem fetch_eq {m : Mem} {a : W} {l : List B} (h : Bytes m a l) (hl : l.length ≤ 15) :
    ∃ r, fetch m a = l ++ r := by
  refine ⟨(List.range (15 - l.length)).map fun j => m.b (a + BitVec.ofNat 64 (l.length + j)), ?_⟩
  have e : fetch m a = (List.range (l.length + (15 - l.length))).map
      (fun i => m.b (a + BitVec.ofNat 64 i)) := by
    simp only [fetch]
    congr 2
    omega
  rw [e, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.getElem_map, List.getElem_range]
  exact (h j (by simpa using h1)).1

theorem step_code {x : X} {i : Ins} {is : List Ins} (h : Code x.mem x.rip (i :: is)) :
    step x = exec i (enc i).length x := by
  obtain ⟨ho, hb, _⟩ := h
  obtain ⟨r, hr⟩ := fetch_eq hb (enc_len_le i)
  have ha : Mem.all x.mem.rd x.rip (enc i).length = true := all_of fun j hj => (hb j hj).2.1
  simp only [step, hr, decode_enc i ho r, ha, ↓reduceIte]

theorem reach_runL : ∀ (is : List Ins) (x : X), Code x.mem x.rip is →
    (∀ i ∈ is.dropLast, Fall i = true) → Reach x (runL is x)
  | [], x, _, _ => Star.refl x
  | i :: is, x, hc, hf => by
    have hs := step_code hc
    simp only [runL]
    cases he : exec i (enc i).length x with
    | next y =>
      simp only [bind_next]
      obtain ⟨hk, hr⟩ := exec_next he
      apply Reach.cons (hs.trans he)
      cases is with
      | nil => exact Star.refl y
      | cons j js =>
        have hfi : Fall i = true := hf i (by simp)
        apply reach_runL
        · rw [hr hfi]; exact hc.2.2.keep hk
        · intro k hk'
          exact hf k (by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hk')
    | fault => exact Reach.here (hs.trans he) (by simp)
    | sys q k => exact Reach.here (hs.trans he) (by simp)
    | unk => exact Reach.here (hs.trans he) (by simp)

end Runner.Beweis
