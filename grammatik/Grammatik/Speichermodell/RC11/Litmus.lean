/-
  File:      Grammatik/Speichermodell/RC11/Litmus.lean
  Subject:   THE CLASSIC LITMUS SHAPES as statements over EVERY consistent graph of W (no fixture: each
             theorem quantifies over all graphs that contain the shape).
  * `sb_sc_verboten`  -- store buffering with `seq_cst`: the two reads cannot both miss the other
                         thread's write (true SC; under release/acquire the outcome is allowed,
                         `sb_ra_erlaubt` in Trennung.lean);
  * `mp_verboten`     -- message passing through a release/acquire (or `seq_cst`) flag: after seeing
                         the flag, the data read is not older than the data write;
  * `lb_verboten`     -- load buffering, any modes: no two reads that each read the other thread's
                         later write;
  * `corr_verboten`   -- coherence read-read: a later read never reads an older write.
-/
module

public import Grammatik.Speichermodell.RC11.Konsistent

@[expose] public section

namespace Gabbro.Grammatik.Speichermodell.RC11

namespace Graph

variable {E Ort Wert : Type} {G : Graph E Ort Wert}

/-- **Store buffering is forbidden for `seq_cst`.** Thread 1 writes `a₁` then reads `b₁`; thread
    2 writes `a₂` then reads `b₂`. Then not both reads read before the other thread's write
    (`b₁` before `a₂` in `rb` and `b₂` before `a₁`). -/
theorem sb_sc_verboten (hk : G.Konsistent) {a₁ b₁ a₂ b₂ : E}
    (s₁ : G.sc a₁) (s₂ : G.sc b₁) (s₃ : G.sc a₂) (s₄ : G.sc b₂)
    (p₁ : G.po a₁ b₁) (p₂ : G.po a₂ b₂) (r₁ : G.rb b₁ a₂) (r₂ : G.rb b₂ a₁) : False :=
  hk.psc a₁ (.tail (.tail (.tail (.single ⟨s₁, s₂, Or.inl p₁⟩)
    ⟨s₂, s₃, Or.inr (Or.inr (Or.inr (Or.inr r₁)))⟩) ⟨s₃, s₄, Or.inl p₂⟩)
    ⟨s₄, s₁, Or.inr (Or.inr (Or.inr (Or.inr r₂)))⟩)

/-- **Message passing is forbidden through a synchronising flag.** `wd` (data) precedes `wf`
    (flag) in program order; `rf'` reads the flag from `wf` with release/acquire strength
    (`sw`); `rd` follows `rf'`. Then `rd` does not read a write older than `wd`. -/
theorem mp_verboten (hk : G.Konsistent) {wd wf rf' rd : E}
    (p₁ : G.po wd wf) (s : G.sw wf rf') (p₂ : G.po rf' rd) (r : G.rb rd wd) : False :=
  hk.kohaerent wd rd (G.hb_trans (G.hb_trans (G.hb_von_po p₁) (G.hb_von_sw s)) (G.hb_von_po p₂))
    (G.eco_von_rb r)

/-- **Load buffering is forbidden, in every mode.** -/
theorem lb_verboten (hk : G.Konsistent) {r₁ w₁ r₂ w₂ : E}
    (p₁ : G.po r₁ w₁) (f₁ : G.rf w₁ r₂) (p₂ : G.po r₂ w₂) (f₂ : G.rf w₂ r₁) : False :=
  hk.ohneLB r₁ (.tail (.tail (.tail (.single (Or.inl p₁)) (Or.inr f₁)) (Or.inl p₂)) (Or.inr f₂))

/-- **Coherence read-read.** A read `r₂` after `r₁` in program order never reads a write `w₁`
    that `mo` orders before the write `w₂` that `r₁` read. -/
theorem corr_verboten (hk : G.Konsistent) {r₁ r₂ w₁ w₂ : E}
    (p : G.po r₁ r₂) (f₁ : G.rf w₂ r₁) (f₂ : G.rf w₁ r₂) (m : G.mo w₁ w₂) : False := by
  have hne : r₂ ≠ w₂ := by
    rintro rfl
    exact hk.ohneLB _ (.tail (.single (Or.inr f₁)) (Or.inl p))
  exact hk.kohaerent r₁ r₂ (G.hb_von_po p)
    (.tail (.single (Or.inr (Or.inr ⟨w₁, f₂, m, hne⟩))) (Or.inl f₁))

end Graph

end Gabbro.Grammatik.Speichermodell.RC11
