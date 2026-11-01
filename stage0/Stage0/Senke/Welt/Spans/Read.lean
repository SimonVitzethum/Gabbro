/- Complete global reads for integration into the shared expression emitter. -/
import Stage0.Senke.Welt.Spans.Span
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

theorem globalValueC_top {L : Lay D} {g : D.Glob} {dst top : Nat} {code : List II}
    (made : globalValueC L g dst = some (code, top)) :
    top = dst + valueWords (D.gtyp g) := by
  unfold globalValueC at made
  split at made
  · cases made; rfl
  · cases made

/-- Real emitted global loads, with all inherited expression-frame contracts. -/
theorem globalValueC_ok [Kern] {L : Lay D} {g : D.Glob} {dst top K reserved : Nat}
    {code : List II} {m : Runner.Mem} {pc fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ}
    {σ : World D} {W : Runner.Mem → Prop}
    (made : globalValueC L g dst = some (code, top)) (room : top ≤ K)
    (world : ∀ m, W m → WeltAt m L σ)
    (pre : Pre L m pc fp K dst code ρ W reserved) :
    ValueOk L m pc fp K dst code (D.gtyp g) (σ.globs g) := by
  unfold globalValueC at made
  split at made
  · next bound =>
    cases made
    obtain ⟨m', steps, changed, output⟩ := loadSpan_stable_run
      (encodeWords L (D.gtyp g) (σ.globs g)) pre.frame pre.small
      (by simpa only [encodeWords_length] using room)
      (by simpa only [encodeWords_length] using bound)
      (by simpa only [encodeWords_length] using pre.code)
      (by simpa only [encodeWords_length, loadSpan_length] using pre.far)
      pre.wstab pre.welt (fun m hm => (world m hm).2.1 g |>.2)
    refine ⟨m', ?_, Agree.widen (by simpa only [encodeWords_length] using changed) room,
      (world m pre.welt).2.1 g |>.1, output⟩
    simpa [encodeWords_length, loadSpan_length, ← Nat.mul_assoc] using steps
  · cases made

/-- A precondition at a deeper context depth. -/
theorem Pre.raise [Kern] {L : Lay D} {m : Runner.Mem} {pc fp : Runner.W} {K d d' : Nat} {c : List II}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {reserved : Nat}
    (h : Pre L m pc fp K d c ρ W reserved) (hd : d ≤ d') : Pre L m pc fp K d' c ρ W reserved :=
  ⟨Nat.le_trans h.ctx hd, h.small, h.frame, h.code, h.far, h.env, h.welt, h.wstab⟩

/-- The address producer and all runtime span loads compose under the original
    generic expression precondition. No scalar projection of the stored value occurs. -/
theorem pointerWorldValue_ok [Kern] {L : Lay D} {m : Runner.Mem} {pc fp a : Runner.W}
    {K d reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {τ : Ty} {v : Wert D τ}
    {W : Runner.Mem → Prop} {lead : List II}
    (room : d + valueWords τ + 1 < K) (literal : 8 * valueWords τ < 2 ^ 31)
    (pre : Pre L m pc fp K d
      (lead ++ loadPointerSpan (valueWords τ) d (d + valueWords τ) (d + valueWords τ + 1) 0) ρ W reserved)
    (address : ∀ m pc, Pre L m pc fp K (d + valueWords τ) lead ρ W reserved →
      Ok m pc fp K (d + valueWords τ) lead (· = a))
    (source : ∀ m, W m → ValueAt L m a 0 τ v) :
    ValueOk L m pc fp K d
      (lead ++ loadPointerSpan (valueWords τ) d (d + valueWords τ) (d + valueWords τ + 1) 0) τ v := by
  obtain ⟨m1, s1, changed, pointer, read, same⟩ := address m pc
    (pre.left.raise (d' := d + valueWords τ) (by omega))
  subst pointer
  have next := pre.next (changed.mono (by omega : d ≤ d + valueWords τ)) (Nat.le_refl _) (by omega)
  obtain ⟨m2, s2, changed2, effect, output, pointer'⟩ := loadPointerValue_stable_run
    next.frame pre.small (Nat.le_refl _) (by omega) room (by simpa using literal)
    next.code (by simpa only [loadPointerSpan_length] using next.far) read next.wstab next.welt source
  refine ⟨m2, ?_, (changed.mono (by omega : d ≤ d + valueWords τ)).trans changed2, output⟩
  have combined := s1.trans s2
  simpa [List.length_append, loadPointerSpan_length, Nat.mul_add, ← Nat.mul_assoc,
    BitVec.ofNat_add, BitVec.add_assoc] using combined

end Gabbro.Stage0.Senke
