/- The actual full-span store loop updates the canonical source world relation. -/
import Stage0.Senke.Welt.Spans.SpanStore
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration} {L : Lay D}

theorem SpanEffect.value_keep {fp : Runner.W} {tmp address count a : Nat} {m m' : Runner.Mem}
    {τ : Ty} {v : Wert D τ} (effect : SpanEffect fp tmp address count m m')
    (scratch : fp.toNat + 8 * (tmp + 1) ≤ a)
    (bound : a + 8 * valueWords τ ≤ 2 ^ 64)
    (sep : a + 8 * valueWords τ ≤ address ∨ address + 8 * count ≤ a)
    (input : ValueAt L m (BitVec.ofNat 64 a) 0 τ v) :
    ValueAt L m' (BitVec.ofNat 64 a) 0 τ v := by
  refine ⟨input.1, fun i hi => ?_⟩
  have index : i < valueWords τ := by simpa only [encodeWords_length] using hi
  simp only [Nat.zero_add, absolute_slot]
  rw [effect.read (by omega) (Or.inr (by omega)) (by omega)]
  simpa only [Nat.zero_add, absolute_slot] using input.2 i hi

/-- The store's full postvalue and exact footprint suffice for the whole new world. -/
theorem weltAt_slot_effect {fp : Runner.W} {tmp : Nat} {m m' : Runner.Mem}
    {σ : World D} {t : D.Tab} {f : D.Feld t} {kn : Nat} {v : Wert D (D.typ t f)}
    (world : WeltAt m L σ) (layout : LayIn L) (apart : LayDis L)
    (scratch : fp.toNat + 8 * (tmp + 1) ≤ L.lo) (cell : (kn : Int) < L.count t)
    (effect : SpanEffect fp tmp (L.elem t f kn) (valueWords (D.typ t f)) m m')
    (output : StorageAt L m' (L.elem t f kn) (D.typ t f) v) :
    WeltAt m' L (σ.storeSlot t kn f v) := by
  have top := layout.2.2
  refine ⟨fun t' f' k' hk' => ?_, fun g => ?_, world.2.2.keep effect.wr⟩
  · by_cases same : (Zelle.elem t' f' k' : Zelle D) = .elem t f kn
    · cases same; simpa [World.storeSlot, StorageAt] using output
    · have hin := layout.1 t' f' k' hk'
      have sep := apart.spans (.elem t f kn) (.elem t' f' k') cell hk' (Ne.symm same)
      rw [storeSlot_other same]
      exact effect.value_keep (by omega) (by omega)
        (by simpa [Zelle.adr, Zelle.bytes, or_comm] using sep) (world.1 t' f' k' hk')
  · have hin := layout.2.1 g
    have sep := apart.spans (.elem t f kn) (.glob g) cell trivial (by simp)
    exact effect.value_keep (by omega) (by omega)
      (by simpa [Zelle.adr, Zelle.bytes, or_comm] using sep) (world.2.1 g)

/-- The same complete update rule applies to globals. -/
theorem weltAt_glob_effect {fp : Runner.W} {tmp : Nat} {m m' : Runner.Mem}
    {σ : World D} {g : D.Glob} {v : Wert D (D.gtyp g)}
    (world : WeltAt m L σ) (layout : LayIn L) (apart : LayDis L)
    (scratch : fp.toNat + 8 * (tmp + 1) ≤ L.lo)
    (effect : SpanEffect fp tmp (L.ga g) (valueWords (D.gtyp g)) m m')
    (output : StorageAt L m' (L.ga g) (D.gtyp g) v) : WeltAt m' L (σ.storeGlob g v) := by
  have top := layout.2.2
  refine ⟨fun t f k hk => ?_, fun g' => ?_, world.2.2.keep effect.wr⟩
  · have hin := layout.1 t f k hk
    have sep := apart.spans (.glob g) (.elem t f k) trivial hk (by simp)
    exact effect.value_keep (by omega) (by omega)
      (by simpa [Zelle.adr, Zelle.bytes, or_comm] using sep) (world.1 t f k hk)
  · by_cases same : g' = g
    · subst g'; simpa [World.storeGlob, StorageAt] using output
    · have hin := layout.2.1 g'
      have sep := apart.spans (.glob g) (.glob g') trivial trivial (by simp [Ne.symm same])
      have kept := effect.value_keep (by omega) (by omega)
        (by simpa [Zelle.adr, Zelle.bytes, or_comm] using sep) (world.2.1 g')
      simpa [World.storeGlob, same] using kept

/-- Connected expression evaluation followed by the actual complete global store. -/
theorem storeGlobalCode_ok [Kern] {m : Runner.Mem} {pc fp : Runner.W} {K d reserved : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {σ : World D} {g : D.Glob} {v : Wert D (D.gtyp g)} {ce : List II}
    (layout : LayIn L) (apart : LayDis L) (separated : fp.toNat + 8 * K ≤ L.lo)
    (room : d + valueWords (D.gtyp g) < K)
    (pre : Pre L m pc fp K d
      (ce ++ storeSpan (valueWords (D.gtyp g)) (d + valueWords (D.gtyp g)) d (L.ga g))
      ρ (fun m => WeltAt m L σ) reserved)
    (expression : ∀ m pc, Pre L m pc fp K d ce ρ (fun m => WeltAt m L σ) reserved →
      ValueOk L m pc fp K d ce (D.gtyp g) v) :
    ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (ce ++ storeSpan (valueWords (D.gtyp g))
          (d + valueWords (D.gtyp g)) d (L.ga g)).length), fp⟩ m' ∧
      AgreeW L fp d K m m' ∧ WeltAt m' L (σ.storeGlob g v) := by
  obtain ⟨m1, s1, a1, value⟩ := expression m pc pre.left
  have next := pre.next a1 (Nat.le_refl d) (by omega)
  have gin := layout.2.1 g
  have top := layout.2.2
  have old := next.welt.2.1 g
  obtain ⟨m2, s2, effect, output⟩ := storeValue_run layout separated room pre.small next.frame
    (Nat.le_refl _) gin.1 gin.2 next.code (by simpa only [storeSpan_length] using next.far) value
    (fun i hi => next.welt.2.2.word (by omega) (by omega) top)
    (fun i hi => rd64_some_all (by
      simpa only [Nat.zero_add, absolute_slot] using old.2 i (by simpa only [encodeWords_length] using hi)))
  have newWorld := weltAt_glob_effect next.welt layout apart (by omega) effect output
  have changed := (agreeW_of a1).trans ((effect.agreeW room gin.1 gin.2).mono (by omega : d ≤ d + valueWords (D.gtyp g)))
  refine ⟨m2, ?_, changed, newWorld⟩
  have combined := s1.trans s2
  simpa [List.length_append, storeSpan_length, Nat.mul_add, ← Nat.mul_assoc,
    BitVec.ofNat_add, BitVec.add_assoc] using combined

/-- Acceptance of the actual store emitter composes with the generic source-value proof. -/
theorem globalStoreC_ok [Kern] {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {σ : World D} {g : D.Glob} {v : Wert D (D.gtyp g)}
    {child : List II × Nat} {code : List II}
    (made : globalStoreC L g d child = some (code, top)) (fits : top ≤ K)
    (layout : LayIn L) (apart : LayDis L) (separated : fp.toNat + 8 * K ≤ L.lo)
    (pre : Pre L m pc fp K d code ρ (fun m => WeltAt m L σ) reserved)
    (expression : ∀ m pc, Pre L m pc fp K d child.1 ρ (fun m => WeltAt m L σ) reserved →
      ValueOk L m pc fp K d child.1 (D.gtyp g) v) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      AgreeW L fp d K m m' ∧ WeltAt m' L (σ.storeGlob g v) := by
  have room := globalStoreC_top made
  unfold globalStoreC at made
  split at made
  · cases made
    exact storeGlobalCode_ok layout apart separated (by omega) pre expression
  · cases made

end Gabbro.Stage0.Senke
