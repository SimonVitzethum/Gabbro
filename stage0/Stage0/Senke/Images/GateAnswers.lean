module

public import Stage0.Senke.Anweisung.Bindung.Tor

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR

variable {D : Deklaration}

/-- Every actual returning answer must satisfy a gate contract. The
    existential rules for constructing sequential IR runs also need
    this direction before they can characterize arbitrary executions. -/
structure ImageGateAnswers [Kern] (L : Lay D) (O : Orakel D) : Prop where
  plain : ∀ (a : D.Ax) (b : TorB), L.tor a = some b →
    torGut b (D.aparams a).length = true → ptrParam (D.aparams a) = none →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)) (q : Req) (m : Mem),
    q.nr = BitVec.ofNat 64 b.nr → ArgsW L (reqArg q) ρ →
    (∀ i, (D.aparams a).length ≤ i → i < 6 → reqArg q i = 0) → WeltAt m L σ →
    ∀ answer after, Kern.ans q m answer after →
      ∃ word extra, answer = some (word, extra) ∧ KernW L m after ∧
        WeltAt after L (O.wirkt a σ ρ).1 ∧ (O.wirkt a σ ρ).2 = rohW b (D.agruende a) word
  buffer : ∀ (a : D.Ax) (b : TorB), L.tor a = some b → torGut b (D.aparams a).length = true →
    ∀ (j nt : Nat) (writable : Bool) (t : D.Tab) (f : D.Feld t),
    ptrParam (D.aparams a) = some (j, nt, writable) → D.tabNr nt = some t →
    L.byte t = some f → D.typ t f = .int 0 255 →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)) (q : Req) (m : Mem),
    q.nr = BitVec.ofNat 64 b.nr → ArgsW L (reqArg q) ρ →
    (∀ i, (D.aparams a).length ≤ i → i < 6 → reqArg q i = 0) → WeltAt m L σ →
    (∀ i, i < pufW (D.count t).toNat →
      m.rd64 (reqArg q j + BitVec.ofNat 64 (8 * i)) =
        some (packV (fun k => wAt m (L.elem t f k)) (D.count t).toNat i 8)) →
    ∀ answer after, Kern.ans q m answer after →
      ∃ word extra, answer = some (word, extra) ∧ after.rd = m.rd ∧ after.wr = m.wr ∧
        (∀ y, ¬ ((reqArg q j).toNat ≤ y.toNat ∧
          y.toNat < (reqArg q j).toNat + 8 * pufW (D.count t).toNat) → after.b y = m.b y) ∧
        WeltOhne m L (O.wirkt a σ ρ).1 t f ∧
        (∀ k, k < (D.count t).toNat → Enc L (D.typ t f) ((O.wirkt a σ ρ).1.slots t k f)
          (if writable then byteOf after (reqArg q j) k else wAt m (L.elem t f k))) ∧
        (O.wirkt a σ ρ).2 = rohW b (D.agruende a) word
  area : ∀ (a : D.Ax) (b : TorB) (τ : Ty) (he : D.aerg a = some τ) (j : Nat),
    L.tor a = some b → areaGut b (D.aparams a).length j = true →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)) (q : Req) (m : Mem) (fp : W) (base K : Nat),
    FrameOK m fp K → base + valueWords τ ≤ K → LayIn L → fp.toNat + 8 * K ≤ L.lo →
    q.nr = BitVec.ofNat 64 b.nr → ArgsW L (reqArg q) ρ →
    reqArg q j = slot fp (BitVec.ofNat 64 base) →
    (∀ i, (D.aparams a).length ≤ i → i < 6 → i ≠ j → reqArg q i = 0) → WeltAt m L σ →
    ∀ answer after, Kern.ans q m answer after →
      ∃ tag extra, answer = some (tag, extra) ∧ AgreeW L fp base (base + valueWords τ) m after ∧
        WeltAt after L (O.wirkt a σ ρ).1 ∧ AreaReply L O a b τ he σ ρ after fp base tag

end Gabbro.Stage0.Senke
