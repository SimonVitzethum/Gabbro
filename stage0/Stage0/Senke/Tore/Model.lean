/- The source binding's user duty for an explicit caller-owned result span. -/
module
public import Stage0.Senke.Tore.Code
public import Stage0.Senke.Welt.WeltAt
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- The six argument registers of a request, by number. -/
def reqArg (q : Runner.Req) : Nat → Runner.W
  | 0 => q.a1
  | 1 => q.a2
  | 2 => q.a3
  | 3 => q.a4
  | 4 => q.a5
  | 5 => q.a6
  | _ => 0

theorem reqArg_mk (nr : Runner.W) (f : Nat → Runner.W) :
    ∀ i, i < 6 → reqArg ⟨nr, f 0, f 1, f 2, f 3, f 4, f 5⟩ i = f i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | _ + 6, h => absurd h (by omega)

/-- Request registers encode scalar arguments. Internal pointer markers are ignored here:
    the buffer premise of `TorOK.puf` separately constrains the physical buffer address. -/
def ArgsW (L : Lay D) (f : Nat → Runner.W) : {τs : List Ty} → Env D τs → Prop
  | [], .nil => True
  | τ :: _, .cons v ρ => (if isPtr τ then True else Enc L τ v (f 0)) ∧ ArgsW L (fun j => f (j + 1)) ρ

/-- Both source call forms decode the original oracle answer. The scalar tag
    of the provider ABI is independent of this possibly arbitrarily wide value. -/
def foreignDecode (O : Orakel D) (a : D.Ax) (raw : Int) :
    Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a)) :=
  if D.agruende a = 0 then (einpassenErg O.zeiger (D.aerg a) raw).map Sum.inl
  else sonstPasst O.zeiger (D.aerg a) (D.agruende a) raw

/-- An infallible source call has no extra tag in its oracle answer. -/
theorem foreignDecode_zero {O : Orakel D} {a : D.Ax} {raw : Int}
    (noReasons : D.agruende a = 0) :
    foreignDecode O a raw = (einpassenErg O.zeiger (D.aerg a) raw).map Sum.inl := by
  simp only [foreignDecode, noReasons, ↓reduceIte]

/-- A fallible source call keeps its exact canonical payload/reason decoder. -/
theorem foreignDecode_positive {O : Orakel D} {a : D.Ax} {raw : Int}
    (reasons : 0 < D.agruende a) :
    foreignDecode O a raw = sonstPasst O.zeiger (D.aerg a) (D.agruende a) raw := by
  rw [foreignDecode, if_neg (by omega)]

/-- A successful tag is zero and every result word is initialized with the
    canonical encoding. Listed errors carry their exact nominal reason; an
    invalid answer has an unknown nonzero tag and no usable payload. This is a
    software provider obligation, not a hardware assumption or a runtime proof
    of the source binding's postcondition. -/
def AreaReply (L : Lay D) (O : Orakel D) (a : D.Ax) (b : TorB)
    (τ : Ty) (he : D.aerg a = some τ) (σ : World D) (ρ : Env D (D.aparams a))
    (m : Runner.Mem) (fp : Runner.W) (base : Nat) (tag : Runner.W) : Prop :=
  (∃ value, foreignDecode O a (O.wirkt a σ ρ).2 = some (.inl value) ∧
    tag = 0 ∧ ValueAt L m fp base τ (ergWert he value)) ∨
  (∃ reason errno, foreignDecode O a (O.wirkt a σ ρ).2 = some (.inr reason) ∧
    b.fehler.find? (fun entry => entry.1 == tag.toInt) = some (errno, reason.val)) ∨
  (foreignDecode O a (O.wirkt a σ ρ).2 = none ∧ tag ≠ 0 ∧
    b.fehler.find? (fun entry => entry.1 == tag.toInt) = none)

/-- Provider writes may change the declared source world and exactly the
    caller-owned result span. All frame metadata, other locals, code, and
    permission maps are retained by the existing byte-level frame relation. -/
def AreaContract [Kern] (L : Lay D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (b : TorB) (τ : Ty) (he : D.aerg a = some τ) (j : Nat),
  L.tor a = some b → areaGut b (D.aparams a).length j = true →
  ∀ (σ : World D) (ρ : Env D (D.aparams a)) (q : Runner.Req)
    (m : Runner.Mem) (fp : Runner.W) (base K : Nat),
  FrameOK m fp K → base + valueWords τ ≤ K →
  LayIn L → fp.toNat + 8 * K ≤ L.lo →
  q.nr = BitVec.ofNat 64 b.nr →
  ArgsW L (reqArg q) ρ → reqArg q j = slot fp (BitVec.ofNat 64 base) →
  (∀ i, (D.aparams a).length ≤ i → i < 6 → i ≠ j → reqArg q i = 0) →
  WeltAt m L σ →
  ∃ tag extra m', Kern.ans q m (some (tag, extra)) m' ∧
    AgreeW L fp base (base + valueWords τ) m m' ∧
    WeltAt m' L (O.wirkt a σ ρ).1 ∧ AreaReply L O a b τ he σ ρ m' fp base tag

/-- Register-only profiles impose no result-area provider obligation. -/
theorem areaContract_register_only [Kern] {L : Lay D} (O : Orakel D)
    (registers : ∀ a b, L.tor a = some b → b.resultArea = none) : AreaContract L O := by
  intro a b τ he j bound accepted
  have absent := registers a b bound
  simp only [areaGut, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have present : b.resultArea = some j := accepted.2
  rw [absent] at present
  cases present

end Gabbro.Stage0.Senke
