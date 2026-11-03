/- The source binding's user duty for an explicit caller-owned result span. -/
module
public import Stage0.Senke.Tore.AreaCode
public import Stage0.Senke.Tore.RequestModel
public import Stage0.Senke.Welt.WeltAt
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Both source call forms decode the original oracle answer. The scalar tag
    of the provider ABI is independent of this possibly arbitrarily wide value. -/
def foreignDecode (O : Orakel D) (a : D.Ax) (raw : Int) :
    Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a)) :=
  if D.agruende a = 0 then (einpassenErg O.zeiger (D.aerg a) raw).map Sum.inl
  else sonstPasst O.zeiger (D.aerg a) (D.agruende a) raw

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
  q.nr = BitVec.ofNat 64 b.nr →
  ArgsW L (reqArg q) ρ → reqArg q j = slot fp (BitVec.ofNat 64 base) →
  (∀ i, (D.aparams a).length ≤ i → i < 6 → i ≠ j → reqArg q i = 0) →
  WeltAt m L σ →
  ∃ tag extra m', Kern.ans q m (some (tag, extra)) m' ∧
    AgreeW L fp base (base + valueWords τ) m m' ∧
    WeltAt m' L (O.wirkt a σ ρ).1 ∧ AreaReply L O a b τ he σ ρ m' fp base tag

end Gabbro.Stage0.Senke
