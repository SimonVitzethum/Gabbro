module

public import Stage0.Senke.Anweisung.Bindung.Tor
public import Stage0.Senke.Images.ModelExport
public import Runner.IR.Futex

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

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg Runner Runner.IR Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- Raw requests that an image's housekeeping code can issue. A gate
    may use the same transport, so this predicate is only a permission
    to explain a request as internal at its issuing source boundary. -/
def imageCanBeInternal (event : Ev) : Bool :=
  let request := event.2.1
  decide (request = cloneReq ∨ request.nr.toNat = NR_EXIT ∨ request.nr.toNat = NR_EXIT_GROUP ∨
    request = futexReq request.a1 128 request.a3 ∨ request = futexReq request.a1 129 request.a3)

def imageSourceForeignEvents {D : Deklaration} (run : Lauf D) : List (Faden × D.Ax) :=
  run.filterMap fun step => match step.ereignis with
    | .fremd (.inl routine) => some (step.faden, routine)
    | _ => none

inductive ImageForeignTraceAlignment (output : Emitted src reserve options) :
    List Ev → List (Faden × (declOf output.compiled.unit).Ax) → Prop
  | nil : ImageForeignTraceAlignment output [] []
  | internal {event events calls} : imageCanBeInternal event = true →
      ImageForeignTraceAlignment output events calls → ImageForeignTraceAlignment output (event :: events) calls
  | gate {event events typed calls actual} : event.1 = typed.1 → output.image.Y.tor typed.2 = some actual →
      event.2.1.nr = BitVec.ofNat 64 actual.nr → ImageForeignTraceAlignment output events calls →
      ImageForeignTraceAlignment output (event :: events) (typed :: calls)

/-- Host observations and typed calls align in order. The compiler
    refinement selects the originating gate even when its transport
    also serves internal image operations. -/
def ImageForeignTrace (output : Emitted src reserve options)
    (history : List Ev) (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) : Prop :=
  ImageForeignTraceAlignment output history
      (imageSourceForeignEvents (D := (declOf output.compiled.unit).mitRuhe) state.m.lauf)

theorem ImageForeignTraceAlignment.append {output : Emitted src reserve options}
    {first last : List Ev} {calls more : List (Faden × (declOf output.compiled.unit).Ax)}
    (head : ImageForeignTraceAlignment output first calls)
    (suffix : ImageForeignTraceAlignment output last more) :
    ImageForeignTraceAlignment output (first ++ last) (calls ++ more) := by
  induction head with
  | nil => exact suffix
  | internal allowed _ ih => exact .internal allowed ih
  | gate thread transport number _ ih => exact .gate thread transport number ih

end Gabbro.Stage0
