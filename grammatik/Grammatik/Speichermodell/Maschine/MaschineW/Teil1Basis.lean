module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Speichermodell.Maschine.Sicht

@[expose] public section



namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

/-! ## 1. The state -/

/-- A message of a carrier: timestamp, the memory after the write (only the carrier's own
    component is read), and the view it carries. -/
abbrev NachrichtW (D : Deklaration) := Nachricht (D.Tab ⊕ D.Glob) (Speicher D)

/-- A view over the carriers. -/
abbrev SichtW (D : Deklaration) := Sicht (D.Tab ⊕ D.Glob)

/-- **A state of machine W**: machine G's state and the weak memory. -/
structure RufMaschineW (D : Deklaration) where
  g : RufMaschineG D
  hist : D.Tab ⊕ D.Glob → List (NachrichtW D)
  sicht : Faden → SichtW D
  lsicht : D.Lock → SichtW D

/-- **The start of W** over a start of G: every carrier holds ONE message, the initial memory
    at timestamp 0; every view is empty. -/
def RufStartW (M0 : RufMaschineG D) : RufMaschineW D :=
  ⟨M0, fun _ => [⟨0, M0.speicher, Sicht.null⟩], fun _ => Sicht.null, fun _ => Sicht.null⟩

/-- The order of a carrier: a table and a plain global are relaxed; an `atomic` has the order
    of its declaration (`ord`). -/
def ordVon (ord : D.Glob → Ordnung) : D.Tab ⊕ D.Glob → Ordnung
  | .inl _ => .entspannt
  | .inr g => if D.atomar g then ord g else .entspannt

/-- A machine of G with its shared memory replaced. -/
def mitSpeicher (M : RufMaschineG D) (σ : Speicher D) : RufMaschineG D :=
  { M with speicher := σ }

/-- The carriers a step READS (its recorded read events). -/
def lesenVon (M M' : RufMaschineG D) (u : Faden) : List (D.Tab ⊕ D.Glob) :=
  (zugriffe M M' u).filterMap fun p => if p.2 then none else some p.1

/-- The locks a step TAKES (its `nimmt` events). -/
def genommenVon (M M' : RufMaschineG D) (u : Faden) : List D.Lock :=
  (ereignisse M M' u).filterMap fun e => match e with
    | .nimmt L _ => some L
    | _ => none

/-- The locks a step RELEASES (its `gibt` events). -/
def gegebenVon (M M' : RufMaschineG D) (u : Faden) : List D.Lock :=
  (ereignisse M M' u).filterMap fun e => match e with
    | .gibt L => some L
    | _ => none

/-- The view after the reads of `rs` (message `wahl c` at `c`). -/
def lesesicht (ord : D.Glob → Ordnung) (wahl : D.Tab ⊕ D.Glob → NachrichtW D)
    (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) : SichtW D :=
  rs.foldr (fun c w => w.verein (beitrag (ordVon ord c) c (wahl c))) v

/-- The view after taking the locks `Ls`. -/
def locksicht (ls : D.Lock → SichtW D) (Ls : List D.Lock) (v : SichtW D) : SichtW D :=
  Ls.foldr (fun L w => w.verein (ls L)) v

/-- The view of thread `u` before its writes: after its reads and the locks it takes. -/
def vorSicht (ord : D.Glob → Ordnung) (W : RufMaschineW D) (u : Faden) (σ : Speicher D)
    (M'' : RufMaschineG D) (wahl : D.Tab ⊕ D.Glob → NachrichtW D) : SichtW D :=
  locksicht W.lsicht (genommenVon (mitSpeicher W.g σ) M'' u)
    (lesesicht ord wahl (lesenVon (mitSpeicher W.g σ) M'' u) (W.sicht u))

/-! ## 2. The step -/

/-- **The acting thread's head is an `exchange` of `g`** (the one read-modify-write form of the
    language: `let x = g exchange update(v) { … }`, emitted as ONE atomic read-modify-write --
    `atomic_fetch_*`, `atomic_exchange` or a compare-and-swap loop). Only the rule
    `dannExchange` fires at such a head (`exchange_liest_schreibt`, RMW.lean). -/
def ExchangeKopf (M : RufMaschineG D) (u : Faden) (g : D.Glob) : Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
    (hw : (vertragVon D (M.faeden u).kopf.f).gschreibt g = true) (hL : gdarf D g Λ)
    (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ),
    (M.faeden u).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.exchange g neuE hw hL rest) k⟩

/-- The global an `exchange` at the head of a rest reads and writes (`none`: no exchange). -/
def GRest.exchangeGlob {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Option D.Glob
  | .dann (.exchange g _ _ _ _) _ => some g
  | _ => none

/-- An `exchange` head is seen by `exchangeGlob` (so a head whose `exchangeGlob` computes to
    `none` is no exchange head -- decided by evaluation on a concrete machine). -/
theorem exchangeKopf_glob {M : RufMaschineG D} {u : Faden} {g : D.Glob}
    (h : ExchangeKopf M u g) : (M.faeden u).kopf.rest.2.2.2.2.exchangeGlob = some g := by
  obtain ⟨l, Γ, Λ, Λ', neuE, hw, hL, rest, k, ρ, hK⟩ := h
  rw [hK]
  rfl

/-- **One step of W, with its witnesses**: the presented memory `σ`, G's step to `M''` on it,
    the message read at every carrier (`wahl`), and the timestamp of every write (`neu`). -/
structure SchrittW (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W : RufMaschineW D) (u : Faden) (W' : RufMaschineW D) (σ : Speicher D)
    (M'' : RufMaschineG D) (wahl : D.Tab ⊕ D.Glob → NachrichtW D)
    (neu : D.Tab ⊕ D.Glob → Nat) : Prop where
  /-- Machine G steps on the presented memory. -/
  schritt : RufSchrittG P O passes (mitSpeicher W.g σ) u M''
  /-- At a carrier the step reads: SOME message at or above the thread's view. -/
  lies : ∀ c, LiestG (mitSpeicher W.g σ) M'' u c →
    Lesbar W.hist (W.sicht u) c (wahl c) ∧ TraegerGleich σ (wahl c).wert c
  /-- At a carrier the step does not read: G's memory. -/
  ungelesen : ∀ c, ¬ LiestG (mitSpeicher W.g σ) M'' u c → TraegerGleich σ W.g.speicher c
  /-- A write takes a fresh timestamp above the view before the writes. -/
  frisch : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c →
    Frisch W.hist (vorSicht ord W u σ M'' wahl) c (neu c)
  /-- G's memory: written carriers from the step, the others unchanged. -/
  speicherS : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c →
    TraegerGleich W'.g.speicher M''.speicher c
  speicherU : ∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c →
    TraegerGleich W'.g.speicher W.g.speicher c
  faeden : W'.g.faeden = M''.faeden
  lauf : W'.g.lauf = M''.lauf
  start : W'.g.start = M''.start
  /-- A written carrier gets its message. -/
  histS : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c →
    W'.hist c = nachricht (ordVon ord c) (vorSicht ord W u σ M'' wahl) c (neu c) W'.g.speicher
      :: W.hist c
  histU : ∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c → W'.hist c = W.hist c
  /-- The acting thread's view: its write timestamps, else the view before the writes. -/
  sichtS : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c → W'.sicht u c = neu c
  sichtU : ∀ c, ¬ SchreibG (mitSpeicher W.g σ) M'' u c →
    W'.sicht u c = vorSicht ord W u σ M'' wahl c
  sichtF : ∀ t, t ≠ u → W'.sicht t = W.sicht t
  /-- A released lock joins the thread's final view. -/
  lsicht : ∀ L, W'.lsicht L =
    if L ∈ gegebenVon (mitSpeicher W.g σ) M'' u then (W.lsicht L).verein (W'.sicht u)
    else W.lsicht L
  /-- **A read-modify-write is atomic** (Opus lane O25c, 2026-09-26): an `exchange` of `g`
      writes `g` DIRECTLY above the message it read (`ts + 1`). With `frisch` no other write sits
      in between, so no two RMWs read one message (`w_kein_verlust`, RMW.lean) -- RC11's
      atomicity of read-modify-writes, which the C11 `atomic_fetch_*`/`atomic_exchange`/CAS the
      emitter writes guarantee. -/
  rmw : ∀ g, ExchangeKopf W.g u g → neu (.inr g) = (wahl (.inr g)).ts + 1

/-- **The step relation of W.** -/
def RufSchrittW (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W : RufMaschineW D) (u : Faden) (W' : RufMaschineW D) : Prop :=
  ∃ σ M'' wahl neu, SchrittW P O passes ord W u W' σ M'' wahl neu

/-- **The machines W reaches** from `W0`. -/
inductive RufErreichbarW (P : Programm D) (O : Orakel D) (passes : Nat) (ord : D.Glob → Ordnung)
    (W0 : RufMaschineW D) : RufMaschineW D → Prop where
  | start : RufErreichbarW P O passes ord W0 W0
  | schritt (W W' : RufMaschineW D) (u : Faden) :
      RufErreichbarW P O passes ord W0 W → RufSchrittW P O passes ord W u W' →
        RufErreichbarW P O passes ord W0 W'


end Gabbro.Grammatik
