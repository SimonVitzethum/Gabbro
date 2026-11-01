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

/-! ## 3. Views grow -/

section Wachsen

variable {ord : D.Glob → Ordnung}

theorem lesesicht_ge (wahl : D.Tab ⊕ D.Glob → NachrichtW D) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) (x : D.Tab ⊕ D.Glob),
      v x ≤ lesesicht ord wahl rs v x
  | [], _, _ => Nat.le_refl _
  | c :: rs, v, x => Nat.le_trans (lesesicht_ge wahl rs v x) (Sicht.verein_links _ _ x)

/-- A carrier read in the list: the view reaches the message read there. -/
theorem lesesicht_mem (wahl : D.Tab ⊕ D.Glob → NachrichtW D) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D) (c : D.Tab ⊕ D.Glob), c ∈ rs →
      ∀ x, beitrag (ordVon ord c) c (wahl c) x ≤ lesesicht ord wahl rs v x
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | c' :: rs, v, c, h, x => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Sicht.verein_rechts _ _ x
      · exact Nat.le_trans (lesesicht_mem wahl rs v c h x) (Sicht.verein_links _ _ x)

/-- The view after reads stays below a bound that bounds the view and every contribution. -/
theorem lesesicht_le (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (T : D.Tab ⊕ D.Glob → Nat) :
    ∀ (rs : List (D.Tab ⊕ D.Glob)) (v : SichtW D), (∀ x, v x ≤ T x) →
      (∀ c ∈ rs, ∀ x, beitrag (ordVon ord c) c (wahl c) x ≤ T x) →
      ∀ x, lesesicht ord wahl rs v x ≤ T x
  | [], _, hv, _, x => hv x
  | c :: rs, v, hv, hb, x => by
      show max (lesesicht ord wahl rs v x) (beitrag (ordVon ord c) c (wahl c) x) ≤ T x
      exact Nat.max_le.mpr ⟨lesesicht_le wahl T rs v hv (fun c' h => hb c' (List.mem_cons_of_mem _ h)) x,
        hb c List.mem_cons_self x⟩

theorem locksicht_ge (ls : D.Lock → SichtW D) :
    ∀ (Ls : List D.Lock) (v : SichtW D) (x : D.Tab ⊕ D.Glob), v x ≤ locksicht ls Ls v x
  | [], _, _ => Nat.le_refl _
  | _ :: Ls, v, x => Nat.le_trans (locksicht_ge ls Ls v x) (Sicht.verein_links _ _ x)

theorem locksicht_mem (ls : D.Lock → SichtW D) :
    ∀ (Ls : List D.Lock) (v : SichtW D) (L : D.Lock), L ∈ Ls →
      ∀ x, ls L x ≤ locksicht ls Ls v x
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | L' :: Ls, v, L, h, x => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Sicht.verein_rechts _ _ x
      · exact Nat.le_trans (locksicht_mem ls Ls v L h x) (Sicht.verein_links _ _ x)

theorem locksicht_le (ls : D.Lock → SichtW D) (T : D.Tab ⊕ D.Glob → Nat) :
    ∀ (Ls : List D.Lock) (v : SichtW D), (∀ x, v x ≤ T x) → (∀ L ∈ Ls, ∀ x, ls L x ≤ T x) →
      ∀ x, locksicht ls Ls v x ≤ T x
  | [], _, hv, _, x => hv x
  | L :: Ls, v, hv, hL, x => by
      show max (locksicht ls Ls v x) (ls L x) ≤ T x
      exact Nat.max_le.mpr ⟨locksicht_le ls T Ls v hv (fun L' h => hL L' (List.mem_cons_of_mem _ h)) x,
        hL L List.mem_cons_self x⟩

/-- The view before the writes is at least the old view. -/
theorem vorSicht_ge (W : RufMaschineW D) (u : Faden) (σ : Speicher D) (M'' : RufMaschineG D)
    (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (x : D.Tab ⊕ D.Glob) :
    W.sicht u x ≤ vorSicht ord W u σ M'' wahl x :=
  Nat.le_trans (lesesicht_ge wahl _ _ x) (locksicht_ge _ _ _ x)

/-- **Views only grow**: the acting thread's view after a step is at least the one before. -/
theorem sicht_waechst {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (t : Faden) (x : D.Tab ⊕ D.Glob) : W.sicht t x ≤ W'.sicht t x := by
  by_cases ht : t = u
  · subst ht
    have hv := vorSicht_ge (ord := ord) W t σ M'' wahl x
    by_cases hw : SchreibG (mitSpeicher W.g σ) M'' t x
    · rw [h.sichtS x hw]
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt hv (h.frisch x hw).1)
    · rw [h.sichtU x hw]; exact hv
  · rw [h.sichtF t ht]; exact Nat.le_refl _

/-- The view after a step is at least the view before the writes. -/
theorem vor_le_nach {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (x : D.Tab ⊕ D.Glob) : vorSicht ord W u σ M'' wahl x ≤ W'.sicht u x := by
  by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u x
  · rw [h.sichtS x hw]; exact Nat.le_of_lt (h.frisch x hw).1
  · rw [h.sichtU x hw]; exact Nat.le_refl _

/-- A carrier the step reads is in its read list. -/
theorem lesenVon_mem {M M' : RufMaschineG D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    (h : LiestG M M' u c) : c ∈ lesenVon M M' u :=
  List.mem_filterMap.mpr ⟨(c, false), h, rfl⟩

/-- **Coherence of a read, on EVERY program** (by construction of W): the message a step
    reads at `c` lies at or above the reader's view, and afterwards the reader's view has
    reached it -- so a later read of `c` by the same thread never returns an older message
    (CoRR), nor one older than its own write (CoWR). -/
theorem schrittW_kohaerent {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hl : LiestG (mitSpeicher W.g σ) M'' u c) :
    W.sicht u c ≤ (wahl c).ts ∧ (wahl c).ts ≤ W'.sicht u c := by
  refine ⟨(h.lies c hl).1.2, ?_⟩
  have h1 := lesesicht_mem (ord := ord) wahl _ (W.sicht u) c (lesenVon_mem hl) c
  have h2 := beitrag_selbst (ordVon ord c) c (wahl c)
  exact Nat.le_trans h2 (Nat.le_trans h1 (Nat.le_trans (locksicht_ge _ _ _ c) (vor_le_nach h c)))

/-- **Release/acquire, on EVERY program** (by construction of W): an acquire read (a carrier of
    order `freigabe`) of a message joins the message's view -- for a release write, the writer's
    view at the write -- into the reader's view: every write the writer had seen, the reader
    now sees at least as new. -/
theorem schrittW_erwerb {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hl : LiestG (mitSpeicher W.g σ) M'' u c)
    (ho : ordVon ord c = .freigabe) (x : D.Tab ⊕ D.Glob) : (wahl c).sicht x ≤ W'.sicht u x := by
  have h1 := lesesicht_mem (ord := ord) wahl _ (W.sicht u) c (lesenVon_mem hl) x
  rw [ho] at h1
  exact Nat.le_trans (Sicht.verein_links _ _ x)
    (Nat.le_trans h1 (Nat.le_trans (locksicht_ge _ _ _ x) (vor_le_nach h x)))

theorem lsicht_waechst {P : Programm D} {O : Orakel D} {passes : Nat} {W W' : RufMaschineW D}
    {u : Faden} {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (L : D.Lock) (x : D.Tab ⊕ D.Glob) : W.lsicht L x ≤ W'.lsicht L x := by
  rw [h.lsicht L]
  split
  · exact Sicht.verein_links _ _ x
  · exact Nat.le_refl _

end Wachsen

/-! ## 4. Memories agreeing on every carrier are equal -/

theorem speicher_ext {s s' : Speicher D} (h : ∀ c, TraegerGleich s s' c) : s = s' := by
  cases s with
  | mk sl gl =>
    cases s' with
    | mk sl' gl' =>
      have e1 : sl = sl' := funext fun t => h (.inl t)
      have e2 : gl = gl' := funext fun g => h (.inr g)
      subst e1 e2
      rfl

theorem mitSpeicher_selbst (M : RufMaschineG D) : mitSpeicher M M.speicher = M := by
  cases M; rfl

/-- Not written: the step leaves the carrier as it was. -/
theorem traegerGleich_of_nicht_schreib {M M' : RufMaschineG D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    (h : ¬ SchreibG M M' u c) : TraegerGleich M'.speicher M.speicher c :=
  Classical.byContradiction fun hn => h (Or.inr hn)

theorem traegerGleich_trans {s s' s'' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h1 : TraegerGleich s s' c) (h2 : TraegerGleich s' s'' c) : TraegerGleich s s'' c := by
  cases c
  · exact h1.trans h2
  · exact h1.trans h2

theorem traegerGleich_symm {s s' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h : TraegerGleich s s' c) : TraegerGleich s' s c := by
  cases c
  · exact h.symm
  · exact h.symm

/-- **A step of W whose presented memory is G's own is a step of G**, and its G-part is G's
    successor. -/
theorem schrittW_g {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
    {W W' : RufMaschineW D} {u : Faden} {M'' : RufMaschineG D}
    {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' W.g.speicher M'' wahl neu) :
    RufSchrittG P O passes W.g u M'' ∧ W'.g = M'' := by
  have hs := h.schritt
  rw [mitSpeicher_selbst] at hs
  refine ⟨hs, ?_⟩
  have esp : W'.g.speicher = M''.speicher := speicher_ext fun c => by
    by_cases hw : SchreibG (mitSpeicher W.g W.g.speicher) M'' u c
    · exact h.speicherS c hw
    · have h1 := h.speicherU c hw
      have h2 := traegerGleich_of_nicht_schreib hw
      rw [mitSpeicher_selbst] at h2
      exact traegerGleich_trans h1 (traegerGleich_symm h2)
  have e1 := h.faeden
  have e2 := h.lauf
  have e3 := h.start
  cases hW' : W'.g with
  | mk sp fa la st =>
    cases M'' with
    | mk sp'' fa'' la'' st'' =>
      rw [hW'] at esp e1 e2 e3
      simp only at esp e1 e2 e3
      subst esp e1 e2 e3
      rfl

/-! ## 5. Every run of G is a run of W (`w_aus_g`) -/

section Einbettung

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-- **The SC shape of a W state**: a bound `T` per carrier that a message carrying G's value
    reaches, and that bounds every timestamp and every view. Always writing at `T + 1` and
    reading the message at `T` keeps it. -/
def SCForm (W : RufMaschineW D) : Prop :=
  ∃ T : D.Tab ⊕ D.Glob → Nat, ∀ c,
    (∃ m ∈ W.hist c, m.ts = T c ∧ TraegerGleich W.g.speicher m.wert c) ∧
    (∀ m ∈ W.hist c, m.ts ≤ T c) ∧ (∀ t, W.sicht t c ≤ T c) ∧ (∀ L, W.lsicht L c ≤ T c) ∧
    (∀ x, ∀ m ∈ W.hist x, m.sicht c ≤ T c)

theorem scForm_start (M0 : RufMaschineG D) : SCForm (RufStartW M0) :=
  ⟨fun _ => 0, fun c => ⟨⟨⟨0, M0.speicher, Sicht.null⟩, List.mem_singleton_self _, rfl,
    traegerGleich_refl _ c⟩, fun m hm => by rw [List.mem_singleton.mp hm]; exact Nat.le_refl 0,
    fun _ => Nat.le_refl _,
    fun _ => Nat.le_refl _, fun _ m hm => by rw [List.mem_singleton.mp hm]; exact Nat.le_refl _⟩⟩

theorem beitrag_le {T : D.Tab ⊕ D.Glob → Nat} {o : Ordnung} {c : D.Tab ⊕ D.Glob} {m : NachrichtW D}
    (hts : m.ts ≤ T c) (hs : ∀ x, m.sicht x ≤ T x) (x : D.Tab ⊕ D.Glob) : beitrag o c m x ≤ T x := by
  have heins : Sicht.eins c m.ts x ≤ T x := by
    unfold Sicht.eins
    split
    · rename_i h; subst h; exact hts
    · exact Nat.zero_le _
  cases o
  · exact heins
  · exact Nat.max_le.mpr ⟨hs x, heins⟩

open Classical in
/-- **One G step lifts to a W step** that keeps the SC shape; every write sits right above the
    message read at its carrier (`neu c = ts + 1`: the step is atomic for an RMW, `RMW.lean`). -/
end Einbettung
end Gabbro.Grammatik
