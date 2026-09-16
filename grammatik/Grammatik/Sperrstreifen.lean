/-
  File:      Grammatik/Sperrstreifen.lean
  Subject:   **A LOCK CHOSEN BY THE DATA** -- what `Held(L[i])` would have to mean, and
             why striping the TABLES is the only honest answer at this granularity.

  THE QUESTION, from outside this tree.  `/home/ubuntu/brandmauer` writes a firewall in
  Gabbro.  Its connection table is 1024 buckets x 4 slots, and every worker thread hits it
  on every packet.  `messung/BEFUNDE-bm3.md` F6 records that per-bucket-group locks could
  not be written, and names the upgrade path it could not take: *stripe the TABLES, not the
  locks.*  This file answers WHY, in the model, and not by taste.

  THE MODEL'S ANSWER, in one sentence: **`darf` is CONJUNCTIVE** (Syntax.lean:244,
  `darf t Λ = ∀ w ∈ D.braucht t, Res.von D w ∈ Λ`), so a carrier with N guard locks needs
  all N in hand at EVERY access.  `Held(L[i])` at the granularity of a carrier therefore
  cannot mean "one of the N"; the conjunction makes it mean ALL of them, and N locks over
  one table are strictly WORSE than one -- more takes, more ranks, the same exclusion.

  WHAT IS PROVED HERE.

  1. `zugriff_haelt_jeden_waechter` -- every good access event to a carrier records EVERY
     guard lock of that carrier as really held.  From `Ereignis.gut` (Satz.lean:263) alone.
  2. `ziel_haelt_jeden_waechter` -- the same over the CONCLUSION of the goal theorem: on
     every reachable machine of an accepted program, `Ziel.speicherSicher` (`SpurInv`)
     forces it.  This is the sentence "`Held(L[i])` would have to mean `Held` of all the
     `L[j]`" stated where it has to hold: inside `gabbro_ziel`.
  3. `streifensperren_kosten_alle` -- for a carrier with TWO guards, both are held at every
     access.  F6, as a theorem.
  4. The two concrete declarations, non-degenerate (real tables, real locks, distinct):
     * `grobD` -- ONE table, TWO locks (the shape "stripe the locks"):
       `grob_eine_reicht_nicht` says holding one is not enough,
       `grob_braucht_beide` says both together are.
     * `strD` -- TWO tables, TWO locks, one each (the shape "stripe the tables"):
       `streifen_getrennt` says holding lock 0 admits stripe 0 and NOT stripe 1 --
       the disjointness that is the parallelism, and
       `streifen_waechter_disjunkt` says no lock guards both stripes, so the `∃ L` of
       `RennfreiBis` never has to be met ACROSS stripes;
       `streifen_sperrInvOk` says the striped lock family is well-formed
       (`SperrInvOk`, SperreSem.lean:53), i.e. the checker component `sperrOrte`
       (Zielsatz/Akzeptiert.lean) is satisfiable on it.
  5. `gleicher_rang_kein_zweiter` / `streifen_nur_eine_richtung` -- the price nobody writes
     down: with EQUAL ranks no ONE thread may hold two stripe locks (`Ereignis.gut` of a
     `.nimmt` demands a STRICT rank rise, `H006`).  The packet path is fine either way (it
     takes exactly one), but a sweep over all stripes must take them ONE AFTER THE OTHER,
     or the stripes need distinct ranks -- and then the nesting has exactly one direction.

  AXIOMS, measured: `#print axioms gabbro_ziel` is unchanged, the standard three; every
  theorem here depends on `propext` alone, except `ziel_haelt_jeden_waechter`, which
  inherits the goal theorem's three through `Ziel`.

  WHAT IS *NOT* CLAIMED.  That a sub-carrier granularity is impossible in principle -- only
  that it is not expressible in THIS `Deklaration`.  `Bewacht` (InterferenzAllgemein:1350),
  `darf`, `SperrInv.orte`, `TraegerSchreibt`, `fussOrteG`, `SchreibGetrennt` and
  `ZugriffG` all key on `c : D.Tab ⊕ D.Glob`, and `Expr.slot t f i hL` carries
  `hL : darf D t Λ` beside a RUNTIME index `i` -- the guard witness is part of the typing
  derivation and cannot depend on `i`'s value.  Making `Held(L[i])` mean "the region `i`"
  would move the unit of race freedom from the carrier to a region, i.e. change
  `Deklaration` and every leg of `Ziel` that quantifies a carrier.  That is a different
  model, not a rule; the header of `Zielsatz/Spec.lean` would have to be rewritten for it.
-/
import Grammatik.Zielsatz.Spec

namespace Gabbro.Grammatik.Sperrstreifen

open Gabbro.Grammatik

/-! ## 1. The conjunctive guard -- the wall, in general -/

variable {D : Deklaration}

/-- **Every guard of a carrier is really held at every good access to it.**
    `Ereignis.gut (.zugriff t w Λ h)` is `darf D t Λ ∧ HeldIn Λ h`: the static hand `Λ`
    carries every watch entry of `t` (`darf`, Syntax.lean:244 -- a ∀, not an ∃), and every
    lock `Λ` names is in the dynamically held list `h` (`HeldIn`, Satz.lean:214).  So for a
    table guarded by `L₀ … Lₙ`, an access holds ALL of them -- there is no "one of". -/
theorem zugriff_haelt_jeden_waechter {t : D.Tab} {w : Bool} {Λ : List (Res D)}
    {h : List D.Lock} (hg : Ereignis.gut (D := D) (.zugriff t w Λ h))
    {L : D.Lock} (hL : Bewacht (D := D) (.inl t) L) : L ∈ h :=
  hg.2 L (hg.1 (Sum.inl L) hL)

/-- The same for a global (`gdarf`/`gbraucht`). -/
theorem gzugriff_haelt_jeden_waechter {g : D.Glob} {w : Bool} {Λ : List (Res D)}
    {h : List D.Lock} (hg : Ereignis.gut (D := D) (.gzugriff g w Λ h))
    {L : D.Lock} (hL : Bewacht (D := D) (.inr g) L) : L ∈ h :=
  hg.2 L (hg.1 (Sum.inl L) hL)

/-- **F6, as a theorem.** Two guards over ONE carrier are not an alternative: every access
    holds both.  Striping the locks of a table buys no parallelism -- it buys a second take
    on the same path.  (`/home/ubuntu/brandmauer` `messung/BEFUNDE-bm3.md` F6.) -/
theorem streifensperren_kosten_alle {t : D.Tab} {w : Bool} {Λ : List (Res D)}
    {h : List D.Lock} (hg : Ereignis.gut (D := D) (.zugriff t w Λ h)) {L₀ L₁ : D.Lock}
    (h₀ : Bewacht (D := D) (.inl t) L₀) (h₁ : Bewacht (D := D) (.inl t) L₁) :
    L₀ ∈ h ∧ L₁ ∈ h :=
  ⟨zugriff_haelt_jeden_waechter hg h₀, zugriff_haelt_jeden_waechter hg h₁⟩

/-- The static half on its own: a hand that admits an access to `t` names every guard of
    `t`.  This is what a signature `requires Held(…)` would have to establish, and why a
    signature naming ONE of N stripe locks cannot establish it. -/
theorem darf_verlangt_jeden_waechter {t : D.Tab} {Λ : List (Res D)} (hd : darf D t Λ)
    {L : D.Lock} (hL : Bewacht (D := D) (.inl t) L) : Res.held L ∈ Λ :=
  hd (Sum.inl L) hL

/-! ## 2. The same, over the conclusion of the goal theorem -/

/-- **`Held(L[i])` inside `gabbro_ziel`.** `Ziel.speicherSicher` is `SpurInv M`
    (RennfreiVoll.lean:249): every recorded access on every thread trace is `gut`.  So on
    every machine the goal theorem reaches, every recorded access to a carrier carries
    EVERY guard lock of that carrier as really held.

    That is the answer to "what would `Held(L[i])` have to mean for the goal theorem to
    still hold?": at this granularity it would have to mean `Held(L[0]) ∧ … ∧ Held(L[N-1])`
    -- the conjunction, not a choice.  A rule that let a signature name ONE stripe lock and
    an access to the whole table proceed would falsify this leg. -/
theorem ziel_haelt_jeden_waechter {P : Programm D} {S : SperrInv D} {O : Orakel D}
    {passes : Nat} {M0 M : RufMaschineG D}
    (hZ : Zielsatz.Ziel P S O passes M0 M) (t : Faden)
    {tab : D.Tab} {w : Bool} {Λ : List (Res D)} {h : List D.Lock}
    (he : Ereignis.zugriff (D := D) tab w Λ h ∈ (M.faeden t).spur)
    {L : D.Lock} (hL : Bewacht (D := D) (.inl tab) L) : L ∈ h :=
  zugriff_haelt_jeden_waechter ((hZ.speicherSicher t).2 _ he rfl) hL

/-! ## 3. Two declarations, side by side

    The smallest pair that tells the two shapes apart.  Both have two locks of rank 0 and
    no globals, marks, axioms, registers or invariants; they differ ONLY in how the tables
    and the guards are cut. -/

/-- The one function both declarations carry: it holds both locks and writes. -/
def spSig : Signatur Unit Empty Bool Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [false, true]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The same signature over a two-table declaration. -/
def stSig : Signatur Bool Empty Bool Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [false, true]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- **COARSE-STRIPED: one table, TWO locks.** The shape F6 considered and rejected --
    `braucht () = [S₀, S₁]`. -/
def grobD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 3
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Bool
  decLock := inferInstance
  rang := fun L => if L then 1 else 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl false, .inl true]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => spSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ _ => List.cons_ne_nil _ _
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- **STRIPED TABLES: two tables, two locks, one each.** The shape F6 named as the upgrade
    path -- `braucht t = [S t]`. -/
def strD : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 3
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some false | 1 => some true | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Bool
  decLock := inferInstance
  rang := fun L => if L then 1 else 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun t => [.inl t]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => stSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ _ => List.cons_ne_nil _ _
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-! ### The coarse-striped table: one lock is not enough, both are -/

/-- Injectivity of the lock witness, used by every non-membership below. -/
private theorem held_inj {L M : D.Lock}
    (e : Res.held (D := D) L = Res.held (D := D) M) : L = M := by
  injection e

/-- The one table of `grobD` is guarded by BOTH locks. -/
theorem grob_bewacht (L : grobD.Lock) : Bewacht (D := grobD) (.inl ()) L := by
  cases L
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

/-- Both locks really guard the one table (non-degeneracy: the two guards are DISTINCT). -/
theorem grob_zwei_waechter :
    Bewacht (D := grobD) (.inl ()) false ∧ Bewacht (D := grobD) (.inl ()) true ∧
      (false : grobD.Lock) ≠ true :=
  ⟨grob_bewacht false, grob_bewacht true, fun e => Bool.noConfusion e⟩

/-- **Holding ONE of the two stripe locks does not admit the access.** This is exactly the
    refusal `H007` prints on `.gab` source and the reason F6 gives: a signature naming one
    stripe lock cannot cover a table that names two. -/
theorem grob_eine_reicht_nicht : ¬ darf grobD () [Res.held (D := grobD) false] := by
  intro h
  have hm : Res.held (D := grobD) true ∈ [Res.held (D := grobD) false] :=
    h (Sum.inl true) (grob_bewacht true)
  exact Bool.noConfusion (held_inj (List.mem_singleton.mp hm))

/-- And symmetrically for the other one -- so neither stripe lock alone is a guard. -/
theorem grob_andere_reicht_auch_nicht : ¬ darf grobD () [Res.held (D := grobD) true] := by
  intro h
  have hm : Res.held (D := grobD) false ∈ [Res.held (D := grobD) true] :=
    h (Sum.inl false) (grob_bewacht false)
  exact Bool.noConfusion (held_inj (List.mem_singleton.mp hm))

/-- **Both together admit it.** So `Held(L[i])` over ONE carrier collapses to the
    conjunction: N stripe locks on one table are N takes on every packet path, not one. -/
theorem grob_braucht_beide :
    darf grobD () [Res.held (D := grobD) false, Res.held (D := grobD) true] := by
  intro w hw
  match w, hw with
  | Sum.inl false, _ => exact List.Mem.head _
  | Sum.inl true, _ => exact List.Mem.tail _ (List.Mem.head _)
  | Sum.inr m, _ => exact nomatch m

/-! ### The striped tables: disjoint guards, disjoint hands -/

/-- Each stripe of `strD` is guarded by its own lock, and by that one only. -/
theorem streifen_bewacht (t : strD.Tab) : Bewacht (D := strD) (.inl t) t :=
  List.Mem.head _

/-- **The parallelism, as a fact about hands.** A thread holding only lock `false` may
    touch stripe `false` and may NOT touch stripe `true` -- and symmetrically.  Two threads
    with these two hands are both admitted, at the same time, on different carriers.  That
    is what striping the tables buys, and it needs no new rule. -/
theorem streifen_darf (t : strD.Tab) : darf strD t [Res.held (D := strD) t] := by
  intro w hw
  have e : w = Sum.inl t := List.mem_singleton.mp hw
  subst e
  exact List.Mem.head _

theorem streifen_fremd (t u : strD.Tab) (hne : t ≠ u) :
    ¬ darf strD u [Res.held (D := strD) t] := by
  intro h
  have hm : Res.held (D := strD) u ∈ [Res.held (D := strD) t] :=
    h (Sum.inl u) (streifen_bewacht u)
  exact hne (held_inj (List.mem_singleton.mp hm)).symm

/-- The four facts together: lock `false` admits stripe `false` and refuses stripe `true`,
    and the other way round.  Two threads, two hands, two carriers, at the same time. -/
theorem streifen_getrennt :
    darf strD false [Res.held (D := strD) false] ∧
      ¬ darf strD true [Res.held (D := strD) false] ∧
      darf strD true [Res.held (D := strD) true] ∧
      ¬ darf strD false [Res.held (D := strD) true] :=
  ⟨streifen_darf false, streifen_fremd false true (fun e => Bool.noConfusion e),
   streifen_darf true, streifen_fremd true false (fun e => Bool.noConfusion e)⟩

/-- **No lock guards both stripes.**  `RennfreiBis` demands `∃ L, Bewacht c L ∧ GeordnetG …`
    for two cross-thread accesses to ONE carrier `c`.  Since the guard sets of the two
    stripes are disjoint, no obligation ever relates them: accesses to different stripes are
    accesses to different `c`, and the premise of the race leg is never met. -/
theorem streifen_waechter_disjunkt (L : strD.Lock) :
    ¬ (Bewacht (D := strD) (.inl false) L ∧ Bewacht (D := strD) (.inl true) L) := by
  rintro ⟨h₀, h₁⟩
  have e₀ : Sum.inl L = Sum.inl (false : strD.Tab) :=
    List.mem_singleton.mp (h₀ : Sum.inl L ∈ [Sum.inl (false : strD.Tab)])
  have e₁ : Sum.inl L = Sum.inl (true : strD.Tab) :=
    List.mem_singleton.mp (h₁ : Sum.inl L ∈ [Sum.inl (true : strD.Tab)])
  have : (false : strD.Tab) = true := by
    have := e₀.symm.trans e₁
    exact Sum.inl.inj this
  exact Bool.noConfusion this

/-- The striped lock family: each lock protects exactly its own stripe. -/
def strS : SperrInv strD where
  orte := fun L => [.inl L]
  inv := fun _ _ => true

/-- **The striped family is well formed** (`SperrInvOk`, SperreSem.lean:53): every protected
    carrier is guarded by its lock, and the invariant reads only those carriers.  The first
    half is the checker component `sperrOrte` of `AkzeptiertSpec` (Zielsatz/Spec.lean:465),
    so the striped shape is admissible for `gabbro_ziel` with no change to the statement. -/
theorem streifen_sperrInvOk : SperrInvOk strS := by
  refine ⟨?_, fun _ _ _ _ => rfl⟩
  intro L c hc
  have e : c = Sum.inl L := List.mem_singleton.mp hc
  subst e
  exact streifen_bewacht L

/-- And the coarse-striped family is well formed too -- which is the point: the model does
    not FORBID two locks on one carrier, it makes them cost both.  `SperrInvOk` is not the
    obstruction; `darf` is. -/
def grobS : SperrInv grobD where
  orte := fun _ => [.inl ()]
  inv := fun _ _ => true

theorem grob_sperrInvOk : SperrInvOk grobS := by
  refine ⟨?_, fun _ _ _ _ => rfl⟩
  intro L c hc
  have e : c = Sum.inl () := List.mem_singleton.mp hc
  subst e
  exact grob_bewacht L

/-! ## 4. The price of equal ranks -/

/-- **One thread cannot hold two locks of equal rank.** `Ereignis.gut` of a `.nimmt`
    demands a STRICT rank rise over everything already held (`H006`, Satz.lean:267).  Two
    stripes of the same rank are therefore mutually exclusive FOR ONE THREAD -- which is
    exactly right for the packet path (it takes exactly one) and is the reason a sweep over
    all stripes must take them one after the other, or the stripes need distinct ranks.

    Stated on a rank-equal pair: with `rang L = rang M`, no good `.nimmt` of `L` exists
    while `M` is held. -/
theorem gleicher_rang_kein_zweiter {L M : D.Lock} (hr : D.rang L = D.rang M)
    {h : List D.Lock} (hM : M ∈ h) : ¬ Ereignis.gut (D := D) (.nimmt L h) := by
  rintro ⟨hlt, -⟩
  have h1 : D.rang M < D.rang L := hlt M hM
  rw [hr] at h1
  exact Int.lt_irrefl _ h1

/-- The same on the striped declaration, where the two stripe locks are declared at
    ranks `0` and `1`: a thread holding stripe lock `false` (rank 0) may still take stripe
    lock `true` (rank 1), but not the other way round.  A sweep over the stripes has ONE
    admissible nesting order, and the packet path -- which takes exactly one -- has none to
    obey.  (Non-degenerate: the witness is a real held list.) -/
theorem streifen_nur_eine_richtung :
    Ereignis.gut (D := strD) (.nimmt true [false]) ∧
      ¬ Ereignis.gut (D := strD) (.nimmt false [true]) := by
  constructor
  · refine ⟨?_, ?_⟩
    · intro M hM
      have e : M = false := List.mem_singleton.mp hM
      subst e
      show (0 : Int) < 1
      decide
    · intro hin
      exact Bool.noConfusion (List.mem_singleton.mp hin)
  · rintro ⟨hlt, -⟩
    have h1 : strD.rang true < strD.rang false := hlt true (List.Mem.head _)
    have h2 : (1 : Int) < 0 := h1
    exact absurd h2 (by decide)

end Gabbro.Grammatik.Sperrstreifen
