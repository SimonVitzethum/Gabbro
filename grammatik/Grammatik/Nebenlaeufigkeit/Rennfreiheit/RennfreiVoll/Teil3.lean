module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiG
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil2
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil3a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
/-! ## 5. Runs by index, and the ordering through a lock -/

/-- A run of `n` steps from `M0`, by index: machine `ms k`, actor `fs k`. -/
def LaufG (P : Programm D) (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat) : Prop :=
  ms 0 = M0 ∧ ∀ k, k < n → RufSchrittG P O passes (ms k) (fs k) (ms (k + 1))

theorem laufG_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n) : ∀ k, k ≤ n → RufErreichbarG P O passes M0 (ms k)
  | 0, _ => by rw [hl.1]; exact .start
  | k + 1, hk => .schritt _ _ _ (laufG_erreichbar hl k (by omega)) (hl.2 k (by omega))

/-- Two runs glued at the end of the first. -/
theorem laufG_verketten {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms0 ms1 : Nat → RufMaschineG D} {fs0 fs1 : Nat → Faden} {n0 n1 : Nat}
    (h0 : LaufG P O passes M0 ms0 fs0 n0) (h1 : LaufG P O passes (ms0 n0) ms1 fs1 n1) :
    LaufG P O passes M0 (fun k => if k ≤ n0 then ms0 k else ms1 (k - n0))
      (fun k => if k < n0 then fs0 k else fs1 (k - n0)) (n0 + n1) := by
  refine ⟨by simp only [Nat.zero_le, if_true]; exact h0.1, fun k hk => ?_⟩
  dsimp only
  by_cases hk0 : k < n0
  · rw [if_pos (Nat.le_of_lt hk0), if_pos hk0, if_pos (show k + 1 ≤ n0 by omega)]
    exact h0.2 k hk0
  · have e1 : (if k ≤ n0 then ms0 k else ms1 (k - n0)) = ms1 (k - n0) := by
      split
      · have e : k = n0 := by omega
        subst e
        rw [Nat.sub_self]
        exact h1.1.symm
      · rfl
    have e2 : (if k + 1 ≤ n0 then ms0 (k + 1) else ms1 (k + 1 - n0)) = ms1 (k - n0 + 1) := by
      rw [if_neg (by omega)]
      congr 1
      omega
    rw [e1, e2, if_neg hk0]
    exact h1.2 (k - n0) (by omega)

/-- A thread that does not act in a run keeps its state. -/
theorem laufG_fremd {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n) (g : Faden) (hg : ∀ k, k < n → fs k ≠ g) :
    ∀ k, k ≤ n → (ms k).faeden g = M0.faeden g
  | 0, _ => by rw [hl.1]
  | k + 1, hk => by
      rw [rufSchrittG_fremd (hl.2 k (by omega)) g (Ne.symm (hg k (by omega)))]
      exact laufG_fremd hl g hg k (by omega)

/-- The first change of a property along the indices. -/
theorem erster_wechsel (Q : Nat → Prop) : ∀ (b a : Nat), a ≤ b → Q a → ¬ Q b →
    ∃ r, a ≤ r ∧ r < b ∧ Q r ∧ ¬ Q (r + 1)
  | 0, a, hab, hq, hn => by
      have : a = 0 := by omega
      subst this
      exact absurd hq hn
  | b + 1, a, hab, hq, hn => by
      have hab' : a ≤ b := by
        rcases Nat.lt_or_ge b a with h | h
        · have : a = b + 1 := by omega
          subst this
          exact absurd hq hn
        · exact h
      by_cases hb : Q b
      · exact ⟨b, hab', by omega, hb, hn⟩
      · obtain ⟨r, h1, h2, h3, h4⟩ := erster_wechsel Q b a hab' hq hb
        exact ⟨r, h1, by omega, h3, h4⟩

/-- A release of `L` by `f` in the step `M → M'`: held before, not after,
    and the step recorded `gibt L`. -/
def GibtFrei (M M' : RufMaschineG D) (f : Faden) (L : D.Lock) : Prop :=
  L ∈ offen (M.faeden f).spur ∧ L ∉ offen (M'.faeden f).spur ∧ Ereignis.gibt L ∈ ereignisse M M' f

/-- An acquire of `L` by `f` in the step `M → M'`: not held before, held
    after, no other thread held it, and the step recorded `nimmt L`. -/
def NimmtAn (M M' : RufMaschineG D) (f : Faden) (L : D.Lock) : Prop :=
  L ∉ offen (M.faeden f).spur ∧ L ∈ offen (M'.faeden f).spur ∧ RufFreiG M f L ∧
    ∃ h : List D.Lock, Ereignis.nimmt L h ∈ ereignisse M M' f

/-- **Happens-before through the lock `L`**: between the steps `i` and `j`
    the actor of `i` releases `L` at `r` and the actor of `j` acquires it at
    `a`, with `i < r < a < j`. -/
def GeordnetG (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (L : D.Lock) (i j : Nat) : Prop :=
  ∃ r a, i < r ∧ r < a ∧ a < j ∧ fs r = fs i ∧ fs a = fs j ∧
    GibtFrei (ms r) (ms (r + 1)) (fs i) L ∧ NimmtAn (ms a) (ms (a + 1)) (fs j) L

/-- **The ordering through a lock.** On a run from an exclusive start, if
    thread `fs i` holds `L` after its step `i` and thread `fs j ≠ fs i`
    holds `L` before its step `j > i`, then `fs i` releases `L` at some step
    `r` and `fs j` acquires it at some step `a`, with `i < r < a < j`. -/
theorem sperre_ordnet {P : Programm D} {O : Orakel D} {passes : Nat} (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O) (hex : StartExklusiv init)
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes (RufStartG P sp init) ms fs n) (i j : Nat) (hij : i < j)
    (hjn : j < n) (hfg : fs i ≠ fs j) (L : D.Lock)
    (hi : L ∈ offen ((ms (i + 1)).faeden (fs i)).spur)
    (hj : L ∈ offen ((ms j).faeden (fs j)).spur) : GeordnetG ms fs L i j := by
  have hx : ∀ k, k ≤ n → ∀ u v : Faden, u ≠ v → L ∈ offen ((ms k).faeden u).spur →
      L ∉ offen ((ms k).faeden v).spur :=
    fun k hk u v huv hu => exklusivG hO sp init hex (laufG_erreichbar hl k hk) u v huv L hu
  -- the release: the first index after `i` where `fs i` no longer holds `L`
  obtain ⟨r, hr1, hr2, hQr, hQr1⟩ := erster_wechsel
    (fun k => L ∈ offen ((ms k).faeden (fs i)).spur) j (i + 1) (by omega) hi
    (hx j (by omega) (fs j) (fs i) (Ne.symm hfg) hj)
  have hsr := hl.2 r (by omega)
  have hfr : fs r = fs i := by
    apply Classical.byContradiction
    intro hne
    exact hQr1 (by rw [rufSchrittG_fremd hsr (fs i) (Ne.symm hne)]; exact hQr)
  rw [hfr] at hsr
  have hgibt : Ereignis.gibt L ∈ ereignisse (ms r) (ms (r + 1)) (fs i) := by
    rcases schritt_delta hO hsr with ⟨_, _, _, _, _, hoff⟩ | ⟨⟨X, eX, _, _⟩, _⟩
    · exact absurd (by rw [hoff]; exact hQr) hQr1
    · rw [ereignisse_eq eX]
      exact gibt_aus_offen L X _ hQr (by rw [← eX]; exact hQr1)
  -- the acquire: the last index before `j` where `fs j` does not hold `L`
  have hn1 : L ∉ offen ((ms (r + 1)).faeden (fs j)).spur := by
    rw [rufSchrittG_fremd hsr (fs j) (Ne.symm hfg)]
    exact hx r (by omega) (fs i) (fs j) hfg hQr
  obtain ⟨a, ha1, ha2, hQa, hQa1⟩ := erster_wechsel
    (fun k => L ∉ offen ((ms k).faeden (fs j)).spur) j (r + 1) (by omega) hn1
    (fun h => h hj)
  have hQa1' : L ∈ offen ((ms (a + 1)).faeden (fs j)).spur :=
    Classical.byContradiction hQa1
  have hsa := hl.2 a (by omega)
  have hfa : fs a = fs j := by
    apply Classical.byContradiction
    intro hne
    exact hQa (by rw [← rufSchrittG_fremd hsa (fs j) (Ne.symm hne)]; exact hQa1')
  rw [hfa] at hsa
  have hnimmt : ∃ h, Ereignis.nimmt L h ∈ ereignisse (ms a) (ms (a + 1)) (fs j) := by
    rcases schritt_delta hO hsa with ⟨_, _, _, _, _, hoff⟩ | ⟨⟨X, eX, _, _⟩, _⟩
    · exact absurd (by rw [← hoff]; exact hQa1') hQa
    · rw [ereignisse_eq eX]
      exact nimmt_aus_offen L X _ hQa (by rw [← eX]; exact hQa1')
  have hfrei : RufFreiG (ms a) (fs j) L := by
    intro u hu
    rw [← rufSchrittG_fremd hsa u hu]
    exact hx (a + 1) (by omega) (fs j) u (Ne.symm hu) hQa1'
  exact ⟨r, a, by omega, by omega, ha2, hfr, hfa, ⟨hQr, hQr1, hgibt⟩,
    ⟨hQa, hQa1', hfrei, hnimmt⟩⟩

/-! ## 6. The theorem -/

/-- **Data-race freedom on the call machine G, full form (`rennfrei_g_voll`).**
    On every run from `RufStartG P sp init` (good oracle, exclusive start),
    any two accesses by different threads to one carrier `c` guarded by the
    lock `L` -- at steps `i < j`, each a recorded read or write event or a
    memory change -- are ordered through `L`: the first thread releases `L`
    at some step `r`, the second acquires it at some step `a`, with
    `i < r < a < j`. Reads included, any distance; it holds for read/read
    pairs too, so in particular for every pair with at least one write.
    Every premise is used: `hO`/`hex` for the invariant, exclusivity and the
    holder form; `hl` for reachability and the steps; `hij`/`hjn`/`hfg` for
    the ordering; `hB`/`hzi`/`hzj` for the held guard. -/
theorem rennfrei_g_voll (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O) (hex : StartExklusiv init)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat)
    (hl : LaufG P O passes (RufStartG P sp init) ms fs n) (i j : Nat) (hij : i < j)
    (hjn : j < n) (hfg : fs i ≠ fs j) (c : D.Tab ⊕ D.Glob) (L : D.Lock) (hB : Bewacht c L)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (fs i) c)
    (hzj : ZugriffG (ms j) (ms (j + 1)) (fs j) c) : GeordnetG ms fs L i j := by
  have hi := zugriff_haelt sp init hO hex (laufG_erreichbar hl i (by omega)) (hl.2 i (by omega))
    hB hzi
  have hj := zugriff_haelt sp init hO hex (laufG_erreichbar hl j (by omega)) (hl.2 j hjn) hB hzj
  exact sperre_ordnet sp init hO hex hl i j hij hjn hfg L hi.2 hj.1

/-- **A data race** on a run: two accesses by different threads to one
    lock-guarded carrier, at least one a write, the carrier neither an
    atomic global nor a published payload (the lock-free disciplines,
    excluded by their declared discipline as in `SchreibRasse`), and NOT
    ordered through any guard of the carrier. -/
def DatenRasse (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (i j : Nat)
    (c : D.Tab ⊕ D.Glob) : Prop :=
  i < j ∧ fs i ≠ fs j ∧ ZugriffG (ms i) (ms (i + 1)) (fs i) c ∧
    ZugriffG (ms j) (ms (j + 1)) (fs j) c ∧
    (SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) ∧
    ¬ AtomarAusgenommen c ∧ ¬ PaarungAusgenommen c ∧ (∃ L : D.Lock, Bewacht c L) ∧
    ∀ L : D.Lock, Bewacht c L → ¬ GeordnetG ms fs L i j

/-- **No data race on a lock-guarded carrier** (`keine_datenrasse_g`), on
    every run from an exclusive start with a good oracle. The write and the
    lock-free exclusions of `DatenRasse` travel unused: the ordering holds
    for every pair of accesses. -/
theorem keine_datenrasse_g (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O) (hex : StartExklusiv init)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat)
    (hl : LaufG P O passes (RufStartG P sp init) ms fs n) (i j : Nat) (hjn : j < n)
    (c : D.Tab ⊕ D.Glob) : ¬ DatenRasse ms fs i j c := by
  rintro ⟨hij, hfg, hzi, hzj, _, _, _, ⟨L, hB⟩, hno⟩
  exact hno L hB (rennfrei_g_voll P O passes sp init hO hex ms fs n hl i j hij hjn hfg c L hB
    hzi hzj)

/-! ## CUTS:

  What is proved: the trace delta of every step rule (`schritt_delta`: an
  access step takes no lock, keeps the held set and adds only good access
  events; a lock step adds only lock events and keeps memory); the trace
  invariant on every reachable machine (`spurInv_erreichbar`); the guard
  holding of every access, read or write, before and after the step
  (`zugriff_haelt`); the ordering through a lock over run indices
  (`sperre_ordnet`, release `gibt L` by the first thread and acquire
  `nimmt L` by the second, strictly between the two accesses); the
  full-form theorem `rennfrei_g_voll` (every pair of accesses by different
  threads to a lock-guarded carrier, reads included, any distance) and
  `keine_datenrasse_g` (no pair with at least one write is unordered). The
  joint witness is `rennfrei_g_voll_zeuge` (`TravAwaitsLauf.lean`): a write
  at step 16 and a read at step 24 by different threads.

  What the access notion covers: every read the semantics performs through
  `World.lese` (expressions, arguments, conditions, loop heads, `awaits`,
  `exchange`, returns) and every write (slot/global/byte writes, publish,
  transition, exchange, the axiom's recorded `axiomSpur` writes), and every
  memory change. The accesses to a carrier are ordered for EVERY lock guard
  of it.

  What is NOT covered, precisely:
  * reads by the ORACLE: an axiom's `O.wirkt`, a register read's
    `O.regLies` and an `awaits`'s visibility answer `O.sichtbar` may depend
    on memory without recording a read event; they are hardware, not
    program accesses (`RegLokal` bounds the register and visibility answers
    to the declared carriers, it records nothing);
  * carriers without a lock guard: `atomic` globals (ordered by the machine,
    A10), published payloads (ordered by the publish/awaits pairing), and
    unshared carriers (`D.geteilt = false`, guarded by an owner mark or by
    nothing: one thread's own state, W5 of `Gesittet`, a checker duty) --
    for those the theorem has no premise `Bewacht c L` to start from, and
    the ownership ordering (single-thread marks) is not proved on G here.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.schritt_delta
#print axioms Gabbro.Grammatik.rennfrei_g_voll
#print axioms Gabbro.Grammatik.keine_datenrasse_g
