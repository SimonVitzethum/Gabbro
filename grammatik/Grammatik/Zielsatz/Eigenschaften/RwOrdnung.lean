/-
  File:      Grammatik/Zielsatz/Eigenschaften/RwOrdnung.lean
  Subject:   THE READER/WRITER LOCK, STEP THREE: DATA-RACE FREEDOM and the VISIBILITY of a held
             lock over the layer (`RwSchritt.lean`).

  The discipline of the lock (a premise, named): `LeserLos` -- a thread that takes `L` shared never
  writes a carrier `L` guards. In the final language the checker derives it from the effect of the
  reader's section (a function whose signature writes the carrier cannot be called from a shared
  section); in the layer it is the premise on the run, exactly as `KernPlan`/`masken` were for the mask.

  PROVED (every theorem: `propext`, `Classical.choice`, `Quot.sound` at most; the layer's own steps
  are machine G's, so the access facts of G transfer through `rwSchritt_delta`):
  * `spurInv_rw_lauf`, `zugriff_haelt_rw` -- every access (a recorded event or a change of memory)
    to a carrier guarded by `L` is made by a thread that holds `L`, before and after the step.
  * `sperre_ordnet_rw` -- THE ORDER THROUGH THE LOCK. If thread `fs i` holds `L` after its step `i` and a
    different thread `fs j` holds it before its step `j > i`, and one of the two is a writer of `L`,
    then `fs i` releases `L` at some `r` and `fs j` acquires it at some `a`, `i < r < a < j`
    (`GeordnetRw`). Two readers need no order and get none: exactly the pair the hypothesis excludes.
  * `rennfrei_rw`, `rennfreiRw_aus` -- NO WRITE-WRITE AND NO WRITE-READ RACE on a guarded carrier:
    any two accesses by different threads, one a write, are ordered through the guard. (Read-read
    pairs are not conflicting.) The leg in the shape of `RennfreiBis`.
  * `rwSicht_schritt` -- THE `sperrSicht` OF A SHARED LOCK. A step accesses a carrier guarded by `L` only
    if its thread holds `L`; and while ANY other thread holds `L` -- as a reader or as the writer -- no
    step changes that carrier. A reader's section therefore sees what the writers' sections left.

  NOT CLAIMED: the weak-memory leg (`SchwachSC`) over the layer (the release/acquire edges of a
  reader's acquire and release are those of an exclusive lock's; not re-proved here); starvation
  (a stream of readers can delay a writer forever: the progress leg is machine G's, which names no
  fairness either).
-/
import Grammatik.Zielsatz.Eigenschaften.RwSchritt

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat} {lese : Lese D}

/-! ## 1. The discipline, and the access facts over the layer -/

/-- **Readers write nothing the lock guards**: no step of a thread that takes `L` shared writes a
    carrier guarded by `L` (a recorded write event, or a change of memory). -/
def LeserLos (lese : Lese D) (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat) : Prop :=
  ∀ k, k < n → ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock), Bewacht c L →
    SchreibG (ms k) (ms (k + 1)) (fs k) c → ¬ lese (fs k) L

theorem spurInv_rw_schritt (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RwSchritt P O passes lese M f M') (hI : SpurInv M) : SpurInv M' := by
  rcases hs with h | ⟨L, h⟩
  · exact spurInv_schritt hO h hI
  · obtain ⟨Mh, hg, rfl⟩ := h.schritt
    have hI' : SpurInv (ohneFremde M f) := by
      intro t
      by_cases ht : t = f
      · rw [ht, ohneFremde_self]
        exact hI f
      · have e : (ohneFremde M f).faeden t = { M.faeden t with spur := [] } := by
          simp [ohneFremde, ht]
        rw [e]
        exact ⟨konsistent_nil, fun ev hev => absurd hev List.not_mem_nil⟩
    have h2 := spurInv_schritt hO hg hI'
    intro t
    show Konsistent (rufUpdateG M.faeden f (Mh.faeden f) t).spur ∧
      ∀ e ∈ (rufUpdateG M.faeden f (Mh.faeden f) t).spur, e.istZugriff = true → e.gut
    by_cases ht : t = f
    · rw [ht, rufUpdateG_self]
      exact h2 f
    · rw [rufUpdateG_noteq _ _ _ ht]
      exact hI t

theorem spurInv_rw_lauf (hO : GutO O) {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D}
    {fs : Nat → Faden} {n : Nat} (hl : RwLauf P O passes lese M0 ms fs n) (hI0 : SpurInv M0) :
    ∀ k, k ≤ n → SpurInv (ms k)
  | 0, _ => by rw [hl.1]; exact hI0
  | k + 1, hk => spurInv_rw_schritt hO (hl.2 k (by omega)) (spurInv_rw_lauf hO hl hI0 k (by omega))

/-- A layer step changes no carrier whose guard the acting thread does not hold. -/
theorem rwSchritt_traeger (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RwSchritt P O passes lese M f M') (c : D.Tab ⊕ D.Glob)
    (hc : ∃ L, Bewacht c L ∧ L ∉ offen (M.faeden f).spur) :
    TraegerGleich M'.speicher M.speicher c := by
  rcases hs with h | ⟨L, h⟩
  · exact schritt_traeger hO h c (Or.inl hc)
  · rw [rwAcq_speicher hO h]
    exact traegerGleich_refl _ c

/-- **An access event of a layer step holds the guard** (`ereignis_haelt`, over the layer: the proof
    reads the step only through its trace delta). -/
theorem ereignis_haelt_rw (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RwSchritt P O passes lese M f M') (hI' : SpurInv M') {c : D.Tab ⊕ D.Glob} {w : Bool}
    (hz : (c, w) ∈ zugriffe M M' f) {L : D.Lock} (hB : Bewacht c L) :
    L ∈ offen (M.faeden f).spur ∧ offen (M'.faeden f).spur = offen (M.faeden f).spur := by
  rw [zugriffe_ereignisse] at hz
  obtain ⟨e, he, hzv⟩ := List.mem_filterMap.mp hz
  have hez : e.istZugriff = true := by
    rcases zugriffVon_some hzv with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ <;> rfl
  rcases rwSchritt_delta hO hs with ⟨X, eX, _, _, hnX, hoff⟩ | ⟨⟨X, eX, hX, _⟩, _⟩
  · refine ⟨?_, hoff⟩
    rw [ereignisse_eq eX] at he
    obtain ⟨hk, hg⟩ := hI' f
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
    have hget : (M'.faeden f).spur[n]? = some X[n] := by
      rw [eX, List.getElem?_append_left hn]
      exact List.getElem?_eq_getElem hn
    have hp := hk n _ hget
    have hgut := hg X[n] (by rw [eX]; exact List.mem_append_left _ he) hez
    have hdrop : (M'.faeden f).spur.drop (n + 1) = X.drop (n + 1) ++ (M.faeden f).spur := by
      rw [eX]
      exact List.drop_append_of_le_length hn
    have hY : ∀ (L' : D.Lock) (h : List D.Lock), Ereignis.nimmt L' h ∉ X.drop (n + 1) :=
      fun L' h hm => hnX L' h (List.mem_of_mem_drop hm)
    rw [hdrop] at hp
    rcases zugriffVon_some hzv with ⟨t, Λ, hh, e1, rfl⟩ | ⟨g, Λ, hh, e1, rfl⟩
    · rw [e1] at hp hgut
      simp only [Ereignis.passt] at hp
      simp only [Ereignis.gut] at hgut
      have hL : L ∈ hh := hgut.2 L (hgut.1 _ hB)
      rw [hp] at hL
      exact offen_ohne_nimmt L _ _ hY hL
    · rw [e1] at hp hgut
      simp only [Ereignis.passt] at hp
      simp only [Ereignis.gut] at hgut
      have hL : L ∈ hh := hgut.2 L (hgut.1 _ hB)
      rw [hp] at hL
      exact offen_ohne_nimmt L _ _ hY hL
  · rw [ereignisse_eq eX] at he
    rw [hX e he] at hez
    cases hez

/-- **Every access holds the guard, before and after** (`zugriff_haelt`, over the layer). -/
theorem zugriff_haelt_rw (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RwSchritt P O passes lese M f M') (hI' : SpurInv M') {c : D.Tab ⊕ D.Glob} {L : D.Lock}
    (hB : Bewacht c L) (hz : ZugriffG M M' f c) :
    L ∈ offen (M.faeden f).spur ∧ L ∈ offen (M'.faeden f).spur := by
  rcases hz with ⟨w, hw⟩ | hm
  · obtain ⟨h1, h2⟩ := ereignis_haelt_rw hO hs hI' hw hB
    exact ⟨h1, by rw [h2]; exact h1⟩
  · have h1 : L ∈ offen (M.faeden f).spur := by
      refine Classical.byContradiction fun hn => hm ?_
      exact rwSchritt_traeger hO hs c ⟨L, hB, hn⟩
    rcases rwSchritt_delta hO hs with ⟨_, _, _, _, _, hoff⟩ | ⟨_, hsp⟩
    · exact ⟨h1, by rw [hoff]; exact h1⟩
    · exact absurd (by rw [hsp]; exact traegerGleich_refl _ c) hm

/-! ## 2. The order through the lock -/

/-- **Happens-before through the lock `L`** between the steps `i` and `j`: the actor of `i` releases `L`
    at `r` and the actor of `j` acquires it at `a`, with `i < r < a < j`. -/
def GeordnetRw (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (L : D.Lock) (i j : Nat) : Prop :=
  ∃ r a, i < r ∧ r < a ∧ a < j ∧ fs r = fs i ∧ fs a = fs j ∧
    (L ∈ offen ((ms r).faeden (fs i)).spur ∧ L ∉ offen ((ms (r + 1)).faeden (fs i)).spur) ∧
    (L ∉ offen ((ms a).faeden (fs j)).spur ∧ L ∈ offen ((ms (a + 1)).faeden (fs j)).spur)

/-- **The order through the lock, with one writer.** `fs i` holds `L` after step `i`, a different thread
    `fs j` holds it before step `j`, and at least one of the two takes `L` exclusively: then `fs i`
    releases `L` and afterwards `fs j` acquires it, both strictly between `i` and `j`. -/
theorem sperre_ordnet_rw (hO : GutO O) {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D}
    {fs : Nat → Faden} {n : Nat} (hl : RwLauf P O passes lese M0 ms fs n) (h0 : RwExkl lese M0)
    (i j : Nat) (hij : i < j) (hjn : j < n) (hfg : fs i ≠ fs j) (L : D.Lock)
    (hi : L ∈ offen ((ms (i + 1)).faeden (fs i)).spur)
    (hj : L ∈ offen ((ms j).faeden (fs j)).spur) (hm : ¬ lese (fs i) L ∨ ¬ lese (fs j) L) :
    GeordnetRw ms fs L i j := by
  have hx : ∀ k, k ≤ n → L ∈ offen ((ms k).faeden (fs i)).spur →
      L ∉ offen ((ms k).faeden (fs j)).spur := by
    intro k hk h1 h2
    have := rwExkl_lauf hO hl h0 k hk (fs i) (fs j) L hfg h1 h2
    rcases hm with hm | hm
    · exact hm this.1
    · exact hm this.2
  have hx' : ∀ k, k ≤ n → L ∈ offen ((ms k).faeden (fs j)).spur →
      L ∉ offen ((ms k).faeden (fs i)).spur := fun k hk h1 h2 => hx k hk h2 h1
  -- the release: the first index after `i` where `fs i` no longer holds `L`
  obtain ⟨r, hr1, hr2, hQr, hQr1⟩ := erster_wechsel
    (fun k => L ∈ offen ((ms k).faeden (fs i)).spur) j (i + 1) (by omega) hi
    (hx' j (by omega) hj)
  have hsr := hl.2 r (by omega)
  have hfr : fs r = fs i := by
    refine Classical.byContradiction fun hne => hQr1 ?_
    rw [rwSchritt_fremd hsr (fs i) (Ne.symm hne)]
    exact hQr
  have hn1 : L ∉ offen ((ms (r + 1)).faeden (fs j)).spur := by
    rw [rwSchritt_fremd hsr (fs j) (by rw [hfr]; exact Ne.symm hfg)]
    exact hx r (by omega) hQr
  -- the acquire: the first index after the release where `fs j` holds `L`
  obtain ⟨a, ha1, ha2, hQa, hQa1⟩ := erster_wechsel
    (fun k => L ∉ offen ((ms k).faeden (fs j)).spur) j (r + 1) (by omega) hn1
    (fun h => h hj)
  have hQa1' : L ∈ offen ((ms (a + 1)).faeden (fs j)).spur := Classical.byContradiction hQa1
  have hsa := hl.2 a (by omega)
  have hfa : fs a = fs j := by
    refine Classical.byContradiction fun hne => hQa ?_
    rw [← rwSchritt_fremd hsa (fs j) (Ne.symm hne)]
    exact hQa1'
  exact ⟨r, a, by omega, by omega, ha2, hfr, hfa, ⟨hQr, hQr1⟩, ⟨hQa, hQa1'⟩⟩

/-! ## 3. No write-write and no write-read race -/

/-- **No race on a guarded carrier** over a layer run. Two accesses by different threads to a carrier
    guarded by `L`, at least one a write, are ordered through `L`. Readers do not write
    (`LeserLos`); the start has no two holders but readers (`RwExkl`) and consistent traces. -/
theorem rennfrei_rw (hO : GutO O) {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D}
    {fs : Nat → Faden} {n : Nat} (hl : RwLauf P O passes lese M0 ms fs n) (h0 : RwExkl lese M0)
    (hI0 : SpurInv M0) (hd : LeserLos lese ms fs n) (i j : Nat) (hij : i < j) (hjn : j < n)
    (hfg : fs i ≠ fs j) (c : D.Tab ⊕ D.Glob) (L : D.Lock) (hB : Bewacht c L)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (fs i) c) (hzj : ZugriffG (ms j) (ms (j + 1)) (fs j) c)
    (hw : SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c) :
    GeordnetRw ms fs L i j := by
  have hS := spurInv_rw_lauf hO hl hI0
  have hi := zugriff_haelt_rw hO (hl.2 i (by omega)) (hS (i + 1) (by omega)) hB hzi
  have hj := zugriff_haelt_rw hO (hl.2 j hjn) (hS (j + 1) (by omega)) hB hzj
  have hm : ¬ lese (fs i) L ∨ ¬ lese (fs j) L := by
    rcases hw with hw | hw
    · exact Or.inl (hd i (by omega) c L hB hw)
    · exact Or.inr (hd j hjn c L hB hw)
  exact sperre_ordnet_rw hO hl h0 i j hij hjn hfg L hi.2 hj.1 hm

/-- **The race leg over the layer, in the shape of `RennfreiBis`**: every pair of conflicting accesses by
    different threads to a carrier that is not an atomic is ordered through a guard of the carrier.
    `hG` is the declaration's fact that a shared carrier has a guard or is an atomic. -/
theorem rennfreiRw_aus (hO : GutO O) {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D}
    {fs : Nat → Faden} {n : Nat} (hl : RwLauf P O passes lese M0 ms fs n) (h0 : RwExkl lese M0)
    (hI0 : SpurInv M0) (hd : LeserLos lese ms fs n)
    (hG : ∀ c : D.Tab ⊕ D.Glob, ¬ AtomarAusgenommen c → ∃ L, Bewacht c L)
    (i j : Nat) (c : D.Tab ⊕ D.Glob) (hij : i < j) (hjn : j < n) (hfg : fs i ≠ fs j)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (fs i) c) (hzj : ZugriffG (ms j) (ms (j + 1)) (fs j) c)
    (hw : SchreibG (ms i) (ms (i + 1)) (fs i) c ∨ SchreibG (ms j) (ms (j + 1)) (fs j) c)
    (hat : ¬ AtomarAusgenommen c) : ∃ L, Bewacht c L ∧ GeordnetRw ms fs L i j := by
  obtain ⟨L, hB⟩ := hG c hat
  exact ⟨L, hB, rennfrei_rw hO hl h0 hI0 hd i j hij hjn hfg c L hB hzi hzj hw⟩

/-! ## 4. The visibility of a held lock -/

/-- **`sperrSicht` of a shared lock.** For a step of the layer run and a carrier `c` guarded by `L`: the
    step accesses `c` only if its thread holds `L`; and while any OTHER thread holds `L`, as a reader
    or as the writer, the step does not change `c`. -/
theorem rwSicht_schritt (hO : GutO O) {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D}
    {fs : Nat → Faden} {n : Nat} (hl : RwLauf P O passes lese M0 ms fs n) (h0 : RwExkl lese M0)
    (hI0 : SpurInv M0) (hd : LeserLos lese ms fs n) (k : Nat) (hk : k < n)
    (c : D.Tab ⊕ D.Glob) (L : D.Lock) (hB : Bewacht c L) :
    (ZugriffG (ms k) (ms (k + 1)) (fs k) c → L ∈ offen ((ms k).faeden (fs k)).spur) ∧
    (∀ t, t ≠ fs k → L ∈ offen ((ms k).faeden t).spur →
      TraegerGleich (ms (k + 1)).speicher (ms k).speicher c) := by
  have hS := spurInv_rw_lauf hO hl hI0
  refine ⟨fun hz => (zugriff_haelt_rw hO (hl.2 k hk) (hS (k + 1) (by omega)) hB hz).1,
    fun t ht hL => ?_⟩
  refine Classical.byContradiction fun hne => ?_
  have hz : SchreibG (ms k) (ms (k + 1)) (fs k) c := Or.inr hne
  have hhold : L ∈ offen ((ms k).faeden (fs k)).spur :=
    (zugriff_haelt_rw hO (hl.2 k hk) (hS (k + 1) (by omega)) hB (Or.inr hne)).1
  have hx := rwExkl_lauf hO hl h0 k (by omega) (fs k) t L (Ne.symm ht) hhold hL
  exact hd k hk c L hB hz hx.1

end Gabbro.Grammatik.Zielsatz

#print axioms Gabbro.Grammatik.Zielsatz.sperre_ordnet_rw
#print axioms Gabbro.Grammatik.Zielsatz.rennfrei_rw
#print axioms Gabbro.Grammatik.Zielsatz.rennfreiRw_aus
#print axioms Gabbro.Grammatik.Zielsatz.rwSicht_schritt
