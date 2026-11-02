module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiG
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}


/-! ## 3. The trace invariant over every reachable machine -/

/-- **The trace invariant**: every thread trace is consistent and every
    access event on it is good. -/
def SpurInv (M : RufMaschineG D) : Prop :=
  ∀ t : Faden, Konsistent (M.faeden t).spur ∧
    ∀ e ∈ (M.faeden t).spur, e.istZugriff = true → e.gut

theorem nimmtAlle_inv : ∀ (Ls : List D.Lock) (s : List (Ereignis D)), Konsistent s →
    Konsistent (nimmtAlle Ls s) ∧ ∀ e ∈ nimmtAlle Ls s, e ∈ s ∨ e.istZugriff = false
  | [], s, hk => ⟨hk, fun e he => Or.inl he⟩
  | L :: Ls, s, hk => by
      obtain ⟨hk', hm⟩ := nimmtAlle_inv Ls (Ereignis.nimmt L (offen s) :: s)
        (konsistent_cons rfl hk)
      refine ⟨hk', fun e he => ?_⟩
      rcases hm e he with he | he
      · rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr rfl
        · exact Or.inl he
      · exact Or.inr he

theorem start_spur (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
  show (match init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
        Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).spur = startSpur (init t).1
  cases init t
  rfl

theorem spurInv_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) : SpurInv (RufStartG P sp init) := by
  intro t
  rw [start_spur]
  obtain ⟨hk, hm⟩ := nimmtAlle_inv (D.haelt (init t).1) [] konsistent_nil
  refine ⟨hk, fun e he hz => ?_⟩
  rcases hm e he with he | he
  · exact absurd he List.not_mem_nil
  · rw [he] at hz; cases hz

theorem spurInv_schritt {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (hI : SpurInv M) : SpurInv M' := by
  intro t
  by_cases ht : t = f
  · subst ht
    obtain ⟨hk, hg⟩ := hI t
    rcases schritt_delta hO hs with ⟨X, e, hX, hK, _, _⟩ | ⟨⟨X, e, hX, hK⟩, _⟩
    · refine ⟨hK hk, fun ev hev hz => ?_⟩
      rw [e] at hev
      rcases List.mem_append.mp hev with hev | hev
      · rcases hX ev hev hz with h | h
        · exact hg ev h hz
        · exact h
      · exact hg ev hev hz
    · refine ⟨hK hk, fun ev hev hz => ?_⟩
      rw [e] at hev
      rcases List.mem_append.mp hev with hev | hev
      · rw [hX ev hev] at hz; cases hz
      · exact hg ev hev hz
  · rw [rufSchrittG_fremd hs t ht]
    exact hI t

theorem spurInv_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) : SpurInv M := by
  induction hr with
  | start => exact spurInv_start P sp init
  | schritt M M' u _ hs ih => exact spurInv_schritt hO hs ih

/-! ## 4. Accesses and the events of one step -/

/-- The events one step of `f` prepended to `f`'s trace (newest first). -/
def ereignisse (M M' : RufMaschineG D) (f : Faden) : List (Ereignis D) :=
  (M'.faeden f).spur.take ((M'.faeden f).spur.length - (M.faeden f).spur.length)

theorem zugriffe_ereignisse (M M' : RufMaschineG D) (f : Faden) :
    zugriffe M M' f = (ereignisse M M' f).filterMap zugriffVon := by rfl

theorem ereignisse_eq {M M' : RufMaschineG D} {f : Faden} {X : List (Ereignis D)}
    (e : (M'.faeden f).spur = X ++ (M.faeden f).spur) : ereignisse M M' f = X := by
  unfold ereignisse
  rw [e, List.length_append, Nat.add_sub_cancel]
  exact List.take_left

/-- A step ACCESSES the carrier `c`: it records an access event on `c`
    (read or write), or it changes `c` in shared memory. -/
def ZugriffG (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  (∃ w : Bool, (c, w) ∈ zugriffe M M' f) ∨ ¬ TraegerGleich M'.speicher M.speicher c

/-- A step WRITES `c`: it records a write event on `c`, or changes `c`. -/
def SchreibG (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  (c, true) ∈ zugriffe M M' f ∨ ¬ TraegerGleich M'.speicher M.speicher c

/-- A step READS `c`: its read footprint contains `c` (a recorded read
    event, as every `World.lese` of the step records one per carrier). -/
def LiestG (M M' : RufMaschineG D) (f : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  (c, false) ∈ zugriffe M M' f

theorem zugriffVon_some {e : Ereignis D} {c : D.Tab ⊕ D.Glob} {w : Bool}
    (h : zugriffVon e = some (c, w)) :
    (∃ t Λ hh, e = Ereignis.zugriff t w Λ hh ∧ c = Sum.inl t) ∨
      (∃ g Λ hh, e = Ereignis.gzugriff g w Λ hh ∧ c = Sum.inr g) := by
  cases e with
  | zugriff t w' Λ hh =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨t, Λ, hh, rfl, rfl⟩
  | gzugriff g w' Λ hh =>
      simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨g, Λ, hh, rfl, rfl⟩
  | nimmt => simp only [zugriffVon, reduceCtorEq] at h
  | gibt => simp only [zugriffVon, reduceCtorEq] at h
  | fremd => simp only [zugriffVon, reduceCtorEq] at h

/-- Without a `nimmt` in `Y`, a lock open after `Y` was open before. -/
theorem offen_ohne_nimmt (L : D.Lock) : ∀ (Y s : List (Ereignis D)),
    (∀ (L' : D.Lock) (h : List D.Lock), Ereignis.nimmt L' h ∉ Y) → L ∈ offen (Y ++ s) →
      L ∈ offen s
  | [], _, _, h => h
  | e :: Y, s, hY, h => by
      have ih := offen_ohne_nimmt L Y s (fun L' h' hm => hY L' h' (List.mem_cons_of_mem _ hm))
      cases e with
      | zugriff => exact ih (by simpa [offen] using h)
      | gzugriff => exact ih (by simpa [offen] using h)
      | fremd => exact ih (by simpa [offen] using h)
      | nimmt L' h' => exact absurd List.mem_cons_self (hY L' h')
      | gibt M => exact ih (List.mem_of_mem_erase (by simpa [offen] using h))

/-- A lock that leaves the open set across `X` is released in `X`. -/
theorem gibt_aus_offen (L : D.Lock) : ∀ (X s : List (Ereignis D)), L ∈ offen s →
    L ∉ offen (X ++ s) → Ereignis.gibt L ∈ X
  | [], _, h, hn => absurd h hn
  | e :: X, s, h, hn => by
      by_cases hg : Ereignis.gibt L ∈ X
      · exact List.mem_cons_of_mem _ hg
      · have hX : L ∈ offen (X ++ s) := by
          apply Classical.byContradiction
          intro hn'
          exact hg (gibt_aus_offen L X s h hn')
        cases e with
        | zugriff => exact absurd (by simpa [offen] using hX) hn
        | gzugriff => exact absurd (by simpa [offen] using hX) hn
        | fremd => exact absurd (by simpa [offen] using hX) hn
        | nimmt M hm => exact absurd (by simp only [List.cons_append, offen, List.mem_cons, hX, or_true]) hn
        | gibt M =>
            by_cases hM : M = L
            · subst hM; exact List.mem_cons_self
            · exact absurd (by
                simp only [List.cons_append, offen]
                exact (List.mem_erase_of_ne (Ne.symm hM)).mpr hX) hn

/-- A lock that enters the open set across `X` is taken in `X`. -/
theorem nimmt_aus_offen (L : D.Lock) : ∀ (X s : List (Ereignis D)), L ∉ offen s →
    L ∈ offen (X ++ s) → ∃ h, Ereignis.nimmt L h ∈ X
  | [], _, hn, h => absurd h hn
  | e :: X, s, hn, h => by
      by_cases hX : L ∈ offen (X ++ s)
      · obtain ⟨h', hm⟩ := nimmt_aus_offen L X s hn hX
        exact ⟨h', List.mem_cons_of_mem _ hm⟩
      · cases e with
        | zugriff => exact absurd (by simpa [offen] using h) hX
        | gzugriff => exact absurd (by simpa [offen] using h) hX
        | fremd => exact absurd (by simpa [offen] using h) hX
        | nimmt M hm =>
            simp only [List.cons_append, offen, List.mem_cons] at h
            rcases h with rfl | h
            · exact ⟨hm, List.mem_cons_self⟩
            · exact absurd h hX
        | gibt M =>
            simp only [List.cons_append, offen] at h
            exact absurd (List.mem_of_mem_erase h) hX

/-- A recorded access event of a step of `f` on a carrier guarded by `L`:
    `f` holds `L` before the step. The event is good (its `Λ` names `L`, its
    recorded held set contains `L`) and consistent (the recorded held set is
    the open set behind it, inside the delta, which takes no lock). -/
theorem ereignis_haelt {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (hI' : SpurInv M') {c : D.Tab ⊕ D.Glob} {w : Bool} (hz : (c, w) ∈ zugriffe M M' f)
    {L : D.Lock} (hB : Bewacht c L) :
    L ∈ offen (M.faeden f).spur ∧ offen (M'.faeden f).spur = offen (M.faeden f).spur := by
  rw [zugriffe_ereignisse] at hz
  obtain ⟨e, he, hzv⟩ := List.mem_filterMap.mp hz
  have hez : e.istZugriff = true := by
    rcases zugriffVon_some hzv with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, rfl, _⟩ <;> rfl
  rcases schritt_delta hO hs with ⟨X, eX, _, _, hnX, hoff⟩ | ⟨⟨X, eX, hX, _⟩, _⟩
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

/-- **Every access holds the guard, before and after.** A step of `f` on a
    reachable machine that accesses a carrier `c` guarded by `L` (a recorded
    read or write event, or a memory change) holds `L` before the step, and
    the step keeps the held locks. -/
theorem zugriff_haelt {P : Programm D} {O : Orakel D} {passes : Nat} (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hO : GutO O)
    (hex : StartExklusiv init) {M M' : RufMaschineG D} {f : Faden}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hs : RufSchrittG P O passes M f M') {c : D.Tab ⊕ D.Glob} {L : D.Lock} (hB : Bewacht c L)
    (hz : ZugriffG M M' f c) :
    L ∈ offen (M.faeden f).spur ∧ L ∈ offen (M'.faeden f).spur := by
  rcases hz with ⟨w, hw⟩ | hm
  · have hI' := spurInv_erreichbar hO sp init (RufErreichbarG.schritt M M' f hr hs)
    obtain ⟨h1, h2⟩ := ereignis_haelt hO hs hI' hw hB
    exact ⟨h1, by rw [h2]; exact h1⟩
  · have h1 := (rennfrei_g P O passes sp init hO hex M M' f hr hs c L hB hm).1
    rcases schritt_delta hO hs with ⟨_, _, _, _, _, hoff⟩ | ⟨_, hsp⟩
    · exact ⟨h1, by rw [hoff]; exact h1⟩
    · exact absurd (by rw [hsp]; exact traegerGleich_refl _ c) hm


end Gabbro.Grammatik
