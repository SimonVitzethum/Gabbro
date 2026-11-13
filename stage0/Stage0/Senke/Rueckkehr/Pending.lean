/-
  File:      stage0/Stage0/Senke/Rueckkehr/Pending.lean
  Subject:   A return under pending releases (lock stage 3). A return from inside `locks` bodies of its own function
              gives those locks on its way out (`retScopedC`); seen from a point inside the bodies its change is not
              an `AgreeW` (whose `TicketKlasse` keeps every lock's next − serving), since every pending lock drops
              from mine to free (`TicketGabe`). `AgreeWR … Hs` is `AgreeW` with that drop for the locks of `Hs`;
              `RetZR`/`RetWhyR` are `RetZ`/`RetWhy` with it, the return outcomes of the simulation (`Sim`, `Ret`)
              under the enclosing scopes of the return site. Under no pending release they are the old relations
              (`AgreeWR.nil`, `RetZR.nil`, `RetWhyR.nil`, and back: `.toR`); an `AgreeW` change before them is
              absorbed (`.prefix`). Moved out of `Sperre/Ticket/Gabe.lean` unchanged, so that the simulation can
              name them.
-/
module
public import Stage0.Senke.Rueckkehr
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- What a give does to the ticket lock at `a`: the words stay readable, next − serving drops by one
    (`n' - s' + 1 = n - s`: mine becomes free), the waiters stay. -/
def TicketGabe (m m' : Mem) (a : Nat) : Prop :=
  ∀ n s w, m.rd64 (BitVec.ofNat 64 a) = some n → m.rd64 (BitVec.ofNat 64 (a + 8)) = some s →
    m.rd64 (BitVec.ofNat 64 (a + 16)) = some w →
    ∃ n' s' w', m'.rd64 (BitVec.ofNat 64 a) = some n' ∧ m'.rd64 (BitVec.ofNat 64 (a + 8)) = some s' ∧
      m'.rd64 (BitVec.ofNat 64 (a + 16)) = some w' ∧ n' - s' + 1 = n - s ∧ w' = w

theorem TicketKlasse.gabe {m1 m2 m3 : Mem} {a : Nat} (h1 : TicketKlasse m1 m2 a) (h2 : TicketGabe m2 m3 a) :
    TicketGabe m1 m3 a := fun n s w e1 e2 e3 => by
  obtain ⟨n1, s1, w1, f1, f2, f3, d1, q1⟩ := h1 n s w e1 e2 e3
  obtain ⟨n2, s2, w2, g1, g2, g3, d2, q2⟩ := h2 n1 s1 w1 f1 f2 f3
  exact ⟨n2, s2, w2, g1, g2, g3, by rw [d2, d1], by rw [q2, q1]⟩

theorem TicketGabe.klasse {m1 m2 m3 : Mem} {a : Nat} (h1 : TicketGabe m1 m2 a) (h2 : TicketKlasse m2 m3 a) :
    TicketGabe m1 m3 a := fun n s w e1 e2 e3 => by
  obtain ⟨n1, s1, w1, f1, f2, f3, d1, q1⟩ := h1 n s w e1 e2 e3
  obtain ⟨n2, s2, w2, g1, g2, g3, d2, q2⟩ := h2 n1 s1 w1 f1 f2 f3
  exact ⟨n2, s2, w2, g1, g2, g3, by rw [d2, d1], by rw [q2, q1]⟩

/-- **A change on the way out under the pending releases `Hs`**: what `AgreeW` allows, except that every lock of
    `Hs` is given (`TicketGabe`) instead of keeping its class. -/
structure AgreeWR (L : Lay D) (fp : W) (lo K : Nat) (Hs : List D.Lock) (m m' : Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ x, ¬ inSlots fp lo K x → ¬ InWelt L x → ¬ InSync L x → m'.b x = m.b x
  sync : ∀ Lk, LockFern L fp lo K (L.lk Lk) → Lk ∉ Hs → TicketKlasse m m' (L.lk Lk)
  gabe : ∀ Lk, LockFern L fp lo K (L.lk Lk) → Lk ∈ Hs → TicketGabe m m' (L.lk Lk)

/-- Under no pending release it is `AgreeW`. -/
theorem AgreeWR.nil {L : Lay D} {fp : W} {lo K : Nat} {m m' : Mem} (h : AgreeWR L fp lo K [] m m') :
    AgreeW L fp lo K m m' :=
  ⟨h.rd, h.wr, h.b, fun Lk fern => h.sync Lk fern List.not_mem_nil⟩

theorem AgreeW.toR {L : Lay D} {fp : W} {lo K : Nat} {m m' : Mem} (h : AgreeW L fp lo K m m') :
    AgreeWR L fp lo K [] m m' :=
  ⟨h.rd, h.wr, h.b, fun Lk fern _ => h.sync Lk fern, fun _ _ hm => (List.not_mem_nil hm).elim⟩

/-- An `AgreeW` change before one under pending releases is absorbed. -/
theorem AgreeW.transR {L : Lay D} {fp : W} {lo K : Nat} {Hs : List D.Lock} {m1 m2 m3 : Mem}
    (h1 : AgreeW L fp lo K m1 m2) (h2 : AgreeWR L fp lo K Hs m2 m3) : AgreeWR L fp lo K Hs m1 m3 :=
  ⟨h2.rd.trans h1.rd, h2.wr.trans h1.wr, fun x hx hw hs => (h2.b x hx hw hs).trans (h1.b x hx hw hs),
    fun Lk fern hn => (h1.sync Lk fern).trans (h2.sync Lk fern hn),
    fun Lk fern hm => (h1.sync Lk fern).gabe (h2.gabe Lk fern hm)⟩

/-- **A normal return under the pending releases `Hs`**: `RetZ` with `AgreeWR … Hs` for its change. -/
def RetZR (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : W) (K : Nat)
    (rp cfp : W) (Hs : List D.Lock) (t : T) (m : Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if returnFault P f σ0 σ' ρ0 v ≠ 0
  then Stops t m (returnFault P f σ0 σ' ρ0 v)
  else ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ AgreeWR L fp 2 K Hs m m' ∧
    (ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
      ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
      ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧
      WeltAt m' L (owedWorld P f (σ'.lese (vertragVon D f).ende (P.ensures f).orte))

/-- **A reason return under the pending releases `Hs`**: `RetWhy` with `AgreeWR … Hs` for its change. -/
def RetWhyR (L : Lay D) (f : D.Fn) (fp : W) (K : Nat) (rp cfp : W) (Hs : List D.Lock)
    (t : T) (m : Mem) (σ : World D) (r : Fin (D.gruende f)) : Prop :=
  ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ AgreeWR L fp 2 K Hs m m' ∧
    ValueAt L m' fp (FB + contextWords (D.params f)) (.why (D.gruende f)) r ∧
    ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
    ReturnFlag m' fp (contextWords (D.params f)) false (returnWords (D.erg f) (D.gruende f)) ∧ WeltAt m' L σ

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : W} {K : Nat}
  {rp cfp : W} {Hs : List D.Lock} {t0 t : T} {m0 m : Mem}

theorem RetZR.nil {σ' : World D} {v : ErgVal D (D.erg f)} (h : RetZR L P f σ0 ρ0 fp K rp cfp [] t m σ' v) :
    RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v := by
  unfold RetZR at h
  unfold RetZ
  by_cases hc : returnFault P f σ0 σ' ρ0 v ≠ 0
  · rw [if_pos hc] at h ⊢
    exact h
  · rw [if_neg hc] at h ⊢
    obtain ⟨m', s, a, r, w⟩ := h
    exact ⟨m', s, a.nil, r, w⟩

theorem RetZ.toR {σ' : World D} {v : ErgVal D (D.erg f)} (h : RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v) :
    RetZR L P f σ0 ρ0 fp K rp cfp [] t m σ' v := by
  unfold RetZ at h
  unfold RetZR
  by_cases hc : returnFault P f σ0 σ' ρ0 v ≠ 0
  · rw [if_pos hc] at h ⊢
    exact h
  · rw [if_neg hc] at h ⊢
    obtain ⟨m', s, a, r, w⟩ := h
    exact ⟨m', s, a.toR, r, w⟩

theorem RetZR.prefix {σ' : World D} {v : ErgVal D (D.erg f)} (h : Star t0 m0 t m) (ha : AgreeW L fp 2 K m0 m)
    (hs : RetZR L P f σ0 ρ0 fp K rp cfp Hs t m σ' v) : RetZR L P f σ0 ρ0 fp K rp cfp Hs t0 m0 σ' v := by
  unfold RetZR at hs ⊢
  by_cases hc : returnFault P f σ0 σ' ρ0 v ≠ 0
  · rw [if_pos hc] at hs ⊢
    exact Stops.prefix h hs
  · rw [if_neg hc] at hs ⊢
    obtain ⟨m', s, a, r, w⟩ := hs
    exact ⟨m', h.trans s, ha.transR a, r, w⟩

theorem RetWhyR.nil {σ : World D} {r : Fin (D.gruende f)} (h : RetWhyR L f fp K rp cfp [] t m σ r) :
    RetWhy L f fp K rp cfp t m σ r := by
  obtain ⟨m', s, a, value, mirror, flag, world⟩ := h
  exact ⟨m', s, a.nil, value, mirror, flag, world⟩

theorem RetWhy.toR {σ : World D} {r : Fin (D.gruende f)} (h : RetWhy L f fp K rp cfp t m σ r) :
    RetWhyR L f fp K rp cfp [] t m σ r := by
  obtain ⟨m', s, a, value, mirror, flag, world⟩ := h
  exact ⟨m', s, a.toR, value, mirror, flag, world⟩

theorem RetWhyR.prefix {σ : World D} {r : Fin (D.gruende f)} (h : Star t0 m0 t m) (ha : AgreeW L fp 2 K m0 m)
    (hs : RetWhyR L f fp K rp cfp Hs t m σ r) : RetWhyR L f fp K rp cfp Hs t0 m0 σ r := by
  obtain ⟨m', s, a, value, mirror, flag, world⟩ := hs
  exact ⟨m', h.trans s, ha.transR a, value, mirror, flag, world⟩

end

/-- At function level no scope encloses: the empty list of scopes is held under every `H`. -/
theorem scopes_nil {H : List D.Lock} : ∀ M ∈ ([] : List D.Lock), M ∈ H := fun _ hm => (List.not_mem_nil hm).elim

/-- The enclosing scopes of a `locks Lk` body: the outer ones and `Lk`, all held there. -/
theorem scopes_cons {Lk : D.Lock} {sc H : List D.Lock} (h : ∀ M ∈ sc, M ∈ H) : ∀ M ∈ Lk :: sc, M ∈ Lk :: H := by
  intro M hM
  rcases List.mem_cons.mp hM with e | e
  · exact List.mem_cons.mpr (Or.inl e)
  · exact List.mem_cons.mpr (Or.inr (h M e))

end Gabbro.Stage0.Senke
