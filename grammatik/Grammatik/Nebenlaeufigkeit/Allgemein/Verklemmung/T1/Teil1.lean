module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T1.Teil1a

public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStart
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 2. The rank invariant -/

/-- The floor of a function. -/
def bodenF (f : D.Fn) : Option Int := (D.signatur f).boden

/-- `K` ranks below the floor `b`. -/
def UnterB (b : Option Int) (K : D.Lock) : Prop := ∃ c, b = some c ∧ D.rang K < c

/-- `K` ranks at least the floor `b` (vacuous without a floor). -/
def UeberB (b : Option Int) (K : D.Lock) : Prop := ∀ c, b = some c → c ≤ D.rang K

/-- The floor `b` is at most `b'` (a floor below forces a floor above). -/
def BodenLe (b b' : Option Int) : Prop := ∀ c, b = some c → ∃ c', b' = some c' ∧ c ≤ c'

theorem bodenLe_trans {a b c : Option Int} (h1 : BodenLe a b) (h2 : BodenLe b c) :
    BodenLe a c := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h1 x hx
  obtain ⟨z, hz, hyz⟩ := h2 y hy
  exact ⟨z, hz, Int.le_trans hxy hyz⟩

theorem ueberB_of_le {b b' : Option Int} {K : D.Lock} (h : UeberB b' K) (hle : BodenLe b b') :
    UeberB b K := by
  intro c hc
  obtain ⟨c', hc', hle'⟩ := hle c hc
  exact Int.le_trans hle' (h c' hc')

theorem unter_ueber {b : Option Int} {K : D.Lock} (h1 : UnterB b K) (h2 : UeberB b K) : False := by
  obtain ⟨c, hc, hlt⟩ := h1
  have := h2 c hc
  omega

/-- **The rank chain of a stack** (head first). Every held lock `K ∈ o` is,
    at each frame: named by it, or below its floor (an extra lock of its
    callers), or at least the floor of the frame directly above it (`oben`:
    taken by a callee; nothing above the head); at the bottom frame the
    middle case is absent (a start frame has no caller). Every frame's
    signature locks are named by the frame below it, and floors rise
    towards the head. -/
def RangKette (o : List D.Lock) : (D.Lock → Prop) → RufRahmenG D → List (RufRahmenG D) → Prop
  | oben, F, [] => ∀ K ∈ o, Res.held K ∈ F.rest.2.2.1 ∨ oben K
  | oben, F, c :: rest =>
      (∀ K ∈ o, Res.held K ∈ F.rest.2.2.1 ∨ UnterB (bodenF F.f) K ∨ oben K) ∧
      (∀ L ∈ D.haelt F.f, Res.held L ∈ c.rest.2.2.1) ∧ BodenLe (bodenF c.f) (bodenF F.f) ∧
      RangKette o (UeberB (bodenF F.f)) c rest

theorem rangKette_boden {o : List D.Lock} :
    ∀ {oben : D.Lock → Prop} {F : RufRahmenG D} {S : List (RufRahmenG D)},
      RangKette o oben F S → ∀ G ∈ S, BodenLe (bodenF G.f) (bodenF F.f)
  | _, _, [], _, G, hG => absurd hG List.not_mem_nil
  | _, _, c :: rest, h, G, hG => by
      obtain ⟨_, _, h3, h4⟩ := h
      rcases List.mem_cons.mp hG with rfl | hG
      · exact h3
      · exact bodenLe_trans (rangKette_boden h4 G hG) h3

/-- The head's clause, whatever the stack below. -/
theorem rangKette_kopfK {o : List D.Lock} {F : RufRahmenG D} {S : List (RufRahmenG D)}
    (h : RangKette o (fun _ => False) F S) :
    ∀ K ∈ o, Res.held K ∈ F.rest.2.2.1 ∨ UnterB (bodenF F.f) K := by
  cases S with
  | nil => exact fun K hK => (h K hK).imp id False.elim
  | cons c rest =>
      intro K hK
      rcases h.1 K hK with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact h1.elim

theorem rangKette_tail {o o' : List D.Lock} :
    ∀ {oben : D.Lock → Prop} {F : RufRahmenG D} {S : List (RufRahmenG D)},
      RangKette o oben F S →
      (∀ K ∈ o', K ∈ o ∨ (oben K ∧ ∀ G ∈ F :: S, UeberB (bodenF G.f) K)) →
      RangKette o' oben F S
  | _, _, [], h, hK => fun K hk => by
      rcases hK K hk with h1 | ⟨h1, _⟩
      · exact h K h1
      · exact Or.inr h1
  | _, F, c :: rest, h, hK => by
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨fun K hk => ?_, h2, h3, rangKette_tail h4 fun K hk => ?_⟩
      · rcases hK K hk with h5 | ⟨h5, _⟩
        · exact h1 K h5
        · exact Or.inr (Or.inr h5)
      · rcases hK K hk with h5 | ⟨_, h5⟩
        · exact Or.inl h5
        · exact Or.inr ⟨h5 F List.mem_cons_self, fun G hG => h5 G (List.mem_cons_of_mem _ hG)⟩

end Gabbro.Grammatik
