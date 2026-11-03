module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The resource balance of a residue. Each non-signature held resource
    has one pending lexical release marker, counting multiplicities.
    This is an internal reachable-state invariant, not a program premise. -/
def GRest.scopeBalance {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : GRest D V l Γ Λ) : Prop :=
  ∀ L : D.Lock, Λ.count (Res.held L) = V.ende.count (Res.held L) + r.freis.count L

/-- Exact residual resources identify the cleanup list with the pending
    lexical markers. No ordering or duplicate-free assumption is needed
    for this counting argument. -/
theorem GRest.scopes_perm_freis {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) (R : RueckRessourcen D V Λ)
    (h : r.scopeBalance) : R.scopes.Perm r.freis := by
  apply List.perm_iff_count.mpr
  intro L
  have hp := count_of_perm (a := Res.held L) R.genau
  rw [List.count_append, count_held_map] at hp
  have hb := h L
  omega

/-- In particular, the number of release steps equals the number of
    pending lexical markers; each marker already has a unit of source
    potential. -/
theorem GRest.scopes_length {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) (R : RueckRessourcen D V Λ)
    (h : r.scopeBalance) : R.scopes.length = r.freis.length :=
  (r.scopes_perm_freis R h).length_eq

/-- A lexical marker can release only a resource named by its frame.
    This follows from the existing continuation invariant. -/
theorem GRest.freis_held {V : Vertrag D} {A : List D.Lock} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ),
      r.kette A → ∀ L ∈ r.freis, Res.held L ∈ Λ
  | _, _, _, .ende _, _, _, h => (List.not_mem_nil h).elim
  | _, _, _, .dann b k, h, L, hL =>
      (Block.held_iff b L).mp (k.freis_held h.2 L hL)
  | _, _, _, .schrumpf k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .frei K k, h, L, hL => by
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (k.freis_held h.2 L hL)
  | _, _, _, .trav _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .travRest _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .wieder _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .wiederRest _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .ewig _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .ewigRest _ _ _ _ k, h, L, hL => k.freis_held h.2 L hL
  | _, _, _, .wartet b k, h, L, hL =>
      (Block.held_iff b L).mp (k.freis_held h.2 L hL)
  | _, _, _, .wartetSonst _ _ b k, h, L, hL =>
      (Block.held_iff b L).mp (k.freis_held h.2 L hL)
  | _, _, _, .abbruch k, h, L, hL => h.2.1 L (k.freis_held h.2.2 L hL)
  | _, _, _, .zurueckgekehrt _, _, _, h => (List.not_mem_nil h).elim
  | _, _, _, .aufraeumen _ _, _, L, hL =>
      List.mem_append_left _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
  | _, _, _, .leer, _, _, h => (List.not_mem_nil h).elim
  | _, _, _, .rueckBereit _ k, h, L, hL =>
      List.mem_append_right _ (k.freis_held h.2 L hL)

/-- Lexical release markers never repeat a lock: a `frei` marker's lock
    is absent from its continuation, and every deeper marker is named there. -/
theorem GRest.freis_nodup {V : Vertrag D} {A : List D.Lock} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ),
      r.kette A → r.freis.Nodup
  | _, _, _, .ende _, _ => List.nodup_nil
  | _, _, _, .dann _ k, h => k.freis_nodup h.2
  | _, _, _, .schrumpf k, h => k.freis_nodup h.2
  | _, _, _, .frei L k, h =>
      List.nodup_cons.mpr ⟨fun hm => h.1 (k.freis_held h.2 L hm), k.freis_nodup h.2⟩
  | _, _, _, .trav _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .travRest _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .wieder _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .wiederRest _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .ewig _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .ewigRest _ _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .wartet _ k, h => k.freis_nodup h.2
  | _, _, _, .wartetSonst _ _ _ k, h => k.freis_nodup h.2
  | _, _, _, .abbruch k, h => k.freis_nodup h.2.2
  | _, _, _, .zurueckgekehrt _, _ => List.nodup_nil
  | _, _, _, .aufraeumen _ _, h => h.2.1
  | _, _, _, .leer, _ => List.nodup_nil
  | _, _, _, .rueckBereit _ k, h => k.freis_nodup h.2

/-- The source cleanup list inherits the marker discipline from the frame. -/
theorem GRest.scopes_nodup {V : Vertrag D} {A : List D.Lock} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) (R : RueckRessourcen D V Λ)
    (hb : r.scopeBalance) (hk : r.kette A) : R.scopes.Nodup :=
  (r.scopes_perm_freis R hb).nodup_iff.mpr (r.freis_nodup hk)

/-- An evaluated cleanup residue has precisely the remaining scope
    resources. Releasing one head marker preserves this balance. -/
theorem GRest.scopeBalance_aufraeumen {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D) (remaining : List D.Lock) :
    (GRest.aufraeumen (l := l) (Γ := Γ) a remaining).scopeBalance := by
  intro L
  simp only [GRest.scopeBalance, GRest.freis, List.count_append, count_held_map]
  omega

/-- Finished scoped roots have no remaining lexical releases. -/
theorem GRest.scopeBalance_zurueckgekehrt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (a : (ErgVal D V.erg ⊕ Fin V.gruende) × World D) :
    (GRest.zurueckgekehrt (l := l) (Γ := Γ) a).scopeBalance := by
  intro L
  simp only [GRest.freis, List.count_nil, Nat.add_zero]

/-- A source frame enters without any lexical scope markers. -/
theorem GRest.scopeBalance_eintritt {P : Programm D} (g : D.Fn) :
    (GRest.ende (P.rumpf g)).scopeBalance := by
  intro L
  simp only [GRest.freis, List.count_nil, Nat.add_zero]
  simp only [Signatur.anfang, Vertrag.ende, vertragVon, Vertrag.vonSig,
    List.count_append, count_held_marke_map, Nat.add_zero]

/-- Evaluation retains all held locks. The counted lexical provenance
    transfers the old caller-protection invariant to the cleanup list. -/
theorem haeltInvG_scopedEval {z : RufFadenG D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (R : RueckRessourcen D (vertragVon D z.kopf.f) Λ)
    (hx : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (h : HaeltInvG z)
    (hb : r.scopeBalance)
    (hsc : scopesOkScopes (vertragVon D z.kopf.f).haelt
      (vertragVon D z.kopf.f).boden R.scopes = true)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕
      Fin (vertragVon D z.kopf.f).gruende) × World D)
    (spur' : List (Ereignis D)) (ho : offen spur' = offen z.spur) :
    HaeltInvG ⟨z.stapel,
      ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, _, ρ, .aufraeumen a R.scopes⟩⟩,
      spur', z.log⟩ := by
  have hk := kette_von hx (h.2.1 _ List.mem_cons_self)
  apply haeltInvG_kopf h
  · intro K hK _
    rw [ho]
    exact hK
  · intro L hL
    left
    rw [freis_von hx]
    exact (r.scopes_perm_freis R hb).mem_iff.mp hL
  · refine ⟨?_, r.scopes_nodup R hb hk, ?_⟩
    · intro L hL
      exact (held_ende _ L).mpr hL
    · intro L hL he
      exact (scopesOkScopes_mem hsc hL).1 ((held_ende _ L).mp he)
  · intro L hL
    rw [ho]
    apply h.kopf L
    rw [hx]
    exact (R.genau.trans List.perm_append_comm).mem_iff.mpr hL

/-- An intermediate cleanup step removes exactly its head marker. The
    existing `FreiLinks` protects every suspended caller from that release. -/
theorem haeltInvG_scopedRelease {z : RufFadenG D} {l : Bool} {Γ : Ctx}
    (ρ : Env D Γ)
    (a : (ErgVal D (vertragVon D z.kopf.f).erg ⊕
      Fin (vertragVon D z.kopf.f).gruende) × World D)
    (L : D.Lock) (remaining : List D.Lock)
    (hx : z.kopf.rest = ⟨l, Γ, _, ρ, .aufraeumen a (L :: remaining)⟩)
    (h : HaeltInvG z) :
    HaeltInvG ⟨z.stapel,
      ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, _, ρ, .aufraeumen a remaining⟩⟩,
      .gibt L :: z.spur, z.log⟩ := by
  have hk := kette_von hx (h.2.1 _ List.mem_cons_self)
  change (_ ∧ (L :: remaining).Nodup ∧ _) at hk
  have hnd := List.nodup_cons.mp hk.2.1
  apply haeltInvG_kopf h
  · intro K hK hnf
    have hne : K ≠ L := by
      intro he
      apply hnf
      rw [freis_von hx]
      exact List.mem_cons.mpr (Or.inl he)
    exact (List.mem_erase_of_ne hne).mpr hK
  · intro K hK
    left
    rw [freis_von hx]
    exact List.mem_cons_of_mem _ hK
  · exact ⟨hk.1, hnd.2, fun K hK => hk.2.2 K (List.mem_cons_of_mem _ hK)⟩
  · intro K hK
    have hne : K ≠ L := by
      intro he
      subst K
      rcases List.mem_append.mp hK with hrem | hend
      · obtain ⟨K, hK, he⟩ := List.mem_map.mp hrem
        cases he
        exact hnd.1 hK
      · exact hk.2.2 L List.mem_cons_self hend
    apply (List.mem_erase_of_ne hne).mpr
    apply h.kopf K
    rw [hx]
    exact List.mem_cons_of_mem _ hK

end Gabbro.Grammatik
