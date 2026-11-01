module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T9
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T10.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

theorem invB_schritt {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {f : Faden} {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {stapel : List (RufRahmenG D)} {log : List (RufEreignisF D)} {S : REnde (vertragVon D fn)}
    {M M' : RufMaschineG D} (hs : RufSchrittG P O passes M f M')
    (h : InvB O passes A f fn rho s0 stapel log S M) :
    InvB O passes A f fn rho s0 stapel log S M' := by
  rcases h with ⟨l, Γ, Λ, ρ, r, sp, hM, hc, hg⟩ | ⟨v, s1, ext, hlog, hg⟩
  · rcases schrittErhalt (A := A) hs _ hM ρ r rfl hc with
      ⟨l', Γ', Λ', ρ', r', sp', hM', hc', hg'⟩ | ⟨v, s1, hlog, hg'⟩
    · exact Or.inl ⟨l', Γ', Λ', ρ', r', sp', hM', hc', REnde.gleich_trans hg' hg⟩
    · refine Or.inr ⟨v, s1, [], ?_, REnde.gleich_trans (REnde.gleich_symm hg') hg⟩
      rw [List.nil_append]
      exact hlog
  · rcases rufSchrittG_log hs with he | ⟨e, he⟩
    · exact Or.inr ⟨v, s1, ext, by rw [he]; exact hlog, hg⟩
    · exact Or.inr ⟨v, s1, e :: ext, by rw [he, hlog]; rfl, hg⟩

theorem invB_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {f : Faden} {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {stapel : List (RufRahmenG D)} {log : List (RufEreignisF D)} {S : REnde (vertragVon D fn)}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (h : InvB O passes A f fn rho s0 stapel log S M) :
    InvB O passes A f fn rho s0 stapel log S M' := by
  induction hl with
  | refl => exact h
  | schritt hs _ ih => exact ih (invB_schritt hs h)

/-- **TARGET B -- the converse for the value.** Thread `f` of `M` runs a
    frame of `fn` with residue `.ende b` for a covered, oracle-free end
    block `b`. If ANY run of thread `f` alone reaches a machine whose log is
    the old log with exactly one new event `rueck fn rho' v' s0' s1'` (the
    pop of this frame -- a further call or return would add events), then
    the sequential semantics, started at the thread's world `M.weltVon f`,
    ends normally, returning THE SAME value `v'`, in a world with the same
    shared memory as the logged `s1'`; the logged parameters and entry
    world are the frame's.

    The statement was written for runs that interleave bare
    `nimmt`/`gibt` steps (removed from G on 2026-09-13; it holds a
    fortiori): the logged `s1'` agrees with `execEnd`'s world in memory,
    not necessarily in trace. No lock-freedom
    or holdings premise is needed: the statement is about runs that exist.
    `b.ohneOrakel` excludes `regLies`/`regLiesElse`/`awaits`, whose oracle
    sees the whole world, trace included (see the CUTS block). -/
theorem rufG_adaequat_umkehr (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (stapel : List (RufRahmenG D)) (spur : List (Ereignis D))
    (log : List (RufEreignisF D)) {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (b : Endblock D (vertragVon D fn) false Γ Λ) (A : D.Lock → Prop) (hb : EndG A b)
    (ho : b.ohneOrakel = true)
    (hM : M.faeden f = ⟨stapel, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (M'' : RufMaschineG D) (hl : RufLaufG P O passes f M M'')
    (rho' : Env D (D.params fn)) (v' : ErgVal D (D.erg fn)) (s0' s1' : World D)
    (hlog : (M''.faeden f).log = RufEreignisF.rueck fn rho' v' s0' s1' :: log) :
    ∃ σ', execEnd O passes keinRuf b (M.weltVon f) ρ = .zurueck σ' v' ∧
      σ'.speicher = s1'.speicher ∧ rho' = rho ∧ s0' = s0 := by
  have h0 : InvB O passes A f fn rho s0 stapel log
      (endErg (execEnd O passes keinRuf b (M.weltVon f) ρ)) M :=
    Or.inl ⟨false, Γ, Λ, ρ, .ende b, spur, hM, RestG.ende b hb ho, REnde.gleich_refl _⟩
  rcases invB_lauf hl h0 with ⟨l, Γ', Λ', ρ', r, sp, hM'', _, _⟩ | ⟨v, s1, ext, hlog', hg⟩
  · rw [hM''] at hlog
    have hlen := congrArg List.length hlog
    simp only [List.length_cons, Nat.left_eq_add, Nat.succ_ne_self] at hlen
  · rw [hlog'] at hlog
    have hext : ext = [] := by
      have hlen := congrArg List.length hlog
      simp only [List.length_append, List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff] at hlen
      exact hlen
    subst hext
    simp only [List.nil_append, List.cons.injEq, RufEreignisF.rueck.injEq] at hlog
    obtain ⟨⟨_, hrho, hv, hs0, hs1⟩, _⟩ := hlog
    have hv' : v = v' := eq_of_heq hv
    have hrho' : rho = rho' := eq_of_heq hrho
    subst hv' hrho' hs0 hs1
    revert hg
    cases hex : execEnd O passes keinRuf b (M.weltVon f) ρ with
    | zurueck σ' w =>
      intro hg
      obtain ⟨hsg, hvw⟩ := hg
      subst hvw
      exact ⟨σ', rfl, hsg.speicher.symm, rfl, rfl⟩
    | _ => intro hg; exact absurd hg id

/-- The witness body never consults the oracle. -/
theorem adRumpf_ohneOrakel : adRumpf.ohneOrakel = true := by rfl


end Gabbro.Grammatik
