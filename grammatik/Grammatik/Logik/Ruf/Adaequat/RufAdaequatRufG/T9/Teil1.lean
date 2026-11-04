module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T9.Teil1Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T9.Teil1Basis

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8a

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-- **Witness for `rufG_adaequat_ruf` with `forever`, `leave` and `next`.**
    All premises jointly, on the loop program at depth 1 with one pass:
    the `forever` pass WRITES slot 1 (`0 -> 8`) and then leaves through an
    `if` (the machine peels the `if` layer and fires `dannLeaveEwig`);
    every `traverse` iteration exits by `next` through an `if` (peel,
    `dannNextTrav`), skipping the write behind it -- slot 2 stays `0`. The
    machine pops the frame with the sequential value `9` and memory. -/
theorem rufG_adaequat_ruf_zeuge_leave :
    ∃ (σ' : World t5D) (v : ErgVal t5D (vertragVon t5D t5L).erg),
      execEnd t5O 1 (rufRumpf t5P t5O 1 1) t5LRumpf ((t5M t5L t5LRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (((t5M t5L t5LRumpf).weltVon 0).slots () 1 ()).n = 0 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t5D) (ext : List (RufEreignisF t5D)),
        RufLaufG t5P t5O 1 0 (t5M t5L t5LRumpf) M' ∧
        M'.faeden 0 = ⟨[], t5Unten, σ'.spur,
          RufEreignisF.rueck t5L Env.nil v (t5Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 1 ()).n = 8 ∧ (M'.speicher.slots () 2 ()).n = 0 ∧
        (∀ g, g ≠ 0 → M'.faeden g = (t5M t5L t5LRumpf).faeden g) := by
  obtain ⟨σ', v, hex, h8, h0, h9⟩ := t5L_exec
  obtain ⟨M', ext, hl, hf, hsp, hfr⟩ := rufG_adaequat_ruf t5P t5O 1 1 (t5M t5L t5LRumpf) 0 t5L
    Env.nil (t5Sp.welt []) t5Unten [] [] [] Env.nil t5LRumpf (fun _ => False)
    (t5LRumpf_R _) rfl rfl t5_held (t5_frei t5L t5LRumpf) σ' v hex
  refine ⟨σ', v, hex, rfl, h9, M', ext, hl, hf, ?_, ?_, hfr⟩
  · rw [hsp]; exact h8
  · rw [hsp]; exact h0

/-- **Witness for `rufG_adaequat_ruf` with both paths of `let … else`.**
    All premises jointly, on the bind-else program at depth 1: the first
    call returns normally (`H` writes slot 1, `x = 6`, machine `rueckBind`
    into `wartetSonst`), the second answers a reason (`E` writes slot 0,
    machine `rueckConsGrund` logs `grund` and resumes the caller's else
    block with the reason bound), the else block writes `x` to slot 2 and
    returns 5. The machine pops with `5` and all three slots moved. -/
theorem rufG_adaequat_ruf_zeuge_sonst :
    ∃ (σ' : World t5D) (v : ErgVal t5D (vertragVon t5D t5B).erg),
      execEnd t5O 0 (rufRumpf t5P t5O 0 1) t5BRumpf ((t5M t5B t5BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 5 ∧
      ∃ (M' : RufMaschineG t5D) (ext : List (RufEreignisF t5D)),
        RufLaufG t5P t5O 0 0 (t5M t5B t5BRumpf) M' ∧
        M'.faeden 0 = ⟨[], t5Unten, σ'.spur,
          RufEreignisF.rueck t5B Env.nil v (t5Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 0 ()).n = 4 ∧ (M'.speicher.slots () 1 ()).n = 2 ∧
        (M'.speicher.slots () 2 ()).n = 6 := by
  obtain ⟨σ', v, hex, h4, h2, h6, h5⟩ := t5B_exec
  obtain ⟨M', ext, hl, hf, hsp, _⟩ := rufG_adaequat_ruf t5P t5O 0 1 (t5M t5B t5BRumpf) 0 t5B
    Env.nil (t5Sp.welt []) t5Unten [] [] [] Env.nil t5BRumpf (fun _ => False)
    (t5BRumpf_R _) rfl rfl t5_held (t5_frei t5B t5BRumpf) σ' v hex
  refine ⟨σ', v, hex, h5, M', ext, hl, hf, ?_, ?_, ?_⟩
  · rw [hsp]; exact h4
  · rw [hsp]; exact h2
  · rw [hsp]; exact h6

/-! ## 12. AGREEMENT (formerly a finding): a pop never restores a waiting caller

    Before the repair, `rueck`, `rueckCons` and `dannRet` popped the callee
    frame and restored the caller frame VERBATIM, also when the caller
    waited for a bound value (residue `wartet rest k`): the restored head
    `wartet …` has no rule, the thread was stuck for good (`wartet_steht`,
    `wartet_lauf` below), while the sequential semantics binds the value and
    continues. The three verbatim pops now demand a caller that does not
    wait (`hnw : caller.wartend = false`, `RufMaschineG.lean`); a waiting
    caller is resumed only by a binding pop. `rufG_nie_wartend` shows that
    no reachable head waits; `wartet_einig` checks it on the bind witness
    from its waiting state. -/

/-- At a head `wartet rest k` no step of `f` changes frame, stack or log (the
    bare lock steps that fired there were removed from G on 2026-09-13). -/
theorem wartet_steht {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩) :
    ∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩ := by
  subst hz
  cases hs with
  | g1 hs =>
    cases hs with
    | endeBindAxiomOpt => kopfwegH
    | blatt => kopfwegH
    | ruf => kopfwegH
    | rueck => kopfwegH
    | endeEntf => kopfwegH
    | endeForm => kopfwegH
    | dannBlatt => kopfwegH
    | dannLeer => kopfwegH
    | dannIteWahr => kopfwegH
    | dannIteFalsch => kopfwegH
    | dannOnOptionSome => kopfwegH
    | dannOnOptionNone => kopfwegH
    | dannOnTagSome => kopfwegH
    | dannOnTagNone => kopfwegH
    | dannOnGrund => kopfwegH
    | endeBind => kopfwegH
    | dannBind => kopfwegH
    | dannNarrowOk | dannNarrowRequired => kopfwegH
    | endeBindAxiom => kopfwegH
  | g2 hs =>
    cases hs with
    | dannNarrowElse => kopfwegH
    | dannPruefWahr => kopfwegH
    | dannPruefFalsch => kopfwegH
    | dannBreaking => kopfwegH
    | dannLocks => kopfwegH
    | freiGib => kopfwegH
    | schrumpfVergiss => kopfwegH
    | dannTrav => kopfwegH
    | travNext => kopfwegH
    | travFort => kopfwegH
    | travDone => kopfwegH
    | dannRetry => kopfwegH
    | wiederUeber => kopfwegH
    | wiederWeiter => kopfwegH
    | wiederSchritt => kopfwegH
    | wiederFort => kopfwegH
    | dannForever => kopfwegH
    | ewigWeiter => kopfwegH
    | ewigFort => kopfwegH
    | rufDann => kopfwegH
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk => kopfwegH
    | dannAxiomCallElseGrund => kopfwegH
    | dannCallInd => kopfwegH
    | rufCallInd => kopfwegH
    | dannBindCall => kopfwegH
    | dannBindCallInd => kopfwegH
    | dannBindCallElse => kopfwegH
    | dannBindCallIndElse => kopfwegH
    | dannCallIndElse => kopfwegH
    | rueckBind => kopfwegH
    | dannLeaveTrav => kopfwegH
    | dannNextTrav => kopfwegH
    | dannLeaveWieder => kopfwegH
    | dannNextWieder => kopfwegH
    | dannLeaveEwig => kopfwegH
  | g4 hs =>
    cases hs with
    | dannNextEwig => kopfwegH
    | peelDannLeave => kopfwegH
    | peelDannNext => kopfwegH
    | peelSchrumpfLeave => kopfwegH
    | peelSchrumpfNext => kopfwegH
    | peelFreiLeave => kopfwegH
    | peelFreiNext => kopfwegH
    | peelAbbruchLeave => kopfwegH
    | peelAbbruchNext => kopfwegH
    | dannRet => kopfwegH
    | rueckCons => kopfwegH
    | dannRetBind => kopfwegH
    | rueckConsBind => kopfwegH
    | rueckGrund => kopfwegH
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt => kopfwegH
    | dannBindAxiomOptElseOk => kopfwegH
    | dannBindAxiomOptElseGrund => kopfwegH
    | dannRegLies => kopfwegH
    | dannRegLiesElseWahr => kopfwegH
    | dannRegLiesElseFalsch => kopfwegH
    | dannAwaits => kopfwegH
    | dannExchange => kopfwegH
    | dannGleit => kopfwegH
    | dannGleitLit => kopfwegH
    | dannGleitVon => kopfwegH
    | dannGleitNarrowOk => kopfwegH
    | dannGleitNarrowElse => kopfwegH
    | dannBindAxiom => kopfwegH
    | dannBindAxiomElseOk => kopfwegH
    | dannBindAxiomElseGrund => kopfwegH
    | rueckConsGrund => kopfwegH
    | dannRetGrund => kopfwegH
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk => kopfwegH
    | endeBindAxiomOptElseGrund => kopfwegH
    | endeBindAxiomElseOk => kopfwegH
    | endeBindAxiomElseGrund => kopfwegH
    | endeGleit => kopfwegH
    | endeGleitLit => kopfwegH
    | endeGleitVon => kopfwegH
    | endeGleitNarrowOk => kopfwegH
    | endeGleitNarrowElse => kopfwegH
  | g7 hs =>
    cases hs with
    | dannVerbrauch => kopfwegH
    | verbrauchWeiter => kopfwegH
    | verbrauchLeer => kopfwegH
    | verbrauchFort => kopfwegH
    | dannLeaveVerbrauch => kopfwegH
    | dannNextVerbrauch => kopfwegH
    | rueckScopedWert ρ r e R hhead hret
    | rueckScopedWertDirekt ρ r e R hhead hret =>
      rcases GRest.scopedWert_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> kopfwegH
    | rueckScopedGrund ρ r grund R hhead hret
    | rueckScopedGrundDirekt ρ r grund R hhead hret =>
      rcases GRest.scopedGrund_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> kopfwegH
    | rueckFreigabe => kopfwegH
    | rueckFreigabeLetzte => kopfwegH

/-- A thread whose head waits stays so, and logs nothing, along any run. -/
theorem wartet_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (stapel : List (RufRahmenG D)) (kopf : RufRahmenG D) (log : List (RufEreignisF D))
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (rest : Block D (vertragVon D kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hR : kopf.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩) :
    ∀ sp0, M.faeden f = ⟨stapel, kopf, sp0, log⟩ →
      ∃ sp, M'.faeden f = ⟨stapel, kopf, sp, log⟩ := by
  induction hl with
  | refl => intro sp0 h; exact ⟨sp0, h⟩
  | schritt hs _ ih =>
    intro sp0 h
    obtain ⟨sp, e⟩ := wartet_steht hs _ h rest k ρ hR
    exact ih sp e

/-- The function an event belongs to. -/
def RufEreignisF.fnVon : RufEreignisF D → D.Fn
  | .eintritt f .. => f
  | .rueck f .. => f
  | .why f .. => f

/-- Runs of one thread keep the no-waiting-head invariant of every thread. -/
theorem rufLaufG_sauber {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (h : ∀ g, RufFadenSauberG (M.faeden g)) : ∀ g, RufFadenSauberG (M'.faeden g) := by
  induction hl with
  | refl => exact h
  | schritt hs _ ih => exact ih (rufSchrittG_sauber hs h)

/-- The witness machines satisfy the invariant: `ende` heads above `t4Unten`. -/
theorem t4M_sauber (fn : t4D.Fn) (b : Endblock t4D (vertragVon t4D fn) false [] []) :
    ∀ g, RufFadenSauberG ((t4M fn b).faeden g) := by
  intro g
  refine ⟨rfl, ?_⟩
  intro r hr
  simp only [t4M, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rfl

end Gabbro.Grammatik
