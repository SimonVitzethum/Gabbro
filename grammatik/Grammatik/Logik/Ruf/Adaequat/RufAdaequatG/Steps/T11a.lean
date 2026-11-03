module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T10
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T11b
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- **Witness for `rufG_adaequat_umkehr`.** All premises instantiated
    jointly on the `locks`/`if`/write program: the machine `adM`, the
    covered oracle-free body, the run of thread 0 that `rufG_adaequat`
    produces (a real run of the machine, through `endeEntf`, `dannLocks`,
    `dannIteWahr`, the writing `dannBlatt`, `freiGib`, ... and `rueckCons`),
    and its log, which holds exactly the pop. The converse then recovers
    from the MACHINE's log that the sequential semantics returns the logged
    value `7`, with the memory of the logged world (slot 0 moved to 5). -/
theorem rufG_adaequat_umkehr_zeuge :
    ∃ (M'' : RufMaschineG adD) (v : ErgVal adD (adD.erg adFn)) (s1 : World adD),
      RufLaufG adP adO 0 0 adM M'' ∧
      (M''.faeden 0).log = [RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) s1] ∧
      (s1.slots () 0 ()).n = 5 ∧
      ∃ σ', execEnd adO 0 keinRuf adRumpf (adM.weltVon 0) Env.nil = .zurueck σ' v ∧
        σ'.speicher = s1.speicher ∧ (show Zahl 0 100 from v).n = 7 := by
  obtain ⟨σ', v, _, h5, _, h7, M', hl, hf, _, _, _⟩ := rufG_adaequat_zeuge
  have hlog : (M'.faeden 0).log =
      RufEreignisF.rueck adFn Env.nil v (adSp0.welt []) σ' :: [] := by rw [hf]
  obtain ⟨σ'', hex, hsp, _, _⟩ := rufG_adaequat_umkehr adP adO 0 adM 0 adFn Env.nil
    (adSp0.welt []) [adCaller] [] [] Env.nil adRumpf (fun L : adD.Lock => L = ())
    adRumpf_G adRumpf_ohneOrakel rfl M' hl Env.nil v (adSp0.welt []) σ' hlog
  exact ⟨M', v, σ', hl, hlog, h5, σ'', hex, hsp, h7⟩

/-! ## 18. AGREEMENT (formerly a finding): `traverse` now mirrors `traverseLauf`

    The old rules `dannTravWeiter`/`dannTravFertig` read the invariant at the
    unfold and SKIPPED the loop on a false start invariant (the machine then
    returned where `traverseLauf` ends in `logik .schleife`), `travNext` read
    it a second time before the first iteration, and `travDone` never read it
    after the last. The repaired rules: `dannTrav` unfolds WITHOUT a read,
    `travNext` reads before every iteration, `travDone` reads after the last
    one (both only on `true`), `dannLeaveTrav` reads after a `leave` (only on
    `true`) -- exactly the reads of `traverseLauf`. On a false read NO rule
    for the frame fires (`trav_falsch_steht`): the frame is stuck, and no
    normal return can follow, matching `logik .schleife`. The old
    counterexample now agrees (`trav_einig`). -/

/-- At a head `dann (traverse …; rest) k` every step of `f` is a bare lock
    step or the read-free unfold `dannTrav`. -/
theorem trav_dann_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩) :
    (∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩) ∨
    (∃ sp, M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
      ⟨l, Γ, Λ, ρ, .trav t inv body (alleIndizes (D.count t)) (.dann rest k)⟩⟩, sp, z.log⟩) := by
  subst hz
  cases hs with
  | g1 hs =>
    cases hs with
    | endeBindAxiomOpt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
    | ruf =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueck =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeEntf =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeForm =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBlatt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeer =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannIteWahr =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannIteFalsch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnOptionSome =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnOptionNone =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnTagSome =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnTagNone =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannOnGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNarrowOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiom =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g2 hs =>
    cases hs with
    | dannNarrowElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannPruefWahr =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannPruefFalsch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBreaking =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLocks =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | freiGib =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | schrumpfVergiss =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => (rw [hR] at hhead; cases hhead; exact Or.inr ⟨_, rufUpdateG_self _ _ _⟩)
    | travNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | travFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | travDone =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRetry =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederUeber =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederWeiter =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederSchritt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | wiederFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannForever =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | ewigWeiter =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | ewigFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rufDann =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannAxiomCallElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannCallInd =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rufCallInd =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCall =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCallInd =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCallElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindCallIndElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannCallIndElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveTrav =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNextTrav =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveWieder =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNextWieder =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveEwig =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g4 hs =>
    cases hs with
    | dannNextEwig =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelDannLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelDannNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelSchrumpfLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelSchrumpfNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelFreiLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelFreiNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelAbbruchLeave =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | peelAbbruchNext =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRet =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckCons =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRetBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckConsBind =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomOptElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomOptElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRegLies =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRegLiesElseWahr =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRegLiesElseFalsch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannAwaits =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannExchange =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleit =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitLit =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitVon =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitNarrowOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannGleitNarrowElse =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiom =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannBindAxiomElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckConsGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannRetGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g6 hs =>
    cases hs with
    | endeBindAxiomOptElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiomOptElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiomElseOk =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | endeBindAxiomElseGrund =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
  | g7 hs =>
    cases hs with
    | dannVerbrauch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | verbrauchWeiter =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | verbrauchLeer =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | verbrauchFort =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannLeaveVerbrauch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | dannNextVerbrauch =>
      (try have hhead := ‹(M.faeden f).kopf.rest = _›); (try have hpop := ‹(M.faeden f).stapel = _›); (try have hleaf := ‹Stmt.istBlatt _ = true›); (try have hstep := ‹execStmt _ _ _ _ _ _ = _›); kopfweg
    | rueckScopedWert ρ r e R hhead hret
    | rueckScopedWertDirekt ρ r e R hhead hret =>
      rcases GRest.scopedWert_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> (have hhead := hhead; kopfweg)
    | rueckScopedGrund ρ r grund R hhead hret
    | rueckScopedGrundDirekt ρ r grund R hhead hret =>
      rcases GRest.scopedGrund_faelle hret with hr | ⟨rest, hr⟩ | ⟨Λ', rest, k, hr⟩ <;>
        subst r <;> (have hhead := hhead; kopfweg)

    | rueckFreigabe ρ a L remaining hhead =>
      rw [hR] at hhead
      cases hhead
    | rueckFreigabeLetzte ρ a L hhead z hantwort =>
      rw [hR] at hhead
      cases hhead

end Gabbro.Grammatik
