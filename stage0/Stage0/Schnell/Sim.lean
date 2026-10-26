/-
  File:      stage0/Stage0/Schnell/Sim.lean
  Subject:   **The normal form simulates the thread machine.** A step of `normal ww M` under the fast oracle (it sees
             the questions the compact trace dropped through `OrakelPaar`) is a step of `M` under the machine's
             oracle, and the two results have the same normal form; the machine's thread has asked exactly the
             questions the fast one counts. One lemma per rule of `RufSchrittG` (`Schnell/Sim/S*.lean`).
-/
import Stage0.Schnell.Sim.SA
import Stage0.Schnell.Sim.SB
import Stage0.Schnell.Sim.SC
import Stage0.Schnell.Sim.SD
import Stage0.Schnell.Sim.SE
import Stage0.Schnell.Sim.SF
import Stage0.Schnell.Sim.SG
import Stage0.Schnell.Sim.SH

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {OF OM : Orakel D} {passes : Nat} {ww : World D}

/-- **The simulation.** -/
theorem sim {M : RufMaschineG D} {f : Faden} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    {F' : RufMaschineG D} (h : RufSchrittG P OF passes (normal ww M) f F') :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧ normal ww F' = normal ww M' ∧
      fremdZahl (M'.faeden f).spur = fremdZahl (F'.faeden f).spur + fremdZahl (M.faeden f).spur := by
  generalize hN : normal ww M = N at h
  cases h
  case blatt => subst hN; apply sim_blatt hO <;> assumption
  case ruf => subst hN; apply sim_ruf hO <;> assumption
  case rueck => subst hN; apply sim_rueck hO <;> assumption
  case endeEntf => subst hN; apply sim_endeEntf hO <;> assumption
  case endeForm => subst hN; apply sim_endeForm hO <;> assumption
  case dannBlatt => subst hN; apply sim_dannBlatt hO <;> assumption
  case dannLeer => subst hN; apply sim_dannLeer hO <;> assumption
  case dannIteWahr => subst hN; apply sim_dannIteWahr hO <;> assumption
  case dannIteFalsch => subst hN; apply sim_dannIteFalsch hO <;> assumption
  case dannOnOptionSome => subst hN; apply sim_dannOnOptionSome hO <;> assumption
  case dannOnOptionNone => subst hN; apply sim_dannOnOptionNone hO <;> assumption
  case dannOnTagSome => subst hN; apply sim_dannOnTagSome hO <;> assumption
  case dannOnTagNone => subst hN; apply sim_dannOnTagNone hO <;> assumption
  case dannOnGrund => subst hN; apply sim_dannOnGrund hO <;> assumption
  case endeBind => subst hN; apply sim_endeBind hO <;> assumption
  case endeBindAxiom => subst hN; apply sim_endeBindAxiom hO <;> assumption
  case dannBind => subst hN; apply sim_dannBind hO <;> assumption
  case dannNarrowOk => subst hN; apply sim_dannNarrowOk hO <;> assumption
  case dannNarrowElse => subst hN; apply sim_dannNarrowElse hO <;> assumption
  case dannPruefWahr => subst hN; apply sim_dannPruefWahr hO <;> assumption
  case dannPruefFalsch => subst hN; apply sim_dannPruefFalsch hO <;> assumption
  case dannBreaking => subst hN; apply sim_dannBreaking hO <;> assumption
  case dannLocks => subst hN; apply sim_dannLocks hO <;> assumption
  case freiGib => subst hN; apply sim_freiGib hO <;> assumption
  case schrumpfVergiss => subst hN; apply sim_schrumpfVergiss hO <;> assumption
  case dannTrav => subst hN; apply sim_dannTrav hO <;> assumption
  case travNext => subst hN; apply sim_travNext hO <;> assumption
  case travFort => subst hN; apply sim_travFort hO <;> assumption
  case travDone => subst hN; apply sim_travDone hO <;> assumption
  case dannRetry => subst hN; apply sim_dannRetry hO <;> assumption
  case wiederUeber => subst hN; apply sim_wiederUeber hO <;> assumption
  case wiederWeiter => subst hN; apply sim_wiederWeiter hO <;> assumption
  case wiederSchritt => subst hN; apply sim_wiederSchritt hO <;> assumption
  case wiederFort => subst hN; apply sim_wiederFort hO <;> assumption
  case dannForever => subst hN; apply sim_dannForever hO <;> assumption
  case ewigWeiter => subst hN; apply sim_ewigWeiter hO <;> assumption
  case ewigFort => subst hN; apply sim_ewigFort hO <;> assumption
  case rufDann => subst hN; apply sim_rufDann hO <;> assumption
  case dannCallInd => subst hN; apply sim_dannCallInd hO <;> assumption
  case rufCallInd => subst hN; apply sim_rufCallInd hO <;> assumption
  case dannBindCall => subst hN; apply sim_dannBindCall hO <;> assumption
  case dannBindCallInd => subst hN; apply sim_dannBindCallInd hO <;> assumption
  case dannBindCallElse => subst hN; apply sim_dannBindCallElse hO <;> assumption
  case rueckBind => subst hN; apply sim_rueckBind hO <;> assumption
  case dannLeaveTrav => subst hN; apply sim_dannLeaveTrav hO <;> assumption
  case dannNextTrav => subst hN; apply sim_dannNextTrav hO <;> assumption
  case dannLeaveWieder => subst hN; apply sim_dannLeaveWieder hO <;> assumption
  case dannNextWieder => subst hN; apply sim_dannNextWieder hO <;> assumption
  case dannLeaveEwig => subst hN; apply sim_dannLeaveEwig hO <;> assumption
  case dannNextEwig => subst hN; apply sim_dannNextEwig hO <;> assumption
  case peelDannLeave => subst hN; apply sim_peelDannLeave hO <;> assumption
  case peelDannNext => subst hN; apply sim_peelDannNext hO <;> assumption
  case peelSchrumpfLeave => subst hN; apply sim_peelSchrumpfLeave hO <;> assumption
  case peelSchrumpfNext => subst hN; apply sim_peelSchrumpfNext hO <;> assumption
  case peelFreiLeave => subst hN; apply sim_peelFreiLeave hO <;> assumption
  case peelFreiNext => subst hN; apply sim_peelFreiNext hO <;> assumption
  case peelAbbruchLeave => subst hN; apply sim_peelAbbruchLeave hO <;> assumption
  case peelAbbruchNext => subst hN; apply sim_peelAbbruchNext hO <;> assumption
  case dannRet => subst hN; apply sim_dannRet hO <;> assumption
  case rueckCons => subst hN; apply sim_rueckCons hO <;> assumption
  case dannRetBind => subst hN; apply sim_dannRetBind hO <;> assumption
  case rueckConsBind => subst hN; apply sim_rueckConsBind hO <;> assumption
  case rueckGrund => subst hN; apply sim_rueckGrund hO <;> assumption
  case rueckConsGrund => subst hN; apply sim_rueckConsGrund hO <;> assumption
  case dannRetGrund => subst hN; apply sim_dannRetGrund hO <;> assumption
  case dannRegLies => subst hN; apply sim_dannRegLies hO <;> assumption
  case dannRegLiesElseWahr => subst hN; apply sim_dannRegLiesElseWahr hO <;> assumption
  case dannRegLiesElseFalsch => subst hN; apply sim_dannRegLiesElseFalsch hO <;> assumption
  case dannAwaits => subst hN; apply sim_dannAwaits hO <;> assumption
  case dannExchange => subst hN; apply sim_dannExchange hO <;> assumption
  case dannGleit => subst hN; apply sim_dannGleit hO <;> assumption
  case dannGleitLit => subst hN; apply sim_dannGleitLit hO <;> assumption
  case dannGleitVon => subst hN; apply sim_dannGleitVon hO <;> assumption
  case dannGleitNarrowOk => subst hN; apply sim_dannGleitNarrowOk hO <;> assumption
  case dannGleitNarrowElse => subst hN; apply sim_dannGleitNarrowElse hO <;> assumption
  case dannBindAxiom => subst hN; apply sim_dannBindAxiom hO <;> assumption
  case dannBindAxiomElseOk => subst hN; apply sim_dannBindAxiomElseOk hO <;> assumption
  case dannBindAxiomElseGrund => subst hN; apply sim_dannBindAxiomElseGrund hO <;> assumption
  case endeBindAxiomElseOk => subst hN; apply sim_endeBindAxiomElseOk hO <;> assumption
  case endeBindAxiomElseGrund => subst hN; apply sim_endeBindAxiomElseGrund hO <;> assumption

end Gabbro.Stage0
