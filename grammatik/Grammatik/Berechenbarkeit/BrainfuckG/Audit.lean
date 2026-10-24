import Grammatik.Berechenbarkeit.BrainfuckG.Nimm
import Grammatik.Berechenbarkeit.BrainfuckG.ProgrammAkzeptiert
import Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses
import Grammatik.Berechenbarkeit.BrainfuckG.SchrittWitnesses
import Grammatik.Berechenbarkeit.BrainfuckG.LegeWitnesses

/-! Axiom audit of the Brainfuck-on-G modules. -/

#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.MultiRep.lese
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.plusEins_eval
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.minusEins_eval
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.nimm_leer
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.nimm_voll
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.lege_ok
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.lege_voll
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.LegeWitnesses.lege_ok_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.LegeWitnesses.lege_voll_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.befehl_schritt
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.befehl_voll
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.SchrittWitnesses.befehl_schritt_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.SchrittWitnesses.befehl_voll_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.befehl_genau
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.durchgang
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.durchgang_platz
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.programm_vollstaendig
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.programm_korrekt
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.programm_haelt
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses.programm_vollstaendig_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses.programm_ok_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses.programm_haelt_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammAkzeptiert.prog_klasse_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammAkzeptiert.prog_accepted_zeuge
#print axioms Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammAkzeptiert.prog_exec_zeuge
