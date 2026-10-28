import Runner

/-! The axioms of the runner's theorems, read by the Lean guardian (stage 8): each must depend on exactly
`propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms Runner.Beweis.runner_ok
#print axioms Runner.Beweis.step_ok
#print axioms Runner.Beweis.image_ok
#print axioms Runner.Beweis.runner_zeuge
#print axioms Runner.Beweis.zeuge_ir
#print axioms Runner.Beweis.zeuge_x86
#print axioms Runner.X86.decode_enc
