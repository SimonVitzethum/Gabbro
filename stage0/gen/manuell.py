# Hand-written proof bodies of simulation lemmas: rule name -> lines after `:= by`.
BLATT = '''  have hp := blatt_paar (schwanz_normal M f) hO passes keinRuf s hleaf (paar_normal (w := ww) M f) ρ
  rw [hstep] at hp
  generalize hX : execStmt OM passes keinRuf s (M.weltVon f) ρ = X at hp
  cases hp with
  | ok hq =>
    refine ⟨_, RufSchrittG.{n} M f {args} hleaf hhead ?_ _ ρ' neu hX ?_ hkein_nimmt,
      sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩
    all_goals try sim_ziel
'''
M = {}
M['blatt'] = BLATT.replace('{n}', 'blatt').replace('{args}', 'l Γ Λ Λ\' s rest ρ')
M['dannBlatt'] = BLATT.replace('{n}', 'dannBlatt').replace('{args}', 'l Γ Λ Λ\' Λ\'\' s rest k ρ')
