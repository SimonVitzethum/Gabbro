/-! ## The source guest boundary -/

/-- The current source form contains no service-binding field. Diagnose the
    excluded register-state/unknown-ABI cases before the missing service.
    This refusal is shared by canonical elaboration and Stage 0; neither can
    promote the historical `assume` name to a software-isolation proof. -/
def gastQuelleFehler (arch : String) (registers : List SRegBind) : String :=
  if (wertVon .arch arch).isNone then "entrust: unknown userspace ABI"
  else if !registers.isEmpty then
    "entrust: register-state or privileged transfer is excluded"
  else "entrust: missing isolation service binding"

/-- Source-level admission needs the explicit C08 service binding that the
    current trustT constructor does not yet retain. No name-only candidate
    record stands in for the canonical, typed GuestBoundary. -/
theorem gastQuelle_ohne_dienst (arch : String)
    (ha : (wertVon .arch arch).isNone = false) :
    gastQuelleFehler arch [] = "entrust: missing isolation service binding" := by
  simp [gastQuelleFehler, ha]

end Gabbro.Grammatik.Parser.ProfilBindung
