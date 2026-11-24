module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

def AbsturzNIAussage : Prop :=
  ProtokollwahlNI fun
    | .absturz => True
    | _ => False

end Gabbro.Core.Beobachtung
