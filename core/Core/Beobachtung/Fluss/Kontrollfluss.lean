module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

def KontrollflussNIAussage : Prop :=
  FamilienNI .kontrollfluss

end Gabbro.Core.Beobachtung
