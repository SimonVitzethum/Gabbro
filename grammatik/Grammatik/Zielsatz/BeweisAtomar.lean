-- Compatibility shim (Simon's Lean layout, 2026-10-06): the module moved to Grammatik.Zielsatz.Atomar.BeweisAtomar.
-- The coordinator's merge gate probes `import Grammatik.Zielsatz.BeweisAtomar` and `#print axioms
-- Gabbro.Grammatik.Zielsatz.gabbro_ziel`; this one-line re-export keeps that probe valid. Pinned in
-- instrumente/lean-layout-rules.py (PINNED): the layout tool never moves it. Do not add content.
import Grammatik.Zielsatz.Atomar.BeweisAtomar
