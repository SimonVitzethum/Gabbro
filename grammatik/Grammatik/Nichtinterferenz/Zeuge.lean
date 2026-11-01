/-
  File:      Grammatik/Nichtinterferenz/Zeuge.lean
  Subject:   THE WITNESSES of the noninterference theorem: two tenants on one
             machine.

  Declaration `nD`: tables `tabA` (tenant A) and `tabB` (tenant B), one
  slot each, values `0 .. 9`; two lock-free (`atomic`) globals: `konfig`
  (a configuration the kernel domain `K` writes and both tenants read) and
  `zaehler` (a shared counter). Domains `K`, `A`, `B`: `K` may flow to
  everything, `A` and `B` only to themselves.

  Functions:
  * `hauptA`: `tabA[0] = konfig; return`   (tenant A)
  * `hauptB`: `tabB[0] = konfig; return`   (tenant B)
  * `kern`:   `konfig = 3; return`         (kernel domain)
  * `ruhe`:   `return`
  * `zaehlA`: `zaehler = tabA[0]; return`  (A publishes into a shared
    lock-free structure)
  * `zaehlB`: `tabB[0] = zaehler; return`  (B reads it)
  * `leck`:   `if tabA[0] == 0 { tabB[0] = 1 }; return` -- a write to a
    B-observable carrier under an A-dependent branch.

  1. The ADMITTED configuration (roots `hauptA : A`, `hauptB : B`,
     `kern : K`, `ruhe : K`) passes `flussB` (`n1_fluss`): the shared
     structure `konfig` is written by `K` only and read by both. The
     noninterference theorem holds for it (`n1_ni`, every premise
     discharged), and on two concrete runs with the same fixed timetable
     from memories that differ in tenant A's table (`n1_zeuge`).
  2. The SHARED LOCK-FREE COUNTER (roots `zaehlA : A`, `zaehlB : B`) is
     refused for EVERY label of `zaehler` (`n2_abgelehnt`).
  3. The LEAK (root `leck`) is refused for EVERY domain of its root
     (`n3_abgelehnt`), and it VIOLATES noninterference on two concrete
     runs (`n3_verletzt`): same schedule, start memories equal on every
     B-visible carrier, and after three steps B sees `tabB[0] = 1` in one
     run and `0` in the other.
-/
module

public import Grammatik.Nichtinterferenz.Zeuge.Teil1
public import Grammatik.Nichtinterferenz.Zeuge.Teil2
