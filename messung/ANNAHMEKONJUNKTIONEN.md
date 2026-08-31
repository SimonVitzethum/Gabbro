# Eine Annahme, zwei Behauptungen, ein Falsifikator

**Gemessen 2026-08-31, Anlass «B40».** `dma_kohaerent` trug zwei unabhängige Behauptungen
unter einem Namen:

| | |
|---|---|
| **Kohärenz** | Gerät und Kern sehen dieselben Zellen ohne Cache-Pflege |
| **Ordnung** | zwei volatile Zugriffe werden dem Gerät in Programmreihenfolge sichtbar |

*Die zweite folgt nicht aus der ersten.* Auf AArch64 gilt die Ordnungsaussage für
Device-nGnRnE, aber C11-`volatile` erzeugt dort **keine Barriere gegenüber normalem
Speicher**: ein Deskriptorschreiben in kohärentem RAM und ein anschließendes
Doorbell-Schreiben ins Gerät können ohne `DSB` in falscher Reihenfolge sichtbar werden.

> **Und der eine Falsifikator läuft auf x86 und geht durch.** Eine grüne Sonde für eine
> Annahme, die auf der anderen Hälfte des Bestands falsch ist — genau die Bewegung, gegen
> die die Annahmenschicht gebaut ist: *eine Annahme, die nicht lief, darf nie aussehen wie
> eine, die hielt.*

Caprock hat beide Architekturen. `aarch64` bleibt in diesem Ordner versiegelt — **hier wird
kein aarch64-Code geschrieben.** Was `arch` an `assume` möglich macht, ist nur, *sagbar zu
machen, dass eine Annahme dort nicht gilt.*

## Die Zählung, und ihre zwei Hälften sind verschieden viel wert

```
$ ./instrumente/zaehle-verdrahtung.py     # V5 zählt Wörter ohne Programm, nicht dies
```

Die Frage war: **wie viele der übrigen `assume`-Einträge haben dieselbe Gestalt?** Sie
zerfällt in eine maschinelle und eine menschliche Hälfte, und die Differenz ist der Ertrag.

| | Zahl | wie gewonnen |
|---|---:|---|
| `assume`-Einträge im sauberen Korpus | **41** | Textzählung |
| verschiedene Namen | **34** | dieselbe, entdoppelt |
| maschinell markiert: `;` oder ` und ` im Text | **17** | rein mechanisch |
| **davon nach Urteil echte Konjunktionen** | **8** | Urteil, Zeile für Zeile unten |

**Der maschinelle Filter überzählt um mehr als das Doppelte**, und er steht trotzdem da: er
ist reproduzierbar, das Urteil ist es nicht. *Eine Zahl belegt ihren Nenner, nicht ihre
Beschriftung* (W25) — der Nenner hier ist „Texte mit einem Satzzeichen", nicht „Annahmen mit
zwei Pflichten".

## Das Urteil, je Eintrag

Kriterium: **zwei endliche Aussagen, von denen jede falsch sein kann, während die andere
hält.** Eine Folgerung, eine Umkehrung und eine Wiederholung zählen nicht.

| Name | Urteil | warum |
|---|---|---|
| `vtd_te_wirksam` | **JA** | TE schaltet scharf · DMA ohne Kontexteintrag faultet — das zweite folgt nicht |
| `vtd_te_wirkt` | **JA** | derselbe Text in `F02.gab`, dieselbe Teilung |
| `gcmd_kein_rmw` | **JA** | GCMD wird ganz geschrieben · ein nicht mitgeschriebenes Bit wird gelöscht |
| `quelle_endet` | **JA** | endlich viele Puffer · sie *meldet* `Erschoepft` — eine endliche Quelle kann trotzdem hängen |
| `token_verbraucht` | **JA** | jeder Durchgang verbraucht ein Token · ein DTB hat endlich viele |
| `eingabe_endet` | **JA** | endlich viele Sätze · `lenof` nennt ihre Zahl |
| `gast_bleibt_in_seinem_raum` | **JA** | springt nur an seine Eintrittsadresse · bleibt in seinem Raum |
| `virtq_geraet_schreibt_used` | **JA** | das Gerät schreibt · der Treiber liest nur noch — **zwei Subjekte** |
| ~~`dma_kohaerent`~~ | **war JA** | am 2026-08-31 geteilt; die Zahl war vorher **9** |
| `dma_kohaerent` (neu) | nein | `Gerät und Kern` verbindet Subjekte, keine Sätze — ein Fehlalarm des Filters |
| `dma_veroeffentlichung_braucht_barriere` | nein | die zweite Hälfte ist die Umkehrung der ersten |
| `masks_irq_schuetzt_wie_eine_sperre` | nein | die zweite folgt aus der ersten |
| `mmu_schreibt_nur_a_und_d` | nein | Wiederholung derselben Aussage |
| `fsts_pfo_verwirft` | nein | `und` verbindet zwei Bits, nicht zwei Sätze |
| `geraet_quittiert_merkmale` | nein | eine Bedingung, kein zweiter Satz |
| `x2apic_zweischritt` | nein | `EN und EXTD` ist ein Zustand, kein Paar von Aussagen |
| `zeitgeber_tickt` · `tickt` | nein | die zweite Hälfte begründet, sie behauptet nicht |

**Und `client_calls_or_endpoint_revoked` und `device_completes_or_faults` sind DISJUNKTIONEN**
— dieselbe Bauart, andere Richtung, und der Filter sieht sie gar nicht, weil kein `;` und
kein `und` darin steht. *Ob eine Disjunktion unter einem Falsifikator dasselbe Problem hat,
ist hier nicht gemessen:* eine Sonde, die eine der beiden Seiten herstellt, entlastet die
Annahme zu Recht — aber welche Seite sie hergestellt hat, sagt sie nicht.

## Was ungemessen bleibt

* **Sieben von acht sind nicht geteilt.** Nur `dma_kohaerent` ist zerlegt, weil sie den
  Anlass gab und weil ihre zweite Hälfte auf einer Architektur des Bestands **falsch** ist.
  Bei den anderen sieben ist die Teilung Arbeit ohne gemessenen Mangel (Regel A) — sie steht
  hier als benannte Schuld und nicht als erledigt.
* **`A005` liest den Text nicht.** Der Prüfer sieht nur, ob die genannte Maschine in dieser
  Einheit vorkommt. Eine Konjunktion unter einem Namen bleibt schreibbar, und sie muss es
  bleiben: *ein Wächter gegen Konjunktionen in Prosa wäre ein Textwächter und kein Pass.*
* **`beispiele/gift` steht nicht im Nenner.** Was nur dort steht, fehlt in beiden Zahlen.
* **Der Falsifikator selbst ist ungeprüft.** Dass `sonde_dma_kohaerenz` und
  `sonde_dma_reihenfolge` verschiedene Dinge messen, sagt heute niemand nach — `N024` hält
  nur, dass ein Name nicht zwei Pflichten trägt. *Zwei Namen für dieselbe Sonde fielen
  nirgends auf.*
