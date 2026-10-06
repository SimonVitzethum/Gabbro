# Placement rules for instrumente/lean-layout.py (executed inside it; `rules(folder, table)` is defined there).
# First matching regex wins; the second element is the sub-folder below `folder` (may be nested).
# Keep every resulting folder well under 20 entries: new lanes add files, and the check is a hard gate.

rules('grammatik/Grammatik/X86', [
    # --- GabbroV bridge modules (lanes write them under X86/ because lane ownership allows only that tree)
    (r'^Gv[A-Z]\w*$', '../GabbroV'),
    # --- the coherent multi-core machine and its families
    (r'^HwKapstein', 'Hw/Kapstein'),
    (r'^Hw(Paging|PagingLarge|Translate|TranslateFull|SegTlb|MemTypesWC|WcOrdering|DrainGeneric|ForwardingGeneric)$', 'Hw/Speicher'),
    (r'^Hw(Faults|PreciseFault|Interrupts|NestedInterrupts|PageFaultDelivery|FeatureGates|FeatureStep)$', 'Hw/Ausnahmen'),
    (r'^Hw(LoadedImage|BildFamilien|BildInstanzen)$', 'Hw/Bild'),
    (r'^Hw(Fp|Vector|ContextState|Xsave|Avx)', 'Hw/Gleitkomma'),
    (r'^Hw', 'Hw/Familien'),
    (r'^(HardwareAssumptions|HardwareExecution|HardwareFaults|ExtendedExecution|DeviceBusHardwareExecution|DeviceCommonExecution|DeviceHardwareForms|InterruptDescriptorHardware|ExceptionPriorityHardware)$', 'Hw/Grundlage'),
    # --- composition ledgers
    (r'^Compose(ImageFetch|MapPerms|PatchBytes|RelocRedecode|LoaderBias|GuardPages|SupportBytes|PermCheck|VaCheck|RelaxLayout)$', 'Compose/Bild'),
    (r'^Compose(ContractCall|ContractReturn|CallLogGhost|StackAbi|UnwindTable|SpillPrivacy|RegionCeil|HandlerTable|Entry\w+|BindingSurface|ProfileSelect|AcceptedConsumers)$', 'Compose/Vertraege'),
    (r'^Compose', 'Compose/Buchungen'),
    # --- optimiser
    (r'^Optimization(Rules|Witnesses)$', 'Opt/Regeln'),
    (r'^(Opt\w*Sel|InstructionSelection)$', 'Opt/Auswahl'),
    (r'^(Opt(LicmLoop|UnrollBound|StrengthRed|InlineCall|VectorGate)|StaerkeReduktion|InvariantenOpt|AufrufOpt)$', 'Opt/Schleifen'),
    (r'^Opt(FoldConst|FoldCopy|CfgSimp|CsePure|CseLoad|DceDead|DceStore|RangeElim|BoundElim|OverflowElim|DivGuard|PeepholeDisp|PeepholeFlags|RematConst|AliasCommute|CoalesceMove)$', 'Opt/Vereinfachung'),
    (r'^(Opt(AllocLinear|SpillFresh|LayoutAlign)|RegisterInterference|SpillPrivate|ParallelMoves)$', 'Opt/Register'),
    # --- the pipeline
    (r'^Pipeline(Float|FloatNaN|Tables|BlockTables|Atomics|AtomicsBind|AtomicsBlock)$', 'Pipeline/Ausdruecke'),
    (r'^Pipeline(Calls|CallsBlock|CallsExec|CallsN|Spill|SpillHoming|SpillSplice)$', 'Pipeline/Aufrufe'),
    (r'^Pipeline(Loops|Work|WorkBranches|WorkPath|BlockInduct|ChunkDerive|ChunkIte)$', 'Pipeline/Ablauf'),
    (r'^Pipeline(Link|LinkMulti|LinkRel8|LoadedAll|Profiles|ProfilesReloc|Tso|TsoStore)$', 'Pipeline/Binden'),
    (r'^Pipeline', 'Pipeline/Kern'),
    # --- bridge from the target memory to the source model
    (r'^(Tso\w+|BridgeRead|BridgeWrite|CarrierTraceBridge|ObservationProjection)$', 'Bruecke'),
    # --- store buffer and locked instructions
    (r'^(TSO|TSOHistory|TSOTrace|FenceDrain|MfenceDrainOwn|LfenceLoadNarrow|SfenceStoreNarrow|ReleaseAcquire|WordAccessGrouping|WordAtomicity|WordDrainInterleaving|AtomicPayload)$', 'TSO/Kern'),
    (r'^(CasDivergenceRec|CasRetryBound|LockCmpxchgSuccess|LockXaddFetch|LockedOps|LockedInstructionExecution|XchgOrderNeed|ConcurrentIntegerExecution)$', 'TSO/Verriegelt'),
    # --- instruction families
    (r'^(Int[A-Z]\w*|IntegerCore\w*|IntegerHardwareForms)$', 'Befehle/Ganzzahl'),
    (r'^(MulDiv\w*|Narrow\w*|Shift(Codec|Logic)|BitCount|BitScan|ByteSwap)$', 'Befehle/Arithmetik'),
    (r'^(Compact\w+|LeaPureForm|ZeroIdiomXor|ShortBranchEncoding)$', 'Befehle/Kompakt'),
    (r'^(ScalarFloat\w*|Float\w+|FpControlHardwareForms|Cvtsi2sdW64)$', 'Befehle/Gleitkomma'),
    (r'^(Vector\w+|Avx2\w+)$', 'Befehle/Vektor'),
    (r'^(ControlCodec|ControlFlow|IndirectCallProv|IndirectControlHardwareForms|JumpTableCert|Rel8Reach|BranchLayout|FetchedCondBranch|CallAlign16|BlockSequence646|DecodeFault|GateStub)$', 'Befehle/Kontrolle'),
    (r'^ISA\w*$', 'Befehle/ISA'),
    (r'^Sse\w+$', 'Befehle/Sse'),
    (r'^String\w+$', 'Befehle/Zeichenketten'),
    (r'^System\w+$', 'Befehle/System'),
    (r'^Locked\w+$', 'TSO/Verriegelt'),
    # --- foundations
    (r'^(Typen|Wort|Ganzzahl|Stapel|Vektor|Gleitprofil|Bild|Codec|Ausfuehrung|Byteschritt)$', 'Kern'),
    (r'^(ArchitecturalFlags|FlagBeweis|FlagDependencies|AuxiliaryCarryRows|ConditionalMove|FeatureProfile|CpuFeatureHardwareForms)$', 'Flags'),
    (r'^(Speicher|SpeicherKommutation|Regionen|RegionFresh|RegionSeparation|Zugriffe|AccessList|AccessExecution|AddressEncoding|EffectiveAddress|AddressedHardwareExecution|CodeImmutability|ImageStoreFrame|TableLayout|MemoryTypeHardwareExecution|Disp0Frame)$', 'Speicher'),
    # --- validation of the generated image against the source
    (r'^(Validator\w*|Validation\w*|DecoderSoundness|DecodingCoverage|GenericSourceByteCert|ContractSites|PayloadResidue|OverlapRefusal)$', 'Validierung'),
    (r'^(Source\w+|ExpressionLowering\w*)$', 'Quelle'),
    (r'^(LoadedExecution|RelocatedExecution|Relokation|EntryExecution|EntryState|StackExecution|StackUnwind)$', 'Laden'),
    (r'^(BudgetExecution|CostSummary|DerivedWorkBound|TimeTransfer)$', 'Kosten'),
    (r'^OpcodeLedger', 'Opcode'),
])

rules('grammatik/Grammatik/Zielsatz', [
    (r'^Atomar\w*|^BeweisAtomar$', 'Atomar'),
    (r'^(Akzeptiert|AkzeptiertZeuge|Spec|SpecProben|Beweis|Proben|ProbenG1|ProbenW1)$', 'Kern'),
    (r'^(Faeden|FaedenVor|FaedenZeuge|Ruhe|RuheNutzer|RuheZeuge|PoolSym|PoolZeuge|Verbund|VerbundZeuge)$', 'Faeden'),
    (r'^(Invarianten|InvariantenZeuge|Masken|MaskenZeuge|Divergenz|Schwach|FolgeZiel|NeverAsm)$', 'Eigenschaften'),
])

rules('grammatik/Grammatik/Speichermodell', [
    (r'^Atomar\w*$', 'Atomar'),
    (r'^(DRF|GXMaschine|MaschineW|RMW|Sicht|Zaehler|ZaehlerW|SperreSemA|Zeuge)$', 'Maschine'),
])

rules('bruecke/Bruecke', [
    (r'^Instanz\d+$', 'Instanzen'),
])

rules('grammatik/Grammatik/Zertifikat', [
    (r'^G\d{1,2}_', 'Reihe00'),
    (r'^G1\d\d_', 'Reihe01'),
    (r'^G2\d\d_', 'Reihe02'),
    (r'^G3\d\d_', 'Reihe03'),
    (r'^G4\d\d_', 'Reihe04'),
    (r'^G5\d\d_', 'Reihe05'),
    (r'^G6\d\d_', 'Reihe06'),
    (r'^G7\d\d_', 'Reihe07'),
    (r'^G[89]\d\d_', 'Reihe08'),
])

rules('grammatik/Grammatik/CParser', [
    (r'.*', '../CBackend/Parser'),
])

rules('grammatik/Grammatik', [
    (r'^(Syntax|Typen|Konstanten|Fehler|Satz|Zucker|Marken|MarkenInstanzA|Profil|Koernung|Bits|Geist|Extraktion|Ziel)$', 'Kern/Syntax'),
    (r'^(Semantik|Maschine|MaschinenKette|Erhaltung|ErhaltungT4|Terminierung|Ueberlauf|Fristlauf|Durchgaenge|Budget|Adressraum|Syscall|SyscallPaarung|Geraet)$', 'Kern/Semantik'),
    (r'^(Sperre\w*|Sperr\w+|RelySperre|FremdSperre|MitRuhe\w*|ExportSperre)$', 'Nebenlaeufigkeit/Sperren'),
    (r'^(Rennfrei\w+|Interferenz\w*|EigenZustand\w*)$', 'Nebenlaeufigkeit/Rennfreiheit'),
    (r'^(Unterbrechung|Verschachtelt|Verklemmung|LesenStabil|StabilBewacht|Trennung|Schiebung|Wettlauf|Geteilt|WacheGlobal|DisziplinBedarf|FadenMaschine|FadenMerkmal|MehrfadenLauf|MehrfadenZeuge|TravAwaits\w+)$', 'Nebenlaeufigkeit/Allgemein'),
    (r'^(Ruf\w+|FremdRuf|HoareRuf|HoareRegeln)$', 'Logik/Ruf'),
    (r'^(Folge\w*|Fortschritt\w*|Lebendigkeit\w*|KostenG\w*)$', 'Logik/Fortschritt'),
    (r'^(AxiomVertrag|VertragOrtB|VertragsFuss|AntwortOrte|QLeer|RahmenTreu|HandlerKongruenz|EinpassenVoll|Komposition|Uebersetzung)$', 'Logik/Vertraege'),
    (r'^ZielOrt(Rahmen\w*|Inv\w*|Ax\w*|Einfaden\w*|Mehrfaden)$', 'Zielsatz/ZielOrt/Rahmen'),
    (r'^ZielOrt(Geraet\w*|Sperre\w*|Beweis)$', 'Zielsatz/ZielOrt/Geraet'),
    (r'^ZielOrt\w*$', 'Zielsatz/ZielOrt/Grundlage'),
    (r'^(CForm\w*)$', 'CBackend/Formen'),
    (r'^(CSemantik|CSpeicher|CSLInvariante\w*|CText\d+\w*|CTicket|CNebenlaeufig|ZeichenfolgeC|ZeichenfolgeGebunden|CloneHandoff)$', 'CBackend/Semantik'),
    (r'^(Korrespondenz\w*|KorrOk\w+|Pflicht\d+|Referenz\w*)$', 'Korrespondenz/Allgemein'),
    (r'^(Kette\w*|Schlusssatz\w*)$', 'Korrespondenz/Kette'),
    (r'^(Korpus\d+|Export\d+|GenOblig\d+|TermIdent\d+)$', 'Korrespondenz/Korpus'),
    (r'^(Zeugnis\w*|Zertifikate)$', 'Korrespondenz/Zeugnis'),
    (r'^Schablonen\w*$', 'Bausteine/Schablonen'),
    (r'^(Arena\w*|Bibliothek)$', 'Bausteine/Arena'),
    (r'^(Gleitkomma\w*|GleitZeuge)$', 'Bausteine/Gleitkomma'),
    (r'^(AuditFinal|AuditW5|AuditZiel|BitVecProben|BlattGegenbeispiel|ProbeD|SimPruef|SonstLeaveZeuge|HelferZeuge|InvZeuge)$', 'Proben'),
])

# Compatibility shims at an OLD module path. They are never moved. The coordinator's merge gate still probes
# `import Grammatik.Zielsatz.BeweisAtomar` for the goal-theorem axioms (it lives outside the repo, in .claude/).
PINNED.update([
    'grammatik/Grammatik/Zielsatz/BeweisAtomar.lean',
])
