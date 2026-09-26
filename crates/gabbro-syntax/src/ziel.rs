//! **System calls as named variables, bound per target** (OFFEN O31, Opus agent L).
//!
//! A gate written `syscall g(…) -> … or R via V requires … effects … costs …;` carries
//! no ABI of its own. `syscall V;` declares the variable; a `target T abi A arch X
//! { V = number N regs in {…} regs out {…} clobbers {…} errors {…} assume a falsifier s; }`
//! block binds it for one kernel ABI; `target T;` selects the active one when a unit
//! carries several blocks. This module does the one mechanical step: after the whole unit
//! is read, it fills every `via` gate's ABI fields from the ACTIVE target's binding, so
//! every later pass, the emitter and the exporter read an ordinary gate. What may be wrong
//! with a binding (unbound, twice, undeclared, two targets under one assumption, a literal
//! gate beside a target) is refused by the checker (`gabbro-check/src/zielbindung.rs`,
//! `N562`-`N567`), not here -- the parser checks nothing but form.
//!
//! **The active target** is, in this order: the `GABBRO_TARGET` environment variable
//! (`gabbro … --target T` sets it; it must name a block, else nothing is bound and the
//! checker says why), the one `target T;` selection, or the one block name a unit carries.

use crate::ast::*;

/// The placeholder binding of a `via` gate before (or without) a target.
pub fn platzhalter(v: &Ident) -> ZielBindung {
    let leer = |t: &str| Ident { text: t.to_string(), span: v.span };
    ZielBindung {
        var: v.clone(),
        nummer: Expr { art: ExprArt::Zahl(0), span: v.span },
        regs_in: Vec::new(),
        regs_out: Vec::new(),
        stapel: Vec::new(),
        clobbers: Vec::new(),
        errors: Vec::new(),
        errno_werte: Vec::new(),
        paarung: SyscallPaarung::Annahme {
            annahme: leer(""),
            klasse: AnnahmeKlasse::Falsifizierbar(leer("")),
        },
        span: v.span,
    }
}

/// What a unit says about targets, collected once.
#[derive(Debug, Default, Clone)]
pub struct Zielbild {
    /// Every binding block, in source order.
    pub bloecke: Vec<ZielDecl>,
    /// Every `target T;` selection, in source order.
    pub wahlen: Vec<Ident>,
    /// `GABBRO_TARGET`, when set and non-empty.
    pub vorgabe: Option<String>,
    /// The active target's name, if one is determined AND a block carries it.
    pub aktiv: Option<String>,
}

impl Zielbild {
    /// The distinct block names, in first-seen order.
    pub fn namen(&self) -> Vec<String> {
        let mut aus: Vec<String> = Vec::new();
        for b in &self.bloecke {
            if !aus.contains(&b.name.text) {
                aus.push(b.name.text.clone());
            }
        }
        aus
    }

    /// `(abi, arch)` of the active target (its first block).
    pub fn aktive_abi(&self) -> Option<(String, String)> {
        let n = self.aktiv.as_ref()?;
        self.bloecke.iter().find(|b| &b.name.text == n).and_then(|b| match &b.art {
            ZielArt::Block { abi, arch, .. } => Some((abi.text.clone(), arch.text.clone())),
            ZielArt::Wahl => None,
        })
    }

    /// The active target's binding of `var` (the first, if bound twice).
    pub fn bindung(&self, var: &str) -> Option<(&ZielDecl, &ZielBindung)> {
        let n = self.aktiv.as_ref()?;
        for b in &self.bloecke {
            if &b.name.text != n {
                continue;
            }
            if let ZielArt::Block { bindungen, .. } = &b.art {
                if let Some(x) = bindungen.iter().find(|x| x.var.text == var) {
                    return Some((b, x));
                }
            }
        }
        None
    }
}

fn sammle<'a>(items: &'a [Item], aus: &mut Zielbild) {
    for it in items {
        match &it.art {
            ItemArt::Modul(m) => sammle(&m.items, aus),
            ItemArt::Ziel(z) => match &z.art {
                ZielArt::Wahl => aus.wahlen.push(z.name.clone()),
                ZielArt::Block { .. } => aus.bloecke.push(z.clone()),
            },
            _ => {}
        }
    }
}

/// The unit's targets and the active one (see the module comment for the order).
pub fn zielbild(baum: &Programm) -> Zielbild {
    let mut z = Zielbild::default();
    sammle(&baum.items, &mut z);
    z.vorgabe = std::env::var("GABBRO_TARGET").ok().filter(|s| !s.is_empty());
    let namen = z.namen();
    let mut wahl_namen: Vec<String> = z.wahlen.iter().map(|w| w.text.clone()).collect();
    wahl_namen.dedup();
    let gewollt: Option<String> = if let Some(v) = &z.vorgabe {
        // An override applies only to a unit that has targets at all: a unit without
        // `target` blocks has no `via` gate to bind, and its literal gates stay its own.
        if namen.is_empty() { None } else { Some(v.clone()) }
    } else if wahl_namen.len() == 1 {
        Some(wahl_namen[0].clone())
    } else if wahl_namen.is_empty() && namen.len() == 1 {
        Some(namen[0].clone())
    } else {
        None
    };
    z.aktiv = gewollt.filter(|g| namen.contains(g));
    z
}

fn fuelle(items: &mut [Item], bild: &Zielbild) {
    for it in items {
        match &mut it.art {
            ItemArt::Modul(m) => fuelle(&mut m.items, bild),
            ItemArt::Syscall(s) => {
                let Some(v) = &s.via else { continue };
                let Some((block, b)) = bild.bindung(&v.text) else { continue };
                let ZielArt::Block { abi, arch, .. } = &block.art else { continue };
                s.abi = abi.clone();
                s.arch = arch.clone();
                s.nummer = b.nummer.clone();
                s.regs_in = b.regs_in.clone();
                s.regs_out = b.regs_out.clone();
                s.stapel = b.stapel.clone();
                s.clobbers = b.clobbers.clone();
                s.errors = b.errors.clone();
                s.errno_werte = b.errno_werte.clone();
                s.paarung = b.paarung.clone();
                s.ziel = Some(block.name.clone());
            }
            _ => {}
        }
    }
}

/// Fills every `via` gate from the active target's binding. Idempotent.
pub fn binde(baum: &mut Programm) {
    let bild = zielbild(baum);
    if bild.aktiv.is_none() {
        return;
    }
    fuelle(&mut baum.items, &bild);
}

/// The same fill for ONE named target (the checker holds inactive bindings against the
/// gate's shape with it): a copy of `s` bound by `block`'s binding `b`.
pub fn gebunden(s: &SyscallDecl, block: &ZielDecl, b: &ZielBindung) -> SyscallDecl {
    let mut t = s.clone();
    if let ZielArt::Block { abi, arch, .. } = &block.art {
        t.abi = abi.clone();
        t.arch = arch.clone();
    }
    t.nummer = b.nummer.clone();
    t.regs_in = b.regs_in.clone();
    t.regs_out = b.regs_out.clone();
    t.stapel = b.stapel.clone();
    t.clobbers = b.clobbers.clone();
    t.errors = b.errors.clone();
    t.errno_werte = b.errno_werte.clone();
    t.paarung = b.paarung.clone();
    t.ziel = Some(block.name.clone());
    t
}
