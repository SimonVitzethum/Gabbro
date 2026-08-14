//! **Das Annahmenmanifest -- „bewiesen unter A1…An", maschinenlesbar.**
//!
//! `SYNTAX.md` §12: *„Die Annahmenmenge wird ins Erzeugnis emittiert („bewiesen unter A1…An"),
//! als **Menge von Namen mit Klasse**, nicht als Zahl -- eine Ratsche ueber einer Kardinalzahl
//! greift nicht gegen Austausch."*
//!
//! Deshalb traegt jede Zeile **Name und Klasse**, und die Zaehlung steht darunter statt darueber.
//! Wer eine Annahme austauscht, aendert eine Zeile; die Zahl allein haette sich nicht geruehrt.

use gabbro_syntax::ast::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Klasse {
    /// Eine Sonde ist benannt. Ob sie lief, sagt dieses Manifest nicht -- das sagt der Lauf.
    Falsifizierbar { sonde: String },
    /// Nicht falsifizierbar, **mit Grund**.
    NichtFalsifizierbar { grund: String },
}

#[derive(Debug, Clone)]
pub struct Eintrag {
    pub name: String,
    /// `assume` oder `axiom`.
    pub art: &'static str,
    pub klasse: Klasse,
    /// Bei `assume` der erklaerende Satz, bei `axiom` die Wirkungen.
    pub aussage: String,
}

/// Sammelt die Annahmenmenge eines Baums.
pub fn sammle(baum: &Programm) -> Vec<Eintrag> {
    let mut out = Vec::new();
    sammle_items(&baum.items, &mut out);
    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
}

fn sammle_items(items: &[Item], out: &mut Vec<Eintrag>) {
    for i in items {
        match &i.art {
            ItemArt::Modul(m) => sammle_items(&m.items, out),
            ItemArt::Assume(a) => out.push(Eintrag {
                name: a.name.text.clone(),
                art: "assume",
                klasse: klasse(&a.klasse),
                aussage: a.text.text.clone(),
            }),
            ItemArt::Axiom(a) => out.push(Eintrag {
                name: a.name.text.clone(),
                art: "axiom",
                klasse: klasse(&a.klasse),
                aussage: a
                    .effects
                    .liste
                    .iter()
                    .map(|e| e.art.text())
                    .collect::<Vec<_>>()
                    .join(", "),
            }),
            _ => {}
        }
    }
}

fn klasse(k: &AnnahmeKlasse) -> Klasse {
    match k {
        AnnahmeKlasse::Falsifizierbar(i) => Klasse::Falsifizierbar {
            sonde: i.text.clone(),
        },
        AnnahmeKlasse::NichtFalsifizierbar(t) => Klasse::NichtFalsifizierbar {
            grund: t.text.clone(),
        },
    }
}

/// Zeilenformat, stabil und ohne Werkzeug lesbar:
/// `A<n>\t<name>\t<art>\t<klasse>\t<sonde|grund>\t<aussage>`
pub fn zeige(eintraege: &[Eintrag]) -> String {
    let mut out = String::new();
    out.push_str("-- Annahmenmenge. Die Zusage lautet: bewiesen unter A1…An.\n");
    out.push_str("-- Nr\tName\tArt\tKlasse\tSonde/Grund\tAussage\n");
    for (n, e) in eintraege.iter().enumerate() {
        let (kl, wie) = match &e.klasse {
            Klasse::Falsifizierbar { sonde } => ("falsifizierbar", sonde.as_str()),
            Klasse::NichtFalsifizierbar { grund } => ("nicht-falsifizierbar", grund.as_str()),
        };
        out.push_str(&format!(
            "A{}\t{}\t{}\t{}\t{}\t{}\n",
            n + 1,
            e.name,
            e.art,
            kl,
            wie,
            e.aussage
        ));
    }
    out.push_str(&format!("-- {} Annahmen\n", eintraege.len()));
    out
}
