//! **Was kostet EINE Umgebung, und wie oft wird sie gebaut?**
//!
//! 14 Module rufen `Umgebung::sammle`, sechs bauen zusaetzlich den Aufrufgraphen -- jeder
//! fuer sich, ueber denselben Baum. Diese Messung sagt, was das kostet, bevor irgendein
//! Cache geplant wird: *ein Cache ueber einer Arbeit, die man auch weglassen kann, ist die
//! teurere Loesung.*
fn main() {
    let datei = std::env::args().nth(1).unwrap();
    let q = std::fs::read_to_string(&datei).unwrap();
    let t = std::time::Instant::now();
    let (baum, mut absagen) = gabbro_syntax::lies(&datei, &q);
    println!("lesen (lex+parse)   {:?}", t.elapsed());

    let t = std::time::Instant::now();
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    let eine = t.elapsed();
    println!("Umgebung::sammle    {eine:?}");

    let t = std::time::Instant::now();
    let _g = gabbro_check::aufrufgraph::erhebe_mit(&baum, &u);
    let graph = t.elapsed();
    println!("Aufrufgraph         {graph:?}");

    let t = std::time::Instant::now();
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    println!("alle Paesse         {:?}", t.elapsed());
    println!();
    println!("18 Umgebungen kosten {:?}, 6 Graphen {:?}", eine * 18, graph * 6);
}
