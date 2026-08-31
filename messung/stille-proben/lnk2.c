/* Dieselben Zeilen, die ersten ZWEI vertauscht: eine statische Deklaration NACH
 * einer nicht-statischen ist ein Fehler. *Die Reihenfolge entscheidet, nicht der Inhalt.* */
int f(void);
static int f(void);
static int f(void) { return 1; }
int main(void){ return f()-1; }
