/* C11 6.2.2p4: eine NICHT-statische Deklaration NACH einer statischen erbt die
 * interne Bindung -- und `cc -Werror` sagt dazu nichts. */
static int f(void);
int f(void);
static int f(void) { return 1; }
int main(void){ return f()-1; }
