// un exemple de fichier mini-C
// à modifier au fur et à mesure des tests
//
// la commande 'make' recompile mini-c (si nécessaire)
// et le lance sur ce fichier


/*** listes circulaires doublement chaînées ***/

//int f(int x) {}
//int main() { f(); }

int f(int x, int y, int z, int t) {
  if (!x) return 10;
  putchar(x);
  return f(y, z, t, x);
}

int main() {
  putchar(f('A', 'B', 'C', 0));
  return 0;
}
