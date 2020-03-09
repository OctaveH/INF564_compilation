// un exemple de fichier mini-C
// à modifier au fur et à mesure des tests
//
// la commande 'make' recompile mini-c (si nécessaire)
// et le lance sur ce fichier


/*** listes circulaires doublement chaînées ***/


int fact(int n) {
  if (n <= 1) return 1;
  return n * fact(n-1);
}

int main() {
  int n;
  n = 0;
  while (n <= 4) {
    putchar(65 + fact(n));
    n = n+1;
  }
  putchar(10);
  return 0;
}
