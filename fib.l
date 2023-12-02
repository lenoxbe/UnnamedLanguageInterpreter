float n = 3.14;

int Fib(int n){
  if n == 0 {
    return 1;
  } else if n == 1 {
      return 1;
  } else {
      return Fib(n - 1) + Fib(n - 2);
  }
}
for (int i = 0; i < 30; i = i + 1;){
  return Fib(i);
}
