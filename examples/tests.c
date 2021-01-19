// Random tests.

[[rc::returns("void")]]
void test1(){
  long long ll = 0;
  long l = 0;
  int i = 0;
  short s = 0;
  char c = 0;

  if(ll == l) return;
  if(ll == l) return;
  if(ll == i) return;
  if(ll == s) return;
  if(ll == c) return;

  if(!ll) return;
  if(!l) return;
  if(!i) return;
  if(!s) return;
  if(!c) return;

  return;
}
