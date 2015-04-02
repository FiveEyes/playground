//given b, satisfy a * (a + b) = c * c, maximize a.
//http://poj.openjudge.cn/practice/1046/


#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>

using namespace std;

typedef long long ll;

int main() {
  int t;
  cin >> t;
  while(t--) {
    ll a = 0, b, n;
    cin >> b;
    
    if(b & 1) {
      n = (b * b + 1) / 2;
    } else {
      b /= 2;
      if(b & 1) {
        n = (b * b + 1);
      } else {
        n = (b * b / 2 + 2);
      }
      b *= 2;
    }
    a = (n - b) / 2;
    //ll c2 = a * (a + b);
    //ll c = sqrt(c2);
    //printf("%d %d %d\n", a, c2, c * c);
    cout << a << endl;
  }
  return 0;
}
