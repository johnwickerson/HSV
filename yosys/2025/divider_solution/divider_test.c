// This is something I wrote to help me to convince myself
// that I was really hitting all the possible quotients and
// remainders. It's not essential; I just thought I'd
// include it with my model answer because it was part of my
// own thought process.

#include <stdio.h>

int main() {

  char hits[32][32];
  int quo;
  int rem;
  int misscount = 0;
  int hitcount = 0;

  printf ("Starting.\n");

  for (int i=0; i<32; i++) {
    for (int j=0; j<32; j++) {
      hits[i][j] = 0;
    }
  }
  
  for (int num=0; num<32; num++) {
    for (int den=1; den<32; den++) {
      quo = num / den;
      rem = num % den;
      hits[quo][rem] = 1;
    }
  }

  for (int i=0; i<32; i++) {
    for (int j=0; j<32; j++) {
      if (hits[i][j] == 0) {
	misscount++;
      } else {
	hitcount++;
	printf ("Hitting quo=%2d, rem=%2d.\n", i, j);
      }
    }
  }
  printf ("Done. Had %d misses and %d hits.\n", misscount, hitcount);
}

/*
Starting.
Hitting quo= 0, rem= 0.
Hitting quo= 0, rem= 1.
Hitting quo= 0, rem= 2.
Hitting quo= 0, rem= 3.
Hitting quo= 0, rem= 4.
Hitting quo= 0, rem= 5.
Hitting quo= 0, rem= 6.
Hitting quo= 0, rem= 7.
Hitting quo= 0, rem= 8.
Hitting quo= 0, rem= 9.
Hitting quo= 0, rem=10.
Hitting quo= 0, rem=11.
Hitting quo= 0, rem=12.
Hitting quo= 0, rem=13.
Hitting quo= 0, rem=14.
Hitting quo= 0, rem=15.
Hitting quo= 0, rem=16.
Hitting quo= 0, rem=17.
Hitting quo= 0, rem=18.
Hitting quo= 0, rem=19.
Hitting quo= 0, rem=20.
Hitting quo= 0, rem=21.
Hitting quo= 0, rem=22.
Hitting quo= 0, rem=23.
Hitting quo= 0, rem=24.
Hitting quo= 0, rem=25.
Hitting quo= 0, rem=26.
Hitting quo= 0, rem=27.
Hitting quo= 0, rem=28.
Hitting quo= 0, rem=29.
Hitting quo= 0, rem=30.
Hitting quo= 1, rem= 0.
Hitting quo= 1, rem= 1.
Hitting quo= 1, rem= 2.
Hitting quo= 1, rem= 3.
Hitting quo= 1, rem= 4.
Hitting quo= 1, rem= 5.
Hitting quo= 1, rem= 6.
Hitting quo= 1, rem= 7.
Hitting quo= 1, rem= 8.
Hitting quo= 1, rem= 9.
Hitting quo= 1, rem=10.
Hitting quo= 1, rem=11.
Hitting quo= 1, rem=12.
Hitting quo= 1, rem=13.
Hitting quo= 1, rem=14.
Hitting quo= 1, rem=15.
Hitting quo= 2, rem= 0.
Hitting quo= 2, rem= 1.
Hitting quo= 2, rem= 2.
Hitting quo= 2, rem= 3.
Hitting quo= 2, rem= 4.
Hitting quo= 2, rem= 5.
Hitting quo= 2, rem= 6.
Hitting quo= 2, rem= 7.
Hitting quo= 2, rem= 8.
Hitting quo= 2, rem= 9.
Hitting quo= 3, rem= 0.
Hitting quo= 3, rem= 1.
Hitting quo= 3, rem= 2.
Hitting quo= 3, rem= 3.
Hitting quo= 3, rem= 4.
Hitting quo= 3, rem= 5.
Hitting quo= 3, rem= 6.
Hitting quo= 3, rem= 7.
Hitting quo= 4, rem= 0.
Hitting quo= 4, rem= 1.
Hitting quo= 4, rem= 2.
Hitting quo= 4, rem= 3.
Hitting quo= 4, rem= 4.
Hitting quo= 4, rem= 5.
Hitting quo= 5, rem= 0.
Hitting quo= 5, rem= 1.
Hitting quo= 5, rem= 2.
Hitting quo= 5, rem= 3.
Hitting quo= 5, rem= 4.
Hitting quo= 6, rem= 0.
Hitting quo= 6, rem= 1.
Hitting quo= 6, rem= 2.
Hitting quo= 6, rem= 3.
Hitting quo= 7, rem= 0.
Hitting quo= 7, rem= 1.
Hitting quo= 7, rem= 2.
Hitting quo= 7, rem= 3.
Hitting quo= 8, rem= 0.
Hitting quo= 8, rem= 1.
Hitting quo= 8, rem= 2.
Hitting quo= 9, rem= 0.
Hitting quo= 9, rem= 1.
Hitting quo= 9, rem= 2.
Hitting quo=10, rem= 0.
Hitting quo=10, rem= 1.
Hitting quo=11, rem= 0.
Hitting quo=11, rem= 1.
Hitting quo=12, rem= 0.
Hitting quo=12, rem= 1.
Hitting quo=13, rem= 0.
Hitting quo=13, rem= 1.
Hitting quo=14, rem= 0.
Hitting quo=14, rem= 1.
Hitting quo=15, rem= 0.
Hitting quo=15, rem= 1.
Hitting quo=16, rem= 0.
Hitting quo=17, rem= 0.
Hitting quo=18, rem= 0.
Hitting quo=19, rem= 0.
Hitting quo=20, rem= 0.
Hitting quo=21, rem= 0.
Hitting quo=22, rem= 0.
Hitting quo=23, rem= 0.
Hitting quo=24, rem= 0.
Hitting quo=25, rem= 0.
Hitting quo=26, rem= 0.
Hitting quo=27, rem= 0.
Hitting quo=28, rem= 0.
Hitting quo=29, rem= 0.
Hitting quo=30, rem= 0.
Hitting quo=31, rem= 0.
*/
