#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef __int128 i128;
static long long froot(i128 v){ // integer 5th root if exact, else -1 ; v>=0
  long double r=powl((long double)v,0.2L); long long c=llroundl(r);
  for(long long k=c-2;k<=c+2;k++){ if(k<0)continue; i128 p=(i128)k*k*k*k*k; if(p==v) return k; }
  return -1; }
static long long gcdl(long long a,long long b){if(a<0)a=-a;if(b<0)b=-b;while(b){long long t=a%b;a=b;b=t;}return a;}
int main(int c,char**v){ long long lo=atoll(v[1]),hi=atoll(v[2]); long long found=0;
 for(long long x=lo;x<hi;x++){ i128 x5=(i128)x*x*x*x*x;
  for(long long y=-x;y<=x;y++){ if(y==-x) continue; i128 s=x5+(i128)y*y*y*y*y;
    if(s%88) continue; i128 q=s/88; int neg=q<0; if(neg) q=-q;
    long long z=froot(q); if(z>0 && gcdl(x,y)==1){ printf("FOUND x=%lld y=%lld z=%lld\n",x,y,neg?-z:z); fflush(stdout); found++; } } }
 fprintf(stderr,"done %lld-%lld found %lld\n",lo,hi,found); }
