// For A in [lo,hi): E=enc(A) (p1 e1 p2 e2 ... concatenated). Need 10E < A-10 <= 100E (approx; slack),
// m=A-10 coprime to 10 and to E; print (A,E,L) with m | E*10^(L+1)+1 for L<=LMAX. Python verifies.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static int nd(u64 x){int d=1;while(x>=10){x/=10;d++;}return d;}
static u64 P10[20];
int main(int c,char**v){
 u64 lo=atoll(v[1]),hi=atoll(v[2]); int LMAX=atoi(v[3]);
 P10[0]=1;for(int i=1;i<20;i++)P10[i]=P10[i-1]*10;
 u64 S=1; while(S*S<hi)S++;
 char*isc=calloc(S+1,1); u64*pr=malloc(sizeof(u64)*S); int np=0;
 for(u64 i=2;i<=S;i++) if(!isc[i]){pr[np++]=i; for(u64 j=i*i;j<=S;j+=i)isc[j]=1;}
 const u64 BS=1<<20; u64*rem=malloc(8*BS); 
 // store factor lists per block: up to 12 factors each
 u64 (*fp)[12]=malloc(sizeof(u64)*12*BS); unsigned char (*fe)[12]=malloc(12*BS); unsigned char*nf=malloc(BS);
 long long cand=0,hits=0;
 for(u64 b=lo;b<hi;b+=BS){
  u64 e=b+BS<hi?b+BS:hi, n=e-b;
  for(u64 i=0;i<n;i++){rem[i]=b+i;nf[i]=0;}
  for(int k=0;k<np;k++){u64 p=pr[k]; u64 st=(b+p-1)/p*p;
    for(u64 x=st;x<e;x+=p){u64 i=x-b; int ex=0; while(rem[i]%p==0){rem[i]/=p;ex++;} fp[i][nf[i]]=p; fe[i][nf[i]]=ex; nf[i]++;}}
  for(u64 i=0;i<n;i++){
    u64 A=b+i; if(A<11)continue; u64 m=A-10; if(m%2==0||m%5==0)continue;
    if(rem[i]>1){fp[i][nf[i]]=rem[i];fe[i][nf[i]]=1;nf[i]++;}
    // E digits
    int dE=0; for(int j=0;j<nf[i];j++) dE+=nd(fp[i][j])+nd(fe[i][j]);
    int dA=nd(A); if(dE>dA-1 || dE<dA-3) continue;
    if(dE>18)continue;
    u64 E=0; for(int j=0;j<nf[i];j++){E=E*P10[nd(fp[i][j])]+fp[i][j]; E=E*P10[nd(fe[i][j])]+fe[i][j];}
    // ratio: p=(E*10^(L+1)+1)/m has L digits  <=>  10^(L-1) <= p < 10^L  ~  m/100 < E <= m/10 (+tiny)
    if(!((u128)E*100 >= m && (u128)E*10 < m+1)) continue;
    u64 g=E,h=m; while(h){u64 t=g%h;g=h;h=t;} if(g!=1)continue;
    cand++;
    u64 t=(u64)((u128)E*100%m); // E*10^(L+1) for L=1
    for(int L=1;L<=LMAX;L++){
      if((t+1)%m==0){ printf("%llu %llu %d\n",(unsigned long long)A,(unsigned long long)E,L); hits++; }
      t=(u64)((u128)t*10%m);
    }
  }
 }
 fprintf(stderr,"range %llu-%llu cand %lld divisible %lld\n",(unsigned long long)lo,(unsigned long long)hi,cand,hits);
}
