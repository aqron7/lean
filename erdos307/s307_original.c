#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static u64 mulmod(u64 a,u64 b,u64 m){return (u128)a*b%m;}
static u64 pw(u64 a,u64 e,u64 m){u64 r=1;a%=m;while(e){if(e&1)r=mulmod(r,a,m);a=mulmod(a,a,m);e>>=1;}return r;}
static int isprime(u64 n){if(n<2)return 0;static const u64 P[]={2,3,5,7,11,13,17,19,23,29,31,37};
 for(int i=0;i<12;i++){if(n%P[i]==0)return n==P[i];}
 u64 d=n-1;int s=0;while(!(d&1)){d>>=1;s++;}
 for(int i=0;i<12;i++){u64 x=pw(P[i],d,n);if(x==1||x==n-1)continue;int ok=0;for(int r=1;r<s;r++){x=mulmod(x,x,n);if(x==n-1){ok=1;break;}}if(!ok)return 0;}return 1;}
static u64 gcd(u64 a,u64 b){while(b){u64 t=a%b;a=b;b=t;}return a;}
static u64 rho(u64 n){if(n%2==0)return 2;for(u64 c=1;;c++){u64 x=2,y=2,d=1;while(d==1){x=(mulmod(x,x,n)+c)%n;y=(mulmod(y,y,n)+c)%n;y=(mulmod(y,y,n)+c)%n;d=gcd(x>y?x-y:y-x,n);}if(d!=n)return d;}}
static u64 pr[64];static int npr;
static void fac(u64 n){if(n==1)return;if(isprime(n)){pr[npr++]=n;return;}
 for(u64 p=2;p<1000;p++) if(n%p==0){ pr[npr++]=p; /*placeholder*/ npr--; break;}
 u64 d=rho(n);fac(d);fac(n/d);}
static u64 ppw[32];static int k; static u64 M; static int B,K; static long long cnt,found;
static int blk[32]; static u64 cur[16]; static int nc;
// enumerate set partitions of ppw[0..k-1] via restricted growth
static u64 bp[32];
static void part(int i,int nb){
 if(i==k){ if(nb<2)return; u128 N=1; for(int j=0;j<nb;j++)N*=bp[j];
   u128 s=0; for(int j=0;j<nb;j++) s+=N/bp[j];
   if(s==M){found++;printf("FOUND P=");for(int j=0;j<nc;j++)printf("%llu ",(unsigned long long)cur[j]);printf(" Q=");for(int j=0;j<nb;j++)printf("%llu ",(unsigned long long)bp[j]);printf("\n");fflush(stdout);}
   return;}
 for(int b=0;b<=nb;b++){ u64 save=(b<nb)?bp[b]:1; bp[b]=save*ppw[i]; part(i+1,b==nb?nb+1:nb); bp[b]=save; }
}
static void check(){
 u128 MM=1; for(int j=0;j<nc;j++)MM*=cur[j]; if(MM>>63)return; M=(u64)MM;
 u128 N=0; for(int j=0;j<nc;j++)N+=MM/cur[j]; if(N>>62)return;
 cnt++; npr=0; fac((u64)N);
 // combine equal primes into prime powers
 k=0; for(int i=0;i<npr;i++){int dup=0;for(int j=0;j<k;j++) if(ppw[j]%pr[i]==0 && gcd(ppw[j],pr[i])==pr[i]){ /* same prime? check base */ }
 }
 // simpler: sort primes and group
 for(int i=0;i<npr;i++)for(int j=i+1;j<npr;j++)if(pr[j]<pr[i]){u64 t=pr[i];pr[i]=pr[j];pr[j]=t;}
 k=0; for(int i=0;i<npr;){u64 p=pr[i],q=1;while(i<npr&&pr[i]==p){q*=p;i++;}ppw[k++]=q;}
 if(k<2||k>14)return;
 part(0,0);
}
static void rec(int start,u64 prod){
 if(nc>=2)check();
 if(nc==K)return;
 for(int x=start;x<=B;x++) if(gcd(x,prod)==1){cur[nc++]=x;rec(x+1,prod*x>0?prod*x:prod);nc--;}
}
int main(int c,char**v){B=atoi(v[1]);K=atoi(v[2]);int s=c>3?atoi(v[3]):2;rec(s,1);fprintf(stderr,"checked %lld found %lld\n",cnt,found);}
