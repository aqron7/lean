// s307b: pruned search. P pairwise coprime, elements in [start,B], size 2..K.
// Necessary: S_P * S_Q = 1, S_Q <= sum_{p | N} 1/p, primes of N coprime to M.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
static u64 mulmod(u64 a,u64 b,u64 m){return (u128)a*b%m;}
static u64 pw(u64 a,u64 e,u64 m){u64 r=1;a%=m;while(e){if(e&1)r=mulmod(r,a,m);a=mulmod(a,a,m);e>>=1;}return r;}
static int isprime(u64 n){if(n<2)return 0;static const u64 P[]={2,3,5,7,11,13,17,19,23,29,31,37};
 for(int i=0;i<12;i++){if(n%P[i]==0)return n==P[i];}
 u64 d=n-1;int s=0;while(!(d&1)){d>>=1;s++;}
 for(int i=0;i<12;i++){u64 x=pw(P[i],d,n);if(x==1||x==n-1)continue;int ok=0;for(int r=1;r<s;r++){x=mulmod(x,x,n);if(x==n-1){ok=1;break;}}if(!ok)return 0;}return 1;}
static u64 gcd(u64 a,u64 b){while(b){u64 t=a%b;a=b;b=t;}return a;}
static u64 rho(u64 n){if(n%2==0)return 2;for(u64 c=1;;c++){u64 x=2+c,y=x,d=1;while(d==1){x=(mulmod(x,x,n)+c)%n;y=(mulmod(y,y,n)+c)%n;y=(mulmod(y,y,n)+c)%n;d=gcd(x>y?x-y:y-x,n);}if(d!=n)return d;}}
static u64 pr[128];static int npr;
static void fac(u64 n){if(n==1)return;
 for(u64 p=2;p<200;p++) if(n%p==0){pr[npr++]=p;fac(n/p);return;}
 if(isprime(n)){pr[npr++]=n;return;}
 u64 d=rho(n);fac(d);fac(n/d);}
static int PR[200],NP; static long long B; static int K,START; static long long cand,filt,factored,big,found,partnodes;
static u64 cur[32]; static int nc; static double Smin;
static u64 ppw[64]; static double rp[64]; static int k; static u128 M,N; static double target; static int needEven;
static u64 bp[64]; static int divP(u64 p); static int copP(u64 y);
static void part(int i,int nb,double sumrec,double remrec){
 partnodes++;
 if(sumrec+remrec < target*(1-1e-12)) return;
 if(i==k){ if(nb<2)return; if(needEven && (nb&1))return;
   u128 s=0; for(int j=0;j<nb;j++) s+=N/bp[j];
   if(s==M){found++;printf("FOUND P=");for(int j=0;j<nc;j++)printf("%llu ",(unsigned long long)cur[j]);printf(" Q=");for(int j=0;j<nb;j++)printf("%llu ",(unsigned long long)bp[j]);printf("\n");fflush(stdout);}
   return;}
 double nr=remrec-rp[i];
 for(int b=0;b<=nb;b++){
   if(b<nb){u64 o=bp[b]; bp[b]=o*ppw[i]; part(i+1,nb,sumrec-1.0/o+1.0/bp[b],nr); bp[b]=o;}
   else {bp[b]=ppw[i]; part(i+1,nb+1,sumrec+rp[i],nr);}
 }
}
static void pr128(u128 x){char b[50];int i=49;b[i]=0;do{b[--i]='0'+x%10;x/=10;}while(x);printf("%s",b+i);}
static void check(){
 cand++;
 { double SPl=0,lM=0; for(int j=0;j<nc;j++){SPl+=1.0/cur[j]; lM+=log((double)cur[j]);}
   double lN=lM+log(SPl), H=0, lp=0;
   for(int i=0;i<NP;i++){int p=PR[i]; if(divP(p))continue; lp+=log((double)p); if(lp>lN+1e-9)break; H+=1.0/p;}
   if(SPl*H < 1-1e-9) return;
   if(lM>125*log(2.0)){ big++; printf("BIGM P="); for(int j=0;j<nc;j++)printf("%llu ",(unsigned long long)cur[j]); printf("\n"); return; } }
 u128 MM=1; for(int j=0;j<nc;j++)MM*=cur[j];
 u128 NN=0; for(int j=0;j<nc;j++)NN+=MM/cur[j];
 double SP=0; for(int j=0;j<nc;j++)SP+=1.0/cur[j];
 // Hmax: smallest primes coprime to M, product <= N
 double H=0; long double pp=1, Nd=(long double)NN;
 for(int i=0;i<NP;i++){u64 p=PR[i]; if(MM%p==0)continue; if(pp*p>Nd)break; pp*=p; H+=1.0/p;}
 if(SP*H < 1-1e-9) return;
 filt++;
 // parity: one set has exactly one even element, other all odd with even size
 int ev=0; for(int j=0;j<nc;j++) if(!(cur[j]&1)) ev++;
 if(ev==0 && (nc&1)) return;           // P all odd needs even size
 if(NN>>63){ big++; printf("BIG P="); for(int j=0;j<nc;j++)printf("%llu ",(unsigned long long)cur[j]); printf(" N="); pr128(NN); printf("\n"); return; }
 factored++; M=MM; N=NN; npr=0; fac((u64)N);
 for(int i=0;i<npr;i++)for(int j=i+1;j<npr;j++)if(pr[j]<pr[i]){u64 t=pr[i];pr[i]=pr[j];pr[j]=t;}
 k=0; for(int i=0;i<npr;){u64 p=pr[i],q=1;while(i<npr&&pr[i]==p){q*=p;i++;}ppw[k++]=q;}
 // sort descending for better pruning
 for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)if(ppw[j]>ppw[i]){u64 t=ppw[i];ppw[i]=ppw[j];ppw[j]=t;}
 double R=0; for(int i=0;i<k;i++){rp[i]=1.0/ppw[i]; R+=rp[i];}
 target=1.0/SP; if(R<target*(1-1e-12)) return;
 needEven = (N&1);   // Q all odd => even size
 part(0,0,0,R);
}
static double lnNg;
static int divP(u64 p){for(int j=0;j<nc;j++)if(cur[j]%p==0)return 1;return 0;}
static int copP(u64 y){for(int j=0;j<nc;j++)if(gcd(y,cur[j])!=1)return 0;return 1;}
static void rec(u64 start,double s){
 if(nc>=2)check();
 if(nc==K)return;
 // H bound over primes coprime to current prod, product <= global N bound
 double Hn=0,lp=0; for(int i=0;i<NP;i++){int p=PR[i]; if(divP(p))continue; lp+=log((double)p); if(lp>lnNg)break; Hn+=1.0/p;}
 double need=1.0/Hn*(1-1e-9); if(START==1)need=0;
 int r=K-nc;
 for(u64 x=start;x<=(u64)B;x++){
   // tail: r smallest integers >= x coprime to prod (upper bound on remaining contribution)
   double t=0; int got=0; for(u64 y=x;got<r && y<x+100000;y++) if(copP(y)){t+=1.0/y;got++;}
   if(got<r) t+= (r-got)*1.0/x;
   if(s+t < need) break;
   if(copP(x)){cur[nc++]=x;rec(x+1,s+1.0/x);nc--;}
 }
}
int main(int c,char**v){B=atoll(v[1]);K=atoi(v[2]);START=c>3?atoi(v[3]):2; 
 for(int n=2;NP<200;n++){int ok=1;for(int i=0;i<NP&&PR[i]*PR[i]<=n;i++)if(n%PR[i]==0){ok=0;break;}if(ok)PR[NP++]=n;}
 // global N bound: N <= B^K * K/START
 double lnN=K*log((double)B)+log((double)K); double H=0,lp=0;
 for(int i=0;i<NP;i++){lp+=log((double)PR[i]); if(lp>lnN)break; H+=1.0/PR[i];}
 Smin=(1.0/H)*(1-1e-9); lnNg=lnN; if(START==1)Smin=0;
 fprintf(stderr,"B=%lld K=%d Smin=%.4f\n",B,K,Smin);
 rec(START,0);
 fprintf(stderr,"B=%lld K=%d cand %lld passH %lld factored %lld big %lld partnodes %lld found %lld\n",B,K,cand,filt,factored,big,partnodes,found);}
