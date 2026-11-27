import gmpy2, sys
from gmpy2 import mpz
from sympy import factorint
def enc_f(f):
    return int(''.join(f"{p}{e}" for p,e in sorted(f.items())))
def enc(n):
    return enc_f(factorint(n)) if n>=2 else 0
# brute force small n
for n in range(2,2000000):
    if enc(n)==n: print("BRUTE FIXED",n); sys.stdout.flush()
print("brute done to 2e6"); sys.stdout.flush()
AMAX=int(sys.argv[1]); LMAX=int(sys.argv[2]); found=0
for A in range(11,AMAX):
    m=A-10
    if m%2==0 or m%5==0: continue
    f=factorint(A); E=enc_f(f)
    if not (10*E < m*1.000001 and m <= 100*E*1.000001): continue
    if gmpy2.gcd(E,m)!=1: continue
    mx=max(f)
    t=mpz(E)*10   # E*10^(L+1) at L=0
    for L in range(1,LMAX+1):
        t*=10
        if (t+1)%m: continue
        p=(t+1)//m
        if gmpy2.num_digits(p,10)!=L or p<=mx: continue
        if gmpy2.is_prime(p,30):
            n=A*p
            if enc_f({**f, int(p):1})==n:
                print("FOUND A=%d L=%d p=%s n=%s"%(A,L,p,n)); sys.stdout.flush(); found+=1
print("done AMAX",AMAX,"LMAX",LMAX,"found",found)
