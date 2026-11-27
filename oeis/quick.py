import gmpy2, sys, time
from gmpy2 import mpz
# A113010: n = d^s, d = #digits, s = digit sum
hits=[]
for d in range(1,3001):
    for s in range(1,9*d+1):
        n=mpz(d)**s
        L=gmpy2.num_digits(n,10)
        if L<d: continue
        if L>d: break
        if sum(map(int,str(n)))==s: hits.append((d,s,int(n)))
print("A113010 fixed points (d<=3000):",[h if h[2]<10**12 else (h[0],h[1],'big') for h in hits]); sys.stdout.flush()
# A109905: zeros of a(n) up to N
N=200000; z=[]
for n in range(1,N+1):
    ok=False
    for k in range(n//2,0,-1):
        if gmpy2.is_prime(k*(n-k)+1): ok=True;break
    if not ok: z.append(n)
print("A109905 zeros n<=%d:"%N,z); sys.stdout.flush()
# A108301: digit sum of 2^2^n+1
for n in range(12,24):
    t=time.time(); s=sum(map(int,gmpy2.digits(mpz(2)**(2**n)+1))) ; print("A108301",n,s,gmpy2.is_prime(s),"%.1fs"%(time.time()-t)); sys.stdout.flush()
