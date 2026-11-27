exec(open('ex1.py').read().split('res={}')[0])
from collections import Counter
C=Counter()
def ks(X,Y,i):
    out=[]
    for k in range(5):
        L=mul(zp(-k),add(X,mul(zp(i),Y))); R=mul(zp(k),add(X,mul(zp(-i),Y)))
        if div5lam(add(L,sc(-1,R))): out.append(k)
    return tuple(out)
for a1 in range(25):
  for b1 in range(5):
    X=real(a1,b1)
    if lamdiv(X): continue
    for a2 in range(25):
      for b2 in range(5):
        Y=real(a2,b2)
        if lamdiv(Y) or lamdiv(add(X,Y)): continue
        C[(ks(X,Y,1),ks(X,Y,2))]+=1
print(C)
