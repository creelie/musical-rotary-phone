import sys
N=5000
fib=[0,1]
while len(fib)<60: fib.append(fib[-1]+fib[-2])
luc=[2,1]
while len(luc)<60: luc.append(luc[-1]+luc[-2])
B=sorted(set([f for f in fib if f>0]+luc))
def greedy(n):
    c=0
    while n>0:
        s=max(b for b in B if b<=n); n-=s; c+=1
    return c
def zeck(n):
    l=[]
    while n>0:
        k=max(i for i in range(2,60) if fib[i]<=n); l.append(k); n-=fib[k]
    return l
def W(l):
    if not l: return 0
    if len(l)==1: return 1
    k,k2=l[0],l[1]
    return 1+W(l[2:]) if k2+2==k else 1+W(l[1:])
def cvZ(l):
    if not l: return 0
    return 2**(l[0]-2-(len(l)-1))+cvZ(l[1:])
def compress(ds):
    out=[];i=0
    while i<len(ds):
        if ds[i]==1: out.append(1); i+=2
        else: out.append(ds[i]); i+=1
    return out
def digits(m):
    d=[]
    while m>0: d.append(m%2); m//=2
    return d
def ofd(d): return sum(x*2**i for i,x in enumerate(d))
def a003714(n): return sum(2**(k-2) for k in zeck(n))
def a048679(n): return ofd(compress(digits(a003714(n))))
def v2(x):
    c=0
    while x%2==0: x//=2;c+=1
    return c
def a035263(n): return v2(2*n)%2
def a329320(n):
    import math
    L=n.bit_length()-1 if n>0 else 0
    return sum(1-a035263(1+n//2**k) for k in range(L+1))
bad=0
for n in range(N):
    z=zeck(n); g=greedy(n)
    if W(z)!=g or cvZ(z)!=a048679(n) or a329320(cvZ(z))!=g: bad+=1; print("bad",n)
print("checked",N,"bad",bad)
print([a048679(n) for n in range(15)])
