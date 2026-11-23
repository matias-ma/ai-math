from fractions import Fraction as Q
from math import isqrt
import json, sys

def square(a):
    n=len(a); b=max(map(abs,a)); w=(4*n*b*b).bit_length()//8+1
    z=int.from_bytes(b''.join((x+b).to_bytes(w,'little') for x in a),'little')**2
    z=z.to_bytes(2*n*w,'little')
    c=[int.from_bytes(z[k*w:(k+1)*w],'little') for k in range(2*n)]
    return [c[k]+c[k+n]-n*b*b for k in range(n)]

def fq(n,p,rows):
    a=[int(x,16) for x in rows]; mask=(1<<n)-1
    assert n>=6 and len(a)==4 and all(0<=x<=mask for x in a)
    s=n-2*a[1].bit_count()
    assert s>0 and [n-2*x.bit_count() for x in a]==[-s,s,s,s]
    assert (2*s-2)**2<=2*n<=(2*s+2)**2
    N=[sum(n-2*(x^(((x<<t)|(x>>(n-t)))&mask)).bit_count() for x in a) for t in range(n)]
    D=256; m=isqrt(2*n*D*D-1)+1; c=(5*n+4)*D-2*m; r=3*n*D-6*m
    q=[n*D*x+c-4*D*s*s for x in N]; q[0]-=n*c
    assert sum(q)==0 and r>8 and 0<=p<=12
    R=n*(r-8)
    for _ in range(p): q=square(q); R*=R
    assert sum(map(abs,q))<=R

def psd(A):
    A=[list(map(Q,row)) for row in A]; n=len(A)
    for k in range(n):
        d=A[k][k]; assert d>=0
        if not d: assert not any(A[k][k+1:])
        else:
            for i in range(k+1,n):
                for j in range(i,n):
                    A[i][j]=A[j][i]=A[i][j]-A[i][k]*A[k][j]/d

def matrix(n,t,rows):
    a=[int(x,16) for x in rows]; t=Q(*t)
    assert n>0 and t>0 and len(a) in (1,n) and all(0<=x<1<<n for x in a)
    if len(a)==1: a=[((a[0]<<k)|(a[0]>>(n-k)))&((1<<n)-1) for k in range(n)]
    G=[[n-2*(x^y).bit_count() for y in a] for x in a]
    e=Q(1,10) if n>=5 else 0
    psd([[G[i][j]-(t+e)*(i==j) for j in range(n)] for i in range(n)])
    psd([[(4*t-e)*(i==j)-G[i][j] for j in range(n)] for i in range(n)])

if __name__=='__main__':
    data=json.load(open(sys.argv[1]))
    if len(sys.argv)>2:
        n=int(sys.argv[2]); f=[r[1] for r in data if r[0]=='F']; m=[r[1] for r in data if r[0]=='M']
        assert n>=16 and len(f)==n-15 and set(f)==set(range(16,n+1))
        assert len(m)==32 and set(m)==set(range(1,64,2))
    for row in data:
        if row[0]=='F': fq(*row[1:])
        elif row[0]=='M': matrix(*row[1:])
        else: raise ValueError('Unknown certificate type')
    print('All certificates verified.')
