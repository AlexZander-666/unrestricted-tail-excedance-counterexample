"""Reconstruct selected weighted excedance rows and check real-root counts with integers."""
from fractions import Fraction as F
from functools import reduce
from itertools import permutations
from math import comb, factorial, gcd

def add_product(out, a, b, scalar):
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i+j] += scalar*x*y

def cycle_rows(n, method):
    if method=='insertion':
        rows=[[1]]
        for j in range(1,n):
            nxt=[0]*j
            for i,c in enumerate(rows[-1]):
                nxt[i]+=(i+1)*c
                if i+1<j: nxt[i+1]+=(j-i-1)*c
            rows.append(nxt)
    else:
        rows=[[1]]+[[sum((-1)**b*comb(j+1,b)*(i+1-b)**j for b in range(i+1))
                     for i in range(j)] for j in range(1,n)]
    return [[],[]]+[[0]+rows[a-1] for a in range(2,n+1)]

def anchored(n, allowed):
    cyc=cycle_rows(n,'insertion')
    rows=[[1]]
    for j in range(1,n+1):
        q=[0]*j
        for a in sorted(allowed):
            if a>j: break
            add_product(q,cyc[a],rows[j-a],comb(j-1,a-1))
        rows.append(q)
    return rows

def by_length(n, allowed):
    cyc=cycle_rows(n,'inclusion')
    rows=[[1]]+[[0]*j for j in range(1,n+1)]
    for a in sorted(allowed):
        old=rows
        rows=[v[:] for v in old]
        power=[1]
        for e in range(1,n//a+1):
            prod=[0]*(len(power)+a-1)
            add_product(prod,power,cyc[a],1)
            power=prod
            multiplicity=factorial(a*e)//(factorial(a)**e*factorial(e))
            for j in range(a*e,n+1):
                add_product(rows[j],old[j-a*e],power,comb(j,a*e)*multiplicity)
    return rows

def brute(n, allowed):
    out=[0]*n
    for sigma in permutations(range(n)):
        seen=set()
        for i in range(n):
            if i in seen: continue
            a,j=0,i
            while j not in seen:
                seen.add(j); a+=1; j=sigma[j]
            if a not in allowed: break
        else:
            out[sum(j<v for j,v in enumerate(sigma))]+=1
    return out

def trim(p):
    while p and not p[-1]:p.pop()
    return p

def primitive(p):
    trim(p)
    if not p:return []
    g=reduce(gcd,p,0)
    return [u//g for u in p]

def sturm(p):
    a=primitive(p[:]);b=primitive([i*x for i,x in enumerate(a)][1:])
    chain=[a,b]
    while len(b)>1:
        rem=a[:]
        while len(rem)>=len(b):
            scale=abs(b[-1])
            c=rem[-1]*(1 if b[-1]>0 else -1)
            shift=len(rem)-len(b)
            rem=[scale*x for x in rem]
            for j,v in enumerate(b):rem[j+shift]-=c*v
            rem=primitive(rem)
        assert rem, 'multiple roots in this witness'
        a,b=b,[-v for v in rem];chain.append(b)
    assert len(b)==1 and b[0]
    def var(signs):
        return sum(a!=b for a,b in zip(signs,signs[1:]))
    at_minus=[(q[-1]*(-1)**(len(q)-1)>0) for q in chain]
    at_plus=[q[-1]>0 for q in chain]
    return var(at_minus)-var(at_plus)

def jets(p,t):
    v=b=c=F(0)
    for a in reversed(p):
        v,b,c=v*t+a,b*t+v,c*t+2*b
    return v,b,c

def lag(p,t):
    a,b,c=jets(p,t)
    return b*b-a*c

def disk(p,a,b,radius=10,den=10**6):
    # Expand den^degree * p((a+bi+z)/den) as a Gaussian integer polynomial.
    c=[(0,0) for _ in p];c[0]=(p[-1],0)
    for step,h in enumerate(reversed(p[:-1]),1):
        for j in range(step,-1,-1):
            x,y=c[j];u,v=c[j-1] if j else (h*den**step,0)
            c[j]=(a*x-b*y+u,b*x+a*y+v)
    head=max(map(abs,c[1]))*radius
    rem=sum((abs(u)+abs(v))*radius**j for j,(u,v) in enumerate(c) if j!=1)
    assert 3*rem<head and b>radius
    return True

def run(case,n,A,B,t,weights):
    A=set(A);B=set(B)
    assert n in A and n in B and min(A|B)>=2
    endpoints=[]
    for S in [A,B]:
        rr=anchored(n,S)
        assert rr==by_length(n,S)
        for j in range(2,min(n+1,9)):
            assert rr[j]==brute(j,S)
        f=rr[n];assert f[0]==0 and f[1]>0 and f[-1]>0
        assert all(c>0 for c in f[1:])
        endpoints.append(f)
    a,b=weights;h=[a*x+b*y for x,y in zip(*endpoints)]
    counts=[sturm(f[1:]) for f in endpoints+[h]]
    print(case,'n',n,'quotient degree',n-2,'real roots of endpoints and combination',counts)
    print('test point',t,'positive integer coefficients',weights)
    print('Laguerre on quotient',lag(h[1:],t))
    print('Laguerre on unmodified permutation polynomial',lag(h,t))
    assert counts[:2]==[n-2,n-2] and counts[2]<n-2 and lag(h,t)<0
    centers={44:[(-494231,6159),(-2023030,25210)],
             34:([(-130951,2544),(-7633538,148281)] if case=='short input' else [(-132310,4250),(-7550232,242511)])}[n]
    assert all(disk(h[1:],a,b) for a,b in centers)
    print('Upper-half-plane Rouche disk centers / 10^6',centers,'radius 10 / 10^6')
    return counts

if __name__=='__main__':
    n=44
    A={2,4,6,9,11,13,16,18,20,23,25,27,30,32,34,36,37,39,41,43,44}
    B=(set(range(2,n))-A)|{n}
    run('phase-selected equal average',n,A,B,F(-1,2),(1,1))
    n=34
    A={3,4,7,10,11,13,14,16,17,19,20,23,26,29,32,n}
    B={2,3,5,6,8,9,12,15,18,21,24,27,n}
    run('reduced size',n,A,B,F(-2,15),(1,2))

    A={3}|set(range(4,17,3))|set(range(14,24,3))|{34}
    run('short input',34,A,B,F(-2,15),(1,2))

    for size,extra,top in [(40,{2,5,8},27),(43,{2,5},30)]:
        S=extra|set(range(3,top+1,3))|{size}
        rr=anchored(size,S)
        assert rr==by_length(size,S)
        for j in range(2,9): assert brute(j,S)==rr[j]
        f=rr[size]
        for g in [f,f[1:]]: assert lag(g,F(-2,15))<0
        c=sturm(f[1:])
        assert c==size-6
        print('single genuine profile',size,sorted(S),'quotient real roots',c,'of',size-2)
        print('Laguerre on unmodified permutation polynomial at -2/15',lag(f,F(-2,15)))
        print('original row f, first and second derivatives at -2/15',*jets(f,F(-2,15)))
        c={40:[(-129434,4116),(-7718151,245456)],43:[(-132659,3072),(-7534081,174492)]}[size]
        assert all(disk(f[1:],a,b) for a,b in c)
        print('Upper-half-plane Rouche disk centers / 10^6',c,'radius 10 / 10^6')
        if size==40:
            adjacent=anchored(40,S|{39})
            assert adjacent==by_length(40,S|{39})
            assert adjacent[40]==f and sturm(adjacent[39][1:])==37
            print('Same cutoff 39 and same profile: preceding quotient all 37 simple negative roots; size 40 has 34 of 38 real.')

