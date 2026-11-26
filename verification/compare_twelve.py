"""Check the earlier size-twelve example after admitting the full cycle."""
from fractions import Fraction
from math import comb, factorial

def cycle(size):
    # Eulerian explicit formula, shifted by one strict excedance.
    return [0] + [sum((-1)**h*comb(size,h)*(j+1-h)**(size-1)
                      for h in range(j+1)) for j in range(size-1)]

def power(polynomial, exponent):
    result=[1]
    for _ in range(exponent):
        product=[0]*(len(result)+len(polynomial)-1)
        for i,a in enumerate(result):
            for j,b in enumerate(polynomial):
                product[i+j]+=a*b
        result=product
    return result

def main():
    row=cycle(12)
    for size,count in ((3,4),(4,3)):
        multiplicity=factorial(12)//(factorial(size)**count*factorial(count))
        for j,c in enumerate(power(cycle(size),count)):
            row[j]+=multiplicity*c
    assert row[0]==0
    quotient=row[1:]
    assert len(quotient)==11 and quotient[-1]==1
    nodes=[-2000,-100,-20,-5,-3,-1,Fraction(-1,3),Fraction(-1,5),
           Fraction(-1,20),Fraction(-1,100),0]
    for i,x in enumerate(nodes):
        assert (-1)**i*sum(c*x**j for j,c in enumerate(quotient))>0
    print('PASS: all ten roots of the degree-ten quotient are simple and negative.')
    print('Quotient coefficients, ascending:',*quotient)
    print('Rational sign-change nodes:',*nodes)

if __name__=='__main__': main()
