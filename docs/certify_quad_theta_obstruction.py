"""Exact rational checks for two obstructions to global theta convergence.

No floating-point computation is used. The first obstruction is the
Schroeder resonance at lambda=i, c=1/4+i/2. The second records a nonconstant
normalisation at c=i, for the fixed-degree Taylor limit argument.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import json

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def neg(a): return (-a[0],-a[1])
def sub(a,b): return add(a,neg(b))
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def div(a,b):
    den=b[0]*b[0]+b[1]*b[1]
    assert den!=0
    return ((a[0]*b[0]+a[1]*b[1])/den,(a[1]*b[0]-a[0]*b[1])/den)
def power(a,n):
    out=(Q(1),Q(0))
    for _ in range(n): out=mul(out,a)
    return out
def enc(a): return {'real':str(a[0]),'imag':str(a[1])}

def certify():
    zero=(Q(0),Q(0)); one=(Q(1),Q(0)); lam=(Q(0),Q(1))
    c=(Q(1,4),Q(1,2)); L=(Q(0),Q(1,2)); u=[zero,one]
    for k in range(2,5):
        numerator=zero
        for j in range(1,k): numerator=add(numerator,mul(u[j],u[k-j]))
        u.append(div(numerator,sub(power(lam,k),lam)))
    numerator=zero
    for j in range(1,5): numerator=add(numerator,mul(u[j],u[5-j]))
    denominator=sub(power(lam,5),lam)
    ci=lam; w=zero
    for _ in range(3): w=add(mul(w,w),ci)
    fw=add(mul(w,w),ci)
    checks={
        'parameter_strictly_in_upper_halfplane':c[1]>0,
        'L_is_fixed_and_has_multiplier_i':add(mul(L,L),c)==L and add(L,L)==lam,
        'u2_exact':u[2]==(Q(-1,2),Q(1,2)),
        'u3_exact':u[3]==(Q(-1,2),Q(-1,2)),
        'u4_exact':u[4]==(Q(1,4),Q(-5,4)),
        'order5_denominator_is_zero':denominator==zero,
        'order5_numerator_is_nonzero':numerator==(Q(3,2),Q(-5,2)),
        'at_c_i_w3_is_minus_i':w==neg(lam),
        'at_c_i_w3_is_not_fixed':fw!=w,
    }
    return {'passed':all(checks.values()),'arithmetic':'Exact fractions in Q(i)',
            'scope':'Refutation of all-upper-halfplane convergence for the current Schroeder-based theta/Taylor scheme; not a convergence certificate.',
            'resonance':{'c':enc(c),'lambda':enc(lam),'u2':enc(u[2]),
                         'u3':enc(u[3]),'u4':enc(u[4]),
                         'order5_denominator':enc(denominator),
                         'order5_numerator':enc(numerator)},
            'fixed_degree_example':{'c':enc(ci),'w3':enc(w),'f_w3':enc(fw)},
            'checks':checks}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args=p.parse_args(); result=certify()
    if args.output: args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    raise SystemExit(0 if result['passed'] else 1)
