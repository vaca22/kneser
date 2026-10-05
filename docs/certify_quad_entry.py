"""Arb covering certificate for the compact quadratic exterior core.

R in [1/16,1/2], s in [0,1],
a=-R^2*s+i*R*sqrt(1-R^2*s^2), c=1/4-a^2.
Each accepted box has a finite critical-orbit mark in the crescent or its
explicit chord collar. All earlier orbit points have positive real part
and lie strictly between the chord and its negative. This is stronger than
mere numerical entry and is needed to patch the markings.
"""
from __future__ import annotations
import argparse
import json
import time
from fractions import Fraction
from pathlib import Path
from flint import acb, arb, ctx, fmpq

ETA = Fraction(1, 4)

def rat(x):
    return fmpq(x.numerator, x.denominator)

def ball(lo, hi):
    return arb(rat((lo + hi)/2), rat((hi-lo)/2))

def entry(box, max_steps):
    rlo, rhi, slo, shi = box
    R, s = ball(rlo, rhi), ball(slo, shi)
    ar = -R**2*s
    ai = R*(1-R**2*s**2).sqrt()
    a = acb(ar,ai)
    c = acb(arb(fmpq(1,4))) - a*a
    w = acb(0)
    for n in range(1,max_steps+1):
        w = w*w+c
        z = (w-arb(fmpq(1,2)))/a
        T = z.real-ar/ai*z.imag
        Y = z.imag/ai
        interior = abs(T)<1 and Y<0 and Y>T*T-1
        collar = abs(z.real)<1 and abs(z.imag)<arb(rat(ETA))*ai*(1-z.real*z.real)
        if interior or collar:
            return n, "interior" if interior else "chord-collar"
        # P>0 implies -w is also above the chord. P<ai/2 says w is
        # above the chord; Re w>0 prevents critical inverse steps.
        P = ai*w.real-ar*w.imag
        if not (w.real>0 and P>0 and P<ai/2):
            return None
    return None

def enc(box):
    return [str(x) for x in box]

def run(max_boxes,max_steps):
    # Geometric R bands keep the first propagation intervals well scaled.
    pending=[]
    for k in range(1,4):
        pending.append((Fraction(1,2**(k+1)),Fraction(1,2**k),Fraction(0),Fraction(1)))
    accepted=[];attempts=0;t0=time.monotonic()
    while pending:
        box=pending.pop();attempts+=1
        outcome=entry(box,max_steps)
        if outcome:
            accepted.append({"box":enc(box),"index":outcome[0],"chart":outcome[1]})
        else:
            if attempts>=max_boxes:
                pending.append(box)
                return {"passed":False,"attempts":attempts,"accepted":accepted,
                        "pending":[enc(x) for x in pending],"elapsed_seconds":time.monotonic()-t0}
            rl,rh,sl,sh=box
            # At small R a relative R change is much more sensitive than s.
            if (rh-rl)/rl > (sh-sl)*rl:
                mid=(rl+rh)/2
                pending.extend([(rl,mid,sl,sh),(mid,rh,sl,sh)])
            else:
                mid=(sl+sh)/2
                pending.extend([(rl,rh,sl,mid),(rl,rh,mid,sh)])
        if attempts%10000==0:
            print(f"attempts={attempts} accepted={len(accepted)} pending={len(pending)} elapsed={time.monotonic()-t0:.1f}s",flush=True)
    return {"passed":True,"attempts":attempts,"accepted":accepted,
            "pending":[],"elapsed_seconds":time.monotonic()-t0}

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--max-boxes",type=int,default=300000)
    p.add_argument("--max-steps",type=int,default=1024)
    args=p.parse_args();ctx.dps=60
    result=run(args.max_boxes,args.max_steps)
    result.update({"domain":{"R":"[1/16,1/2]","s":"[0,1]"},
                   "arithmetic":"Arb outward-rounded balls, 60 decimal digits",
                   "collar_eta":str(ETA),"max_steps":args.max_steps})
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in ("accepted","pending")},indent=2))
    print("accepted_boxes",len(result["accepted"]),"pending_boxes",len(result["pending"]))
    raise SystemExit(0 if result["passed"] else 1)
