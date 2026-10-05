"""Independently replay the quadratic entry certificate and its exact cover.

This verifier does not import the generator. Rational rectangle events prove
coverage and absence of overlapping interiors; Arb at higher precision replays
every claimed finite orbit chart and every preceding noncritical chart.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
from collections import defaultdict
from flint import acb, arb, fmpq, ctx

def aq(q):
    return arb(fmpq(q.numerator, q.denominator))

def interval(l, r):
    return arb(fmpq(((l+r)/2).numerator, ((l+r)/2).denominator),
               fmpq(((r-l)/2).numerator, ((r-l)/2).denominator))

def verify(path):
    raw=path.read_bytes(); data=json.loads(raw)
    assert data['passed'] and not data['pending']
    assert data['domain']=={'R':'[1/16,1/2]', 's':'[0,1]'}
    assert data['collar_eta']=='1/4'
    events=defaultdict(list); count=0; max_index=0; charts=defaultdict(int)
    ctx.dps=90
    for item in data['accepted']:
        rl,rh,sl,sh=map(Q,item['box'])
        assert Q(1,16)<=rl<rh<=Q(1,2) and 0<=sl<sh<=1
        events[rl].append((1,sl,sh)); events[rh].append((-1,sl,sh))
        R=interval(rl,rh); s=interval(sl,sh)
        x=-R*R*s; y=R*(1-R*R*s*s).sqrt()
        a=acb(x,y); c=acb(aq(Q(1,4)))-a*a; w=acb(0)
        n=item['index']; assert 1<=n<=data['max_steps']
        for j in range(1,n+1):
            w=w*w+c
            if j<n:
                p=y*w.real-x*w.imag
                assert w.real>0 and p>0 and p<y/2, (item,j)
        z=(w-aq(Q(1,2)))/a
        if item['chart']=='interior':
            t=z.real-x/y*z.imag; v=z.imag/y
            assert abs(t)<1 and v<0 and v>t*t-1, item
        else:
            assert item['chart']=='chord-collar'
            assert abs(z.real)<1 and abs(z.imag)<y/4*(1-z.real*z.real), item
        count+=1; max_index=max(max_index,n); charts[item['chart']]+=1
    active=defaultdict(int); previous=Q(1,16); slabs=0
    for R in sorted(events):
        if R>previous:
            last=Q(0)
            for (sl,sh), multiplicity in sorted(active.items()):
                if not multiplicity: continue
                assert multiplicity==1 and sl==last, (previous,R,sl,sh)
                last=sh
            assert last==1, (previous,R,last)
            slabs+=1
        for change,sl,sh in events[R]:
            active[sl,sh]+=change
            assert active[sl,sh]>=0
        previous=R
    assert previous==Q(1,2) and not any(active.values())
    return {'passed':True,'certificate_sha256':hashlib.sha256(raw).hexdigest(),
            'accepted_boxes_replayed':count,'exact_rational_slabs':slabs,
            'max_orbit_index':max_index,'charts':dict(charts),
            'arithmetic':'Arb outward-rounded balls, 90 decimal digits',
            'coverage':'Exact rational sweep: each open R slab tiles [0,1] once; closed boxes include every boundary.'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate',type=Path)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); result=verify(args.certificate)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
