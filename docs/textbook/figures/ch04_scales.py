"""第 4 章算例：tetration 开折的乘子、内蕴参数 p、强迫尺度 Lambda 与留数。

u 坐标 w = e(1+u)，s = 1 - e log b，a2 = 1/2，gamma = 1，rho = 1/3。
运行：python3 figures/ch04_scales.py
"""
import mpmath as mp
mp.mp.dps=40
E=mp.e
for lam in ['0.5','0.8','0.9','0.95','0.99','0.999']:
    lam=mp.mpf(lam)
    lb=lam*mp.exp(-lam); b=mp.exp(lb); s=1-E*lb
    lam2=mp.findroot(lambda t:t*mp.exp(-t)-lb, 1+(1-lam)*1.2)
    l1=mp.log(lam); l2=mp.log(lam2)
    p=-l1*l2; Lam=mp.exp(4*mp.pi**2/l1); h=2*mp.pi/abs(l1); h2=2*mp.pi/l2
    u1=mp.exp(lam-1)-1; u2=mp.exp(lam2-1)-1
    A1=1/l1;A2=1/l2
    print(f"lam={mp.nstr(lam,4)} b={mp.nstr(b,10)} s={mp.nstr(s,6)} lam2={mp.nstr(lam2,8)} |l1|={mp.nstr(-l1,6)} l2={mp.nstr(l2,6)} sqrt2s={mp.nstr(mp.sqrt(2*s),6)} p={mp.nstr(p,6)} 2s={mp.nstr(2*s,6)} p/s={mp.nstr(p/s,6)} Lam={mp.nstr(Lam,4)} approx={mp.nstr(mp.exp(-2*mp.pi**2/mp.sqrt(s/2)),4)} h={mp.nstr(h,6)} h2-h={mp.nstr(h2-h,6)} A1+A2={mp.nstr(A1+A2,8)} A1d={mp.nstr(A1*(u1-u2),8)} etab={mp.nstr(mp.exp(1/E)-b,6)} Ceta_check={mp.nstr(-mp.log(Lam)*mp.sqrt(mp.exp(1/E)-b),8)}")
C=4*mp.pi**2/mp.sqrt(2*mp.exp(1-1/E)); print('Ceta',mp.nstr(C,15))
print('2pi/3',mp.nstr(2*mp.pi/3,8))
