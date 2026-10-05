# 交接文档：Kneser 型四则延拓与正则迭代的分离问题

最后更新：2026-09-29（猜想已证，见 §0）。作者：李光浩（Guanghao Li，wsmslgh@gmail.com），与 Claude 协作完成。

这份文档写给接手这项研究的人（人或 AI）。读完它，你应当知道：
- 问题是什么；
- 哪些已经严格证明，哪些只是数值证据；
- 每个文件在哪里、怎么复现；
- 踩过哪些坑；
- 接下来具体该做什么。

---

## 0. 一句话结论（2026-09-29 更新：猜想已证）

对底数 1 < b < η = e^{1/e}，把 Kneser 型解写成 K_b = R_b∘(z + Σ c_n e^{2πinz})，其中 R_b 是吸引不动点处的正则解。

**已证明（主定理 E，投稿版 §sec:cusp，Theorem thm:cusp + Cor cor:conjecture）**：
- Kneser 实解从 b>η 出发，经 **η 附近的上半圆盘**做底数解析延拓，穿过 Shell–Thron 边界（与中性乘子是否 Brjuno/Cremer 无关），在 (η−r,η) 上全纯延拓过实轴且**恰等于缝合解 K^W_b**；再沿实轴附近（Prop weld-parameter 的邻域 N_W）延拓，在整段 (1,η) 上边界值 = K^W_b。
- 因而对这条延拓，c_n/Λⁿ → B_n e^{2πina}（所有 n），|c₁|/Λ → |B₁| = 0.0890584…，B₁ ≠ 0（Chéritat 定理）。
- 经下半圆盘延拓得到共轭支 K^{W,#}（与 Cor cusp-real-obstruction 的单值性障碍一致）。

**证明的核心想法（"倾斜初始区域"）**：
- 坐标 χ = log((u−u₁)/(u−u₂))，一步映射 Δ = −ε(1+O(ε))（λ₁ = 1−ε，ε 属于扇形 arg ε ∈ (−7π/12, π/12)）。
- 初始区域取过 iπ、方向 e^{iα} 的直线与其像之间的窄带，α = (arg ε + π/2)/2。外侧 α=0 恰是 Kneser 的直弦；内侧实轴处 α = π/4。
- 在 Z = A₁χ 坐标下，商曲面与平直圆柱之间有伸缩系数 O(ε) 的拟共形映射，所以两端必为穿孔——**不需要线性化，ST 边界不是障碍**。参数全纯性用 Ahlfors–Bers + ∂̄ 消去。
- 标记点取"连续分支上底点轨道第一次穿过带"的点（物理带是螺旋，后续穿越对应平移根 c_j）。从 n₀ 反推回 [0,1] 用平直模型 + 影随引理。
- 内侧识别：从底点交点沿带走到线段 (u₁,u₂) 经过下半平面，吸引时间虚部恰为 −h/2（Lemma realT 钉死），这正是 Prop weld 的 T−ih 分支；构造到缝合面的真全纯映射，局部度 1 ⇒ 双全纯 ⇒ 等于 K^W。

**全上半 ST 区域（2026-09-29，投稿版 §sec:global，Theorem thm:global）**：比较引理已证，经两路对抗审稿与一轮核验。结论：Kneser 解绕尖点进入后，在**整个上半 ST 区域** U⁺=b(H_λ) 单值延拓，沿 U⁺ 内任意路径边界值 = K^W（(1,η) 全段），不再限于实轴附近细通道。工具：另一会话的拟共形搬运（`paulsen-global-qc-transport-zh.md`：φ_λ(ζ)=ζ|ζ|^{2b}，b=(s−s₀)/(2Re s₀)，Ahlfors–Bers 全纯运动 h_λ∘E₀=E_λ∘h_λ）+ 本会话的比较引理：吸引端 h_λ 在 log-Koenigs 坐标下精确为实线性（σ_λ∘h_λ=k_λφ_λ∘σ₀，因与 ζ↦λζ 交换的共形映射必线性），排斥端提升映射与晶格 m₀Z+2πiZ 等变 ⇒ 线性+周期小误差；从而搬运带落在楔形 {|ς|≤(1+|t|)/100}，照换线引理做轨道对应，标记点由共轭精确对应。仍开放：Paulsen 族若在远离 η 的边界弧进入 U⁺，是否同一芽（√2 九位吻合支持）。

**复现与核对（2026-09-29 夜）**：六个 Arb 证书在当前代码下全部重跑通过（far_collar、last_boundary_arc、upper_halfplane、endpoint、parabolic_a、horn_coefficients）。另一会话的 a、B₁–B₃ 证书已核对（混叠误差界推导正确）；|B₁|=0.0890584364122133315632±5e-23，a=3.02929721441803609892499…。Prop zero-one-obstruction（b=1、b=0 不可去）证明已核对。本会话在 Prop attracting-real-slice 后加 Remark rem:stcover：F^tr 作为 s=log λ 的函数在整个 Re s<0 上单值全纯 ⇒ 在去心 ST 内部万有覆盖上延拓，b=1 处单值性（绕行 s↦s+2πi）未定；数值 |ĉ₁| 在 b↓1 缓慢下降（b=1.001 时 0.0770），Λ→1 仅在 λ≪e^{-40}。代码可用性一节补列 far_collar、last_boundary_arc 两个证书。投稿版 62 页。

**端点 e^{-e}（2026-09-29 深夜，投稿版 §sec:endpoint，Lemma lem:chi-crescent，Theorem thm:endpoint，计算机辅助）**：e^{-e} 处"退化"只是 ζ 线性插值的假象（1+σ(λ₊−1) 在 σ=½ 为零）；月牙在 L₊ 处夹角 arg λ₊→π 并不退化。改用对坐标 χ=log((ζ−1)/(ζ+1)) 的线性插值 M=x+iπ+σφ(x)，φ(t)=iθ+log S(iθ(t−1)/2)−log S(iθ(t+1)/2)，S=sinh w/w，条件 (a)–(e) 余量很大且对 Im λ<0 同样成立。证书 docs/certify_endpoint.py（约 30 秒）：λ∈[−1.1,−0.9]×[−0.1,0.1] 方形（R′ 上 λ₊ 单射锚定分支）+ 实轴带 λ∈[−12,−0.2]×[±0.001]（链式分支）。结论：thm:upper 的族在 b∈[e^{−12e^{12}},0.7833] 的邻域上全纯（含 e^{-e}），边界值实解析。b∈(1,η) 上伙伴不动点为实，直月牙塌缩（需倾斜）；b→1 时 θ→∞；b→0 需 χ 形式尾巴分析——列为开放问题 1。修改前备份 /tmp/main.before-endpoint.tex。投稿版 58 页。

**整个上半平面（2026-09-29 晚，投稿版 §sec:upper，Theorem thm:upper + Cor cor:paulsen，计算机辅助）**：Kneser 实解沿上半 b 平面任意路径延拓，得到单值全纯族（外部=直弦月牙族，U⁺ 内=F^tr，跨整条开边界弧）⇒ 路径无关，Paulsen 族（按其定义为上半平面主叶上的延拓）就是本文的族，开放问题 1 解决。参数：λ=L₊ 的乘子，a=g(λ)=λe^{-λ}，θ 为 (λ−2iθ)e^{2iθ}=λ 的非零根；E⁺ ≅ Λ⊂{|λ|>1,0<Im λ<π,0<Im g<π,g∉g(D̄)}。证书 `docs/certify_upper_halfplane.py`（约 15 分钟，10 进程）：(P) 尖点 Rouché+极坐标缩放引理（φ=0,−π/2 实方向用 ∂_φ 符号）⇒ θ 落入已证锥；(T) 尾巴 Re λ≤−12，κ=1/λ、θ=π−κD，D 为固定凸集上的压缩不动点，缩放后在 κ=0 解析，标记恒为 w₋₁=0（ζ(0)→N(0,½)），6230 盒；(K) 核 −12≤Re λ≤5，星形 g(D) 剔除、复 Krawczyk θ 分支、212368 对相邻叶子分支一致、锚点 θ=1 于 λ=cot1+i、端点精确值 f(±1) 加 ∂_t 符号处理 Im λ→0 退化边（b→(0,e^{-e})）、θ 落在已证领/锥（或其共轭，s_θ̄(t)=−conj s_θ(−t)）时直接引用，55110 叶；(I) 接口。一轮 AI 对抗审稿（无致命，4 个严重均已修：锚点、尾巴唯一性、§far 引理适用范围 lem:far-scope、θ=0 恒为根）。仍开放：端点 e^{-e}、(0,e^{-e}) 与负轴上的边界值。修改前备份 /tmp/main.before-upper.tex。投稿版 57 页。

**远离尖点穿越边界（2026-09-29，投稿版 §sec:far，Theorem thm:far，计算机辅助）**：在另一会话"单一远端弧入口"（`paulsen-far-entry-proof-zh.md`）基础上推广到几乎整条上边界弧。θ 参数化 λ±=θcotθ±iθ、L±=re^{±iθ}；仿射坐标 ζ=(w/r−cosθ)/(i sinθ) 把弦变成 [−1,1]，E 共轭为整函数 s_θ(ζ)=(e^{iθζ}−cosθ)/(i sinθ)。区域 Θ = 锥 {p(1+ic):0<p≤0.1,0≤c≤0.1} ∪ 领 {p+ivp²:0.1≤p≤2.2,0≤v≤V(p)}。证书 `docs/certify_far_collar.py`（Arb，约 6 分钟，33027 盒全过）验证：Im g<0、Im(conj(s')g)<0（g=(s(t)−t)/(1−t²)，⇒ 月牙 Jordan、插值 N=t+σ(s−t) 为微分同胚、接缝朝向对）、∂_q|λ₊|²<0（每条竖直纤维恰穿过边界一次）、a'≠0、p≤1.9 时 |Im a|<π（主叶），以及"首次进入"标记（从 w₋₁=0 起，Krawczyk 证明在月牙内或处于接缝图卡）。锥上标记由解析引理 lem:far-cone 给出：精确恒等式 q'=q e^{iθ}T(v−iθ)/T(v)，T=sinh w/w，只需控制 y 步长 ∈(0.84p,1.16p)，**不需要 x 的界**。结论：对每个 0<α≤α₁=0.9354π 的上边界点，Kneser 解沿 b(p+iq) 竖直路径（log b 沿路径延拓）全纯穿过该点，进入 U⁺ 时恰为 F^tr；p≤1.9（α≤0.753π）整条路径在主叶上。对这些竖直路径，与 Paulsen 族的同一性归结为他是否沿该路径解析延拓；主叶内仅 p≤1.9 可直接使用。靠近 e^{−e} 的末段弧由下段新证书覆盖。经一轮 AI 对抗审稿（无致命，2 个严重已修：b 平面非主叶问题→定理改用 a=log b 表述；seam_ok 的 σ<1 论证→Krawczyk 盒须含实边已知根 (t,1)）。修改前备份 /tmp/main.before-far.tex。投稿版现 54 页。

**末段边界弧已闭合（2026-09-29，投稿版 Theorem thm:last-arc）**：旧竖直路径的覆盖止于 0.935π；新证书完成其后的开放弧。新证书 `docs/certify_last_boundary_arc.py`（Arb，约 33 秒）隔离 λ₊(θ*)=−1 的根 θ*=2.29857900665…+0.76604606099…i，证明 λ₊ 在 [2.19,2.31]+i[0.71,0.78] 单叶；以 79 个参数盒覆盖 0.935π≤α≤0.9999π，以 θ* 周围半径 0.0002 的方盒覆盖余段。对 t≤0.95 直接验证 Im g<0、Im(conj(s′)g)<0；对 t≥0.95 验证这两量的 t 导数均正，而在 t=1 它们精确等于 −sin α/2<0。故直月牙对每个 α<π 都成立，虽然 α→π 时端点角度趋零。Krawczyk 证明 w₋₁=0 在整段弧上均严格处于月牙内，标记无需轨道追踪。与旧定理在 α=0.935π 重叠后由解析延拓接通 F^tr，得到整个开放上边界弧 0<α<π 均可全纯穿越。**端点 e^{−e} 本身仍未覆盖。** 对 α>0.753π，旧竖直路径会离开主叶，但可先沿 p≤1.9 的已证主叶路径进入 U⁺，再在 U⁺ 内走到目标附近并由新月牙穿出；这样每个开放弧点都有主叶路径。Paulsen 同一性仍需证明他的构造确是沿其中一条路径的解析延拓。

**√2 处的强数值证据（2026-09-29）**：直接解缝合方程（80 位、32 模、残差 <1e-75，`docs/paulsen_sqrt2_check.py`）得 Im K^W_{√2}(1/2) = −1.18899697185e-48，与 Paulsen 120 位的 −1.18899697e-48 **全部 9 位吻合（含符号）**，相对差 1.6e-9 = 他的舍入。√2 离 η 很远，是 Paulsen 同一性问题的强数值支持，不能取代沿路径的解析延拓证明。

**投稿版重构（第四轮整篇审稿后）**：删去旧的条件性主定理 C（边界值）、Cor W1、Thm bv、§unif；Prop exterior-real-parameter 移入 §cusp；尖点推论块移到 §cusp 末"Consequences at the cusp"；摘要重写为约 200 词，标题改为"Kneser's tetration continued around the cusp…"；主定理现为 A 汇流、B 缝合解、C 一阶项、D 绕尖点延拓；加 Epstein 有限型机制注记（B₁≠0）、记号重载说明；参考文献删 8 条未引用。现 45 页。

**仍开放（不影响上面的定理）**：Paulsen 2019 的构造是否给出沿本文主叶路径的联合全纯解析延拓，以及所得参数芽是否与从实外侧出发的 Kneser 芽一致。仅凭 U⁺ 单连通或一组数值吻合，不能识别两个分别定义的族。另有 parabolic 端点 b=e^{−e} 本身的穿越问题；整条开放弧已解决。

**审稿记录**：新节经三轮 AI 对抗审稿（几何/组合、解析/识别、平直模型/影随、全节一致性），无致命错误，所有指出的缺口已修。**尚无人类专家审读**。

**版本**：`docs/paper-submission/main.tex` 已**精简为 47 页投稿版**（删去约 3000 行已被新定理取代的外侧/内侧区间证书与 Brjuno 归约）；完整存档版为同目录 `main-full.tex`（79 页，含全部证书与 Brjuno 材料）。修改前备份：/tmp/main.before-cusp.tex、/tmp/main.before-cusp-review1.tex、/tmp/main.before-cusp-review2.tex。数值核对脚本 `docs/cusp_tilted_check.py`。

---

## 1. 必读文件（按顺序）

| 文件 | 内容 |
|---|---|
| `docs/paper-submission/main.tex` / `main.pdf`（69 页） | **投稿版论文**，最干净、最新。先读这一份。 |
| `/Volumes/dream/halfexp/Li-Kneser-regular-separation-submission.pdf` | 投稿版 PDF 的带名副本，方便发给别人。 |
| `docs/paper-separation/main.tex` / `main.pdf`（70 页） | **实验记录版**。保留了完整研究史：撤回的拟合、各轮勘误、"What is claimed" 一节。查历史时看它，不要投它。 |
| `docs/mrr-first-order-zh.md` | 一阶项 κ⁽ⁿ⁾ 的抛物点级数公式及其证明思路（主定理 D、Theorem E）。 |
| `docs/certify_exterior_mark.py` | Arb/Acb 有理区间证书：近尖点外侧的一条带 $w=1$ 标记的参数路径；运行 `python3 docs/certify_exterior_mark.py`。 |
| `docs/certify_brjuno_exterior_mark.py` | 强化区间证书：把上述路径终点指定为二次无理 Brjuno 旋转数 $\alpha=(\sqrt2-1)/26$；运行 `python3 docs/certify_brjuno_exterior_mark.py`。 |
| `docs/certify_exterior_flat_cylinder.py` | 全路径圆柱参数化的 Arb 证书：严格界定 $|\mu|<1/10$、$K<11/9$，含中性边界和两端；运行 `python3 docs/certify_exterior_flat_cylinder.py`。 |
| `docs/certify_exterior_wide_corridor.py` | 更宽复参数闭盒 $|\Re\theta-0.1000435842|\le10^{-8}$、$|\Im\theta|\le0.01$ 的 Arb 证书：Jordan 区域、标记点、第 28 层逆支、全圆柱 $|\mu|<1/10$ 与 $\Re b'>0.05$；运行 `python3 docs/certify_exterior_wide_corridor.py`。 |
| `docs/certify_exterior_frozen_abel.py` | 显式冻结 Abel 坐标的 Arb 证书：标记路径上 $|P-i|<0.09$、$|P_Y|<0.01$；$|\Im\theta|\le0.01$ 宽盒上 $|P-i|<0.18$、$|P_Y|<0.004$、冻结竖直斜率虚部 $>0.98$，全圆柱残差 $<0.001\operatorname{sech}^2(Y/20)$，残差导数 $L^4$ 范数 $<0.00025$；运行 `python3 docs/certify_exterior_frozen_abel.py`。 |
| `docs/certify_interior_chord_overlap.py` | Arb/Acb 严格证书：在 $\theta_0=0.1000435842+0.01i$，113 个有理 $t$ 小区间的前向像至多 505 步进入上方吸引不动点的显式收缩圆盘，故外侧弦的 $t\in[-0.13,1]$ 子弧位于同一即时吸引域；另证标记点平直坐标 $t_m>0.14$，与解析缝线界合用推出归一化缝点 $t_*>0$；运行 `python3 docs/certify_interior_chord_overlap.py`。 |
| `docs/certify_interior_lower_overlap.py` | Arb/Acb 严格证书：在同一内侧参数，先以 $N=1000$ 次前向极限构造下方 Poincaré 函数，并用显式尾界 $<2.1\cdot10^{-10}$ 包住极限；将 $S([0,1])$ 分成 32 段，最多再迭代 427 步进入 $B(L_+,0.01)$，同时排除 $L_+$ 的逆像；运行 `python3 docs/certify_interior_lower_overlap.py`。 |
| `docs/certify_interior_transition_slope.py` | Arb/Acb 严格证书：64 段导数球运算与上方 Koenigs 导数的乘积尾界给出 $0.94<\Re T'<1.06$、$|\Im T'|<0.056$、$T(1)-T(0)=1$；下移周期后的缝线位于 $\Im w<-2.5$，从而在 $\theta_0$ 构造局部解析缝合族；运行 `python3 docs/certify_interior_transition_slope.py`。 |
| `docs/certify_interior_path_fold.py` | 独立 Arb/Acb 点证书：在直线参数路径上的 $\theta_\dagger=23541/2560000+0.01i$，下方曲线的上方 Koenigs 时间满足 $\Re T'(0)<-0.11272$；运行 `python3 docs/certify_interior_path_fold.py`。 |
| `docs/certify_interior_self_intersection.py` | Arb/Acb 与二维 Krawczyk 严格证书：同一 $\theta_\dagger$，在 $x\approx0.0456334948$、$y\approx0.2767500344$ 附近有唯一横截根 $S(x)=S(y)$。两高度之间的整段物理曲线位于不含 $L_+$ 的共同吸引图卡圆盘内，所以同一对点在上方时间缝线上也重合；运行 `python3 docs/certify_interior_self_intersection.py`。 |
| `docs/certify_interior_parameter_basin.py` | **尚未完成的参数网格试验**：已独立覆盖路径的 $p\in[0.012,0.1002]$；$p\in[0,0.012]$ 的第 15 个有理小区间尚未认证，因此不能引用为整条路径的吸引域定理。自交命题不依赖此试验。 |
| `docs/probe_interior_detour.py` | **非严格数值探路**：在 $\Im\theta=0.02,0.05,0.1$ 的若干水平参数点及 17 个高度上抽样，较深的 $q=0.05$ 路线斜率接近 $1$；这提示从实内侧先升高 $q$ 再向 $p=0.1000435842$ 绕行，但不能据有限样本声称整条参数路线上无自交。 |
| `docs/certify_interior_quotient_loop.py` | Arb/Acb 严格证书：在同一点，$E^{75}S([0,1])$ 位于外侧弦上方、$E^{77}S([0,1])$ 位于弦下方；$E^{76}S$ 对弦的有向高度导数 $<-0.03$，恰好横截一次。借助精确恒等式 $\zeta(Ew)=s(\zeta(w))$，把 $E^{77}S$ 的前段与 $E^{76}S$ 的后段接成外侧商圆柱的一条嵌入本质圆；运行 `python3 docs/certify_interior_quotient_loop.py`。 |
| `docs/certify_interior_early_return.py` | 独立的 Arb/Acb 64 段证书：同一下方圆在第 13、14、15 次前向像就有另一条回归；第 14 次像的弦高度导数 $<-0.03$ 且恰好横截一次，第 13 次像高度 $>0.005$、第 15 次像高度 $<-0.03$，所成商圆与 76/77 次商圆处于不相交的实坐标条带 $(0.26,0.31)$、$(0.48,0.52)$；运行 `python3 docs/certify_interior_early_return.py`。 |
| `docs/separation-first-mode-zh.md`、`docs/separation-mode-two-zh.md`、`docs/base-separation-zh.md` | 早期中文研究记录：第一模、第二模、问题的最初提法。 |
| `docs/external-validation.md` | 与 fatou.gp 等外部实现的对照记录，以及几个坑。 |
| 项目记忆 `~/.claude/projects/-Volumes-dream-halfexp/memory/kneser-base-separation.md` | 按时间顺序的完整研究日志，含所有关键数字和踩坑记录。**最权威的流水账。** |

---

## 2. 投稿版论文结构与各结论的状态

| 位置 | 结论 | 状态 |
|---|---|---|
| **主定理 E（§sec:cusp，Theorem thm:cusp，Cor cor:conjecture）** | Kneser 经 η 附近上半圆盘绕尖点延拓，边界值 = K^W（(1,η) 全段，路径经 N_W）；猜想 c_n/Λⁿ→B_n e^{2πina} 对此延拓成立 | **已证（2026-09-29）**，三轮 AI 对抗审稿；下表中 P0–P2、证书与 Brjuno 各行对猜想已不再必需（仅存于 main-full.tex） |
| 主定理 A（§4 confluence） | 汇流：τ_n(b) → B_n e^{2πina}（对所有 n）；t_n/t₁ⁿ → B_n/B₁ⁿ | **已证**；$B_1\ne0$ 由单奇异值抛物重整化定理给出 |
| 主定理 B（§ sewing / characterisation） | 缝合解 K^W 存在且唯一（Definition class：两侧正则表示 + 缝高条件），并有加性界 \|c_n/Λⁿ − τ_n\| ≤ C_n Λ | **已证**，经三轮对抗审稿 |
| Prop weld-parameter | 对每个实底数 $b_0\in(1,\eta)$，解析加厚缝线得到随 $b$ 全纯变化的紧化球面族；用两端及 $R_b(0)=1$ 标记固定球面坐标，故归一化内侧缝合解在 $b_0$ 附近的共同正则 $z$ 域上联合全纯 | **已证**；这些局部参数盘可拼成整段实区间的开邻域，但宽度未量化，也未到达 Shell–Thron 边界弧 |
| Prop exterior-real-parameter | 对每个实 $b_0>\eta$，两共轭不动点间的竖直弦及其指数像构成显式初始区域；沿指数映射粘合两边、用 Koenigs 坐标补上两端，得到随复底数全纯变化的三标记球面族。实动力实轴上的有限图卡链包含 $w=1$ 与 $[1,b]$，故归一化 Kneser 支在每个 $b_0$ 附近的共同复高度邻域上联合全纯 | **已证的外侧实轴局部解析性**；与 Trappmann–Kouznetsov 2011 的初始区域唯一性准则识别经典支。尚未到达非尖点 Shell–Thron 弧，(P0) 仍未证 |
| Prop exterior-curve-collar | 用复参数 $\theta$ 写出 $b(\theta)=\exp[\theta e^{-\theta\cot\theta}/\sin\theta]$ 和两不动点；在 $\Re\theta=p>0$、$|\Im\theta|\le Mp$ 的近尖点锥内，弦与指数像保持 Jordan 且仅在端点相遇。存在边界曲线 $q_c(p)=p^2/6+O(p^3)$；$0\le q<q_c(p)$ 时两乘子仍排斥，且 $\theta\mapsto b$ 在小楔形内单叶 | **已证的外侧几何底数走廊**：无标记两端商曲面可逼近非尖点 Shell–Thron 弧。仍未证明 $w=1$ 的标记沿整个走廊运输或固定高度域的统一性，故不是 (P0) |
| Prop exterior-marked-path | 使用 `docs/certify_exterior_mark.py` 的 Arb 外向舍入区间证书：沿 $\theta=1/10+iq$ 从 $q=0$ 到唯一的 $q_c<1667/10^6$，第 28 次迭代 $E_b^{28}(1)$ 一直严格位于初始区域内，底数路径单叶，边界前两不动点均排斥 | **已证一条外侧归一化芽的解析运输路径**；只保证 $z=0$ 的局部芽，没有证明靠近边界的统一 $[0,1]$ 高度域或边界极限，故 (P0) 仍未闭合 |
| Prop exterior-brjuno-path | 取预先指定的 $\lambda_c=e^{2\pi i(\sqrt2-1)/26}$。区间收缩映射唯一圈定 $\theta_c=0.1000435842+0.0016682119i\pm10^{-8}$（逐坐标）；对包含 $\Re\theta_c$ 的整盒和 $0\le\Im\theta\le0.00166823$，外向舍入验证第 28 次轨道点一直在初始区域、下端排斥、上端在终点前排斥，且底数路径不自交 | **已证通向具体 Brjuno 边界点的外侧归一化芽路径**；二次无理性给出 Brjuno 条件。边界芽极限另见下一行；这条路径本身不提供共同 $[0,1]$ 高度域 |
| Prop exterior-pullback-cell | 同一区间证书又验证 $E_b^k(0)$（$0\le k\le28$）在整个路径上位于初始区域弦的上方，统一有 $\Im\zeta>0.02$。对不含这些奇异轨道点的 Jordan 区域逐次取解析对数，得到 $E_b^{28}$ 的全域逆支 $\Phi_b:H_b\to D_b$，并证明其在两条缝合弧上满足 $\Phi_b(E_b(w))=E_b(\Phi_b(w))$ | **已证物理平面内包含 $w=1$ 的整块 Jordan 回拉域**，直到指定 Brjuno 边界；其边界两弧由 $E_b$ 对应，两端仍为原不动点。该命题本身只给物理回拉域；规范化高度整圈的展开已在后续 Cor exterior-full-height 证明 |
| Prop exterior-flat-cylinder | 弦与指数像之间做线性插值，以 $z=x+20i\operatorname{artanh}t$ 为平直圆柱坐标；因子 $(1-t^2)$ 消去后，Arb 级数尾项及全盒区间计算给出 $|\mu|<1/10$ | **已证直到中性边界的整块商圆柱 $K<11/9$ 拟共形模型**，包含两端而非仅有限中段；该数值界本身尚未推出规范化缝线的单次横截 |
| Prop exterior-brjuno-germ-limit | 区间证书对逐坐标半径 $10^{-8}$ 的整个 $p$ 区间证明唯一中性高度 $q_c(p)$；平直圆柱上的 Beltrami 系数在紧参数盒中以 $L^\infty$ 范数连续，三标记归一化由 Ahlfors–Bers 稳定性连续，标记处的共形导数统一非零 | **已证一小段 Shell–Thron 边界弧上，外侧归一化芽在共同小高度盘上有统一单侧极限**；此命题本身只覆盖小高度盘；后续 Cor exterior-full-height 覆盖 $[0,1]$ |
| Prop exterior-analytic-germ-corridor | 同一 Beltrami 系数作为 $L^\infty$ 值函数在复参数 $\theta$ 中全纯。Ahlfors–Bers 参数定理与平直坐标逆映射的 $\bar\partial$ 消去等式，给出标记附近统一化坐标在 $(\theta,w)$ 中联合全纯；新增宽盒证书在 $|\Im\theta|\le0.01$、$|\Re\theta-0.1000435842|\le10^{-8}$ 上验证 Jordan 区域、标记点、逆支、$|\mu|<1/10$ 及 $\Re b'>0.05$ | **已证外侧 Kneser 芽在共同小高度盘上经显式宽复底数走廊全纯穿过一小段非尖点边界弧**；此命题本身是外侧芽级部分；后续 Cor exterior-full-height 已补齐外侧共同 $[0,1]$ 域，内侧分支识别仍未证 |
| Prop exterior-real-seam-anchor | 实参数处的复共轭在三点归一化商球面上成为 $Q\mapsto1/\overline Q$，其固定集为 $|Q|=1$；嵌入缝线仅在 $t=0$ 固定且与实轴横截。平直圆柱上 $v=-(2\pi)^{-1}\log|Q|$ 满足显式一致椭圆方程 $\nabla\cdot(A_\mu\nabla v)=0$ | **已证实轴起点唯一简单穿越**；沿 $q$ 到中性边界若穿越数改变，必有 $v(0,Y)=\partial_Yv(0,Y)=0$。此处提出的切触排除目标已由后续 Prop exterior-seam-monotonicity 完成 |
| Lemma exterior-seam-end-slope | 把统一化坐标在圆柱两端竖直平移，归一化拟共形紧性给出乘子 $\lambda_\pm$ 的直扇形极限；解析缝线图卡与 Cauchy 估计把收敛升级到沿缝线的 $Y$ 导数。宽盒 Arb 证书验证两端极限斜率 $\Im[-1/(10\Log\lambda_+)]$、$\Im[1/(10\Log\lambda_-)]$ 均 $>0.98$ | **已证整条参数盒的两端最终严格单调**，故所有可能切触限于某个有限 $|Y|\le Y_0$；后续 Prop exterior-seam-monotonicity 用全局逐点估计直接排除了切触，无须数值阈值 $Y_0$ |
| Prop exterior-frozen-abel / exterior-frozen-correction | 显式构造冻结 Abel 坐标 $h^0$；Arb 证书给标记路径 $|P-i|<0.09$、宽盒冻结斜率 $\Im c>0.98$ 和残差 $|\partial_YF|<0.001\operatorname{sech}^2(Y/20)$。周期 Beurling 算子 $L^4$ 界与收缩法进一步给真正统一化坐标 $h$ 的 $\|\partial_x(h-h^0)\|_4<0.032$、$\|\partial_Y(h-h^0)\|_4<0.037$ | **已证整条标记路径上的全局积分误差界**；逐点升级见下一行 |
| Prop exterior-seam-monotonicity | 竖直差商避免跨缝线求 $x$ 导数；Arb 在 $|\Im\theta|\le0.01$ 宽盒验证 $\|P-i\|_\infty<0.18$、$\|P_Y\|_\infty<0.004$ 与 $\|F_{YY}\|_4<0.00025$。沿用平面 Beurling 范数 $<4.725$ 到周期圆柱，取 $\|T\|_4<3.5$；收缩与显式二维 Morrey 界给 $\|e_Y\|_\infty<0.041$，从而 $\partial_Y\Im h(0,Y)>0.93$ | **已证宽盒整条缝线严格单调**，同时覆盖中性弧两侧和内侧点 $\theta_0$；单位圆恰好横截一次 |
| Prop interior-chord-overlap | 在严格内侧点 $\theta_0=0.1000435842+0.01i$，把弦 $t\in[-0.13,1]$ 划分为 113 段；Arb 逐段认证最多 505 次迭代进入 $B(L_+,0.01)$，且该盘收缩不变。另一组区间界将归一化单位圆与弦的唯一交点定位在 $t_*>0$；其拉回开发值因此位于完整吸引域，并在某个非整数实高度 $z_*\in(0,1)$ 的复高度与复底数邻域具有联合全纯的上方 Koenigs 坐标 | **已证实际外侧归一化解与内侧上方动力图卡在开参数×开高度域上物理重叠**；尚未证明外侧/内侧全局缝合坐标相同，也没有认证靠近下方排斥端的剩余弦 |
| Prop interior-sewing-circle | 在同一个严格内侧点，以显式下方 Poincaré 极限尾界和 Arb 轨道圆盘认证 $S([0,1])$ 全部在上方吸引域内且避开上方不动点逆像。对 $T=R_+^{-1}\circ S$ 的 64 段导数球与尾积界给出 $0.94<\Re T'<1.06$、$|\Im T'|<0.056$；整圈次数为一，移位缝线位于 $\Im w<-2.5$ | **已证该内侧点附近有局部解析缝合族**，且 $w=0$ 在上方图卡；尚未认证从实内侧底数连续运到此点，也未识别此局部族与外侧归一化族 |
| Prop interior-path-crossing | 在同一直线参数路径的 $\theta_\dagger=23541/2560000+0.01i$，Arb 的 4500 步 Poincaré 尾界和二维 Krawczyk 包含证明 $S(x)=S(y)$，其中 $x\in0.0456334948\pm10^{-4}$、$y\in0.2767500344\pm10^{-4}$，横截且两个区间不交；$S([0.04,0.28])$ 全部落在不含上方不动点的共同吸引图卡圆盘。另一证书给 $\Re T'(0)<-0.11272$ | **已严格排除沿 $\theta=p+0.01i$ 全程维持这条下方正则圆为嵌入正斜率缝线**；并未排除换参数绕路、换缝线或其他解析延拓机制 |
| Prop interior-quotient-loop | 在 $\theta_0$，对下方正则曲线的第 75、76、77 次前向像作 Arb 的 64 段值球及导数球计算；中段第 76 次像严格横截外侧初始弦一次，前段第 77 次像和后段第 76 次像分别严格位于外侧 Jordan 单胞内，端点及跨缝点按指数对应；实部单调确保无自交 | **已证内侧缝合圆在外侧商圆柱里是一条嵌入本质圆，并有共同物理环形图卡**；这比两处各自的吸引域包含更强，但尚不能凭环形重叠认定两张紧化球面的全局统一化坐标相同 |
| Cor interior-two-returns | 同一 $S([0,1])$ 的第 14/15 次前向像也在外侧初始胞元内接成嵌入本质圆；证书给出第 13/15 次像处于弦的两侧、第 14 次像一次横截，且所得圆与第 76/77 次回归圆严格不交 | **已证物理回归圈并非唯一**；选择一条回归圈尚不能自动给出从内侧商到外侧商的规范比较映射，必须补证中间带的单值延拓与一致性 |
| Cor interior-end-germs | 外侧商球面在 $\theta_0$ 的两端本来各有 Koenigs 穿孔坐标；将下方精确关系 $\tau_-(S(z))=-\mu^z$ 和上方精确关系 $\sigma_+(R(z))=\sigma_+(1)\lambda_+^z$ 代入，得到外侧全局坐标沿这两张正则图卡分别是 $C_-^{-1}e^{2\pi iz}(1+O(e^{-2\pi iz}))$ 与 $C_+e^{2\pi iz}(1+O(e^{2\pi iz}))$，$C_\pm\ne0$ | **已证两端各自的局部一次穿孔芽相容**；与共同环形图卡之间还隔着两段紧的中间带，未证明解析延拓能贯通或两种统一化坐标一致 |
| Prop exterior-single-crossing / Cor exterior-full-height | 缝线与 $|Q|=1$ 的单次横截已由上一行验证。单位圆由标记和缝点分成两弧，分别用回拉域 $D_q$ 及 $E_b(D_q)$ 展开，并由缝合等变式解析拼接 | **外侧完整高度走廊已证**：指定非尖点 Brjuno 边界附近有复底数邻域 $U_*$ 与共同连通 $W\supset[0,1]$，外侧 Kneser 族在 $U_*\times W$ 联合全纯；内侧缝合支到同一弧的运输和两支识别仍未证，故 (P0) 整体未闭合 |
| Cor exterior-wide-full-height | 宽盒上每个参数均有唯一横截与带标记回拉域；把 Prop exterior-single-crossing 的局部展开沿 $J=\{0.1000435842+iq:0\le q\le0.01\}$ 有限覆盖并用原点芽的恒等定理拼合 | **同一外侧归一化支在整个 $J$ 的某个连通复参数邻域与共同 $W_J\supset[0,1]$ 上联合全纯**，从实外侧越过中性边界，深入到一个上方吸引、下方排斥的内侧点；仍未识别为实内侧缝合支 |
| Cor exterior-boundary-zero | 外侧完整高度路径经 $\Phi(H)$ 与 $E_b(\Phi(H))$ 展开；证书表明 $E_b^{28}(0)\notin\overline H$，所以路径避开 $0$。沿标记参数路径固定 $\Log F(0)=0$，从实底数的正值路径得 $\Log F(1)=\log b$；反向对数于是给共同 $W_-\supset[-1,1]$，且 $F(-1)=0$ 为单零点，下一步向 $-2$ 有 $2\pi i/\log b$ 绕行 | **已证外侧边界支的零后退标签**，与内侧缝合支的一项必要不变量相同；这仍不足以证明两支相等 |
| Cor exterior-boundary-normal | 将 $(F_\theta(z)-1)/z$ 与 $F_\theta(z)/(z+1)$ 在 $z=0,-1$ 全纯延拓，利用联合全纯性与非零导数，在边界小参数盘及固定高度圆盘上得到 $c|z|\le|F_\theta(z)-1|\le C|z|$、$c|z+1|\le|F_\theta(z)|\le C|z+1|$，并控制 $F_\theta,1/F_\theta$ 于原点盘 | **外侧归一化根统一隔离，外侧 (P1) 在该非尖点小弧的共同正则高度域上已满足**；内侧 (P1) 仍未证 |
| Cor exterior-end-labels | 外侧球面坐标在上端有单零点、下端有单极点；与 Koenigs 穿孔坐标比较，经典 Kneser 支在两个竖直端点的整数标签均为 $m=0$，首系数在各实底数局部参数盘上全纯且不为零 | **已证的两端分支种子数据**；没有建立沿 (P0) 走廊的共同半带或到边界的统一控制 |
| Cor exterior-uniform-tails | 在每个实 $b_0>\eta$ 附近的共同上下半带，$\sigma_{\pm,b}(\kappa_b(z))=e^{\ell_{\pm,b}z}h_\pm(b,e^{\pm2\pi iz})$，其中 $h_\pm$ 对底数及 $q$ 联合全纯且无零点。紧实底数子区间上对 $0\le\Re z\le1$ 有统一指数尾界 $|\kappa_b(x\pm it)-L_\pm(b)|\le Ce^{-ct}$ | **已证的外侧局部一致尾项**；衰减常数和共同半带未沿复底数路径控制到边界 |
| Cor sewn-nonreal | 靠近 $\eta$ 的每个实底数上，归一化缝合解在 $z=0$ 的任意实邻域内都有非实值：若局部全实，则上方 Koenigs 时间修正 $P$ 在实轴上实值；它又只有非负 Fourier 模，故只能为常数，与已证的 $c_1\ne0$ 矛盾 | **已证**；这是内侧缝合解的定性性质，不能据此断言尚未识别的 Paulsen 边界族具有相同性质 |
| Cor imaginary-profile | 在 $z=0$ 附近固定复圆盘上，$(K_b^W(z)-R_b(z))/\Lambda\to(F_\eta^{\rm att})'(z)B_1e^{2\pi ia}(e^{2\pi iz}-1)$ 局部一致，且所有 $z$ 导数收敛；特别地，实高度上的虚部除以 $\Lambda$ 收敛到该轮廓的虚部。由 W2 的指数 Fourier 界，$n\ge2$ 的尾项统一为 $O(\Lambda^2)$ | **已证**；给出完整复高度首阶尺度与形状。Paulsen 在 $b=\sqrt2$ 的微小虚部仍只是该底数上的数值观察，不能用这个尖点渐近式直接认证 |
| Cor cusp-real-obstruction / Remark conjugate-bypasses | 可在 $z=0$ 任意小的实邻域选定一个非整数高度 $x_*$，使每个足够靠近 $\eta$ 的实底数 $b<\eta$ 都满足 $|\operatorname{Im}K_b^W(x_*)|\ge c\Lambda(b)$；Schwarz 反射遂排除从 $b>\eta$ 的实值归一化支直接全纯穿过实尖点并在另一侧等于内侧缝合支。若两条共轭绕行路径均存在且一条抵达缝合支，则另一条抵达其共轭支，在 $x_*$ 的差至少为 $2c\Lambda(b)$ | **已证的尖点限制与条件性绕行分支差**；绕行解析延拓的存在性仍未证 |
| Cor conjugate-sewn-jump | 对实 $1<b<\eta$，反射支 $K_b^{W,\#}(z)=\overline{K_b^W(\bar z)}$ 是另一条局部联合全纯解；它与 $K_b^W$ 在所有非负整数高度及 $z=-1$ 一致，且在 $-1$ 都有单零点、在 $-2$ 具有同一对数绕行型，但在固定非整数实高度 $x_*$ 的差至少是 $2c\Lambda(b)$ | **无条件已证**（对近尖点实底数的差）；反射支是否由 $b>\eta$ 的 Kneser 支沿下方绕行得到仍为条件性问题 |
| Prop cusp-no-puiseux | 对每个充分小的非零实高度 $x$ 及任意整数 $q\ge1$，$t\mapsto K^W_{\eta-t^q}(x)$ 沿正实 $t$ 的芽不能亚纯穿过 $t=0$。其与共轭反射的差非零且为 $O(e^{-c/t^{q/2}})$，与非零 Laurent 展开矛盾 | **已证**；排除在实尖点通过任何有限代数分支参数消除该奇性。若该值能单值全纯覆盖完整穿孔 $t$ 圆盘，则 $t=0$ 必为本性奇点；完整穿孔圆盘延拓的存在性未证 |
| Cor cusp-two-jet | 虽然 $K_b^W(0)=1$ 恒定，但 $\bigl(\operatorname{Im}(K_b^W)'(0),\operatorname{Im}(K_b^W)''(0)\bigr)/\Lambda(b)$ 有非零向量极限；其坐标由 $f'(0),f''(0)$ 和 $A=B_1e^{2\pi ia}$ 显式给出。故前两阶高度导数中至少有一个在任意有限基底分歧后无法亚纯穿过实尖点，并以 $\Lambda$ 量级区分共轭内侧支 | **已证**；给出固定归一化高度处的有限喷流见证，不声称它能识别任意其他解析解或解决 (P0)–(P2) |
| Cor sewn-cusp-local | 当实底数 $b\to\eta^-$，归一化缝合解 $K_b^W$ 在原点附近固定复高度圆盘上局部一致收敛到抛物吸引超函数，所有 $z$ 导数也收敛；因而近尖点内侧的额外 $K_b^W(z)=1$ 根统一远离原点 | **已证**；只覆盖实轴靠近尖点的内侧分支，不覆盖 Shell–Thron 边界弧 |
| Cor cusp-corridor | W1 的局部底数圆盘可沿 $(b_3,\eta)$ 拼成连通复底数开域 $N_\eta$；在整个开域的固定复高度圆盘内，$K_b^W$ 与其倒数统一有界、根隔离，且 $b\to\eta$ 时趋于抛物吸引超函数 | **已证**；$N_\eta$ 可以任意收窄，未证其含固定角度扇区或到达非尖点的 Shell–Thron 弧 |
| Corollary limits | 对 K^W，所有 $n$ 的 $c_n/\Lambda^n\to B_n e^{2\pi i n a}$，且 $c_n/c_1^n\to B_n/B_1^n$ | **已证**；首模非零有解析证明，但 $|B_1|\approx0.0890584$ 的十进制值仍未有认证误差包络 |
| 主定理 D（§ first-order） | 当 $B_n\ne0$ 时，一阶项：log(τ_n/τ_n^∞) = κ⁽ⁿ⁾ p + O(p²)，κ⁽ⁿ⁾ 由抛物点收敛级数给出 | **首模无条件已证**；高阶尚未逐一证明 $B_n\ne0$ |
| Theorem E（§ higher orders） | 当 $B_n\ne0$ 时，关于 p 的全阶对数渐近展开，每个系数都是收敛的抛物点级数 | **首模无条件已证**；高阶仍须证明相应 $B_n\ne0$。加性 Fourier 系数的各阶展开不需除以 $B_n$ |
| 主定理 C（boundary values） | 若 Paulsen 族在某开集上属于类 𝒞，则 κ = K^W，边界值存在，推论对 κ 成立 | **条件性**，条件即 §5 的缺口 |
| Remark paulsen | Paulsen 2019 的 Prop 2（唯一性）是错的；开映射定理和指数放大圆盘给出无穷多个精确反例，对每个实底数 $b>\eta$ 都成立 | **严格已证**，不依赖数值根 |
| § fatou | 在 4 个复底数上，K^W 与 fatou.gp 吻合到 40 位（1+i 为 25 位） | **数值**。⚠ 只说明两种实现一致，**不**检验跨边界延拓 |
| § bndtest | 边界点 b_c ≈ 1.5217+0.0148i；六个两侧底数、五个非整数高度上的四次留一插值误差为 4.3e-13~1.7e-12，最邻近两点的 50/70 位结果相差 <5e-50 | **数值**，只检验 `fatou.gp` 逐底数点值构造的边界相容性；未识别为 Paulsen 的底数延拓族，未证 (P2) |
| § brjuno | 两个径向引理、下方排斥图卡的路径运输及割开单位圆盘上的整体全纯族、Prop lower-monodromy、Prop upper-orbit、Cor entry-depth、Prop basin-inradius、Prop siegel-pullback、Prop no-basin-collar、Cor no-uniform-sewing、Lemma root-normal + 修正后的 Prop brjuno 与 Prop hardy-reduction：跨边界延拓 ⇐ (P0)+(P2)+[(P1) 或 Hardy 范数条件] | **上方归一化轨道与局部图卡的内侧参数运输、Brjuno 边界有限回拉深度、吸引域内半径收缩及固定缝合环带障碍、下方正则超函数的整体参数族、割口必要性、回拉命题、条件性归约已证**；缝合解的 (P0)(P1)(P2) 及 Hardy 替代条件未证 |
| Prop lower-backward-label | 每个非尖点边界的下方排斥正则解 $S_b$ 整且局部单叶、遗漏 $0$，因此可按任意非零整数 $k$ 选简单根并平移成跨边界联合全纯的归一化解 $G_b(0)=1$；其后退值必为 $G_b(-1)=2\pi i k/\log b$，而内侧缝合解恒有 $K_b^W(-1)=0$。事实上任何 $z$ 上整的归一化解都有非零整数标签 | **已证**；单靠函数方程、归一化和边界局部解析性无法识别目标分支。若边界比较域含 $-1$，这些下方整解不可能充当缝合解的边界值 |
| Cor backward-rigidity | 在连通底数域上，若归一化解在 $z=-1,0$ 附近联合全纯，则 $k(b)=(\log b)F_b(-1)/(2\pi i)\in\mathbb Z$ 为常数；$k=0$ 的支不可能保持方程而全纯穿过 $z=-2$ | **已证**；内侧缝合支及从 $b>\eta$ 运来的实归一化 Kneser 支均有 $k=0$。因此 $z=-1$ 的值及所有底数导数也是 (P2) 的无判别力节点 |
| Prop backward-log-monodromy | 若 $F_b(-1)=0$ 且该零点简单，则向 $z=-2$ 的局部后退分支必为 $[\operatorname{Log}(z+2)+\log u_b(z+2)+2\pi i k]/\log b$；绕 $-2$ 一圈的增量是 $2\pi i/\log b$，完整穿孔圆盘上不存在单值全纯或亚纯后退支 | **已证**；实轴 $1<b<\eta$ 的内侧缝合解在 $z=-1$ 确有单零点，且在每个实底数附近的参数圆盘上保持此性质。此绕行型对所有同样有单零点的支都成立，不能单独判定 (P2)，也未解决 (P0) |

p 是 MRR 展开参数：p = \|log λ\|·log λ₂ = ε²(1 − ε/3 + …)，其中 ε = \|log λ\|。

**$B_1\ne0$ 的原始文献核验（2026-09-28）**：[Chéritat 2022](https://amj.math.stonybrook.edu/pdf-Springer-final/020-0172.pdf) 的 Definition 8 定义单花瓣单奇异值类 $S_\infty$；Theorem 9 与 Corollary 11 断言其上下抛物重整化仍属于同类，因此在原点恰有一个吸引花瓣。Lemma 87 将即时吸引域内限制映射的奇异值约束于原映射的奇异值。对 $e^u-1$，沿吸引域内负实射线趋于 $-\infty$ 的渐近值是 $-1$，且没有临界点；所以论文 Proposition horn-nonzero 所用的定理链与原文相符。归一化指数投影的二次系数为 $2\pi i B_1$；一花瓣迫使它非零。

---

## 3. 关键数值（复核用）

- \|B₁\| = 0.089058436412213331563，\|B₂\| = 0.012487384111564700811
- B₂/B₁² = −0.02532049309975755123 + 1.5742190652319516267 i
- B₃/B₁³ = −2.254799124523803111 − 0.024408714296883171 i
- a = Φ_att(1/e − 1) = 3.0292972144180360989
- 迭代留数 ρ = 0.249455254258832 − 0.004029881638351 i，且 κ₂^∞ = 2πi(½ − ρ)
- κ⁽¹⁾ = −0.010199006345897402441 − 0.01325095618250671225 i，故缺陷常数 C = −Re κ⁽¹⁾ = 0.0101990063
- C_η = 4π²/√(2e^{1−1/e}) = 20.3508008…，Λ = exp(−C_η/√(η−b)·(1+o(1)))
- Paulsen Prop 2 的小位移数值例子：c = 2 + slog_e(ln 2π + iπ/2) ≈ 3.00431248259469 + 0.70941354086940 i。投稿版的严格反例改用开映射定理构造足够大的整数 $k$：在 Kneser 解的值域中找到 $w=\log(2\pi k)+i\pi/2$，于是 $K(c-1)=2\pi i k$、$K(c)=1$。数值小位移不参与证明。

---

## 4. 代码与数据地图（都在 `docs/`）

### 转移映射与缝合（核心）
- `transition_map.py`：实底数下的转移映射 T = R⁻¹∘S，其 Fourier 模 t_n、不变量 τ_n。
- `eta_approach.py`、`eta_sweep.py`：用闸门线取样，把计算推到 η 附近（η−b = 3e-5）。输出在 `data/eta-sweep.txt`。
- `weld_solve.py`：实底数下 Wiener 代数中的压缩（W2），直接求缝合解。
- `weld_complex.py`：**复底数**下的缝合求解器，并与 fatou.gp 对照。用法：`python3 docs/weld_complex.py "1.2+0.1j" 40 64 0`，参数依次是底数、精度（dps）、采样数 N、缝高；环境变量 `KREF=re,im` 用来传参考值。不给缝高时只扫描全纯带。
- `confluence_check.py`：逐点检验汇流命题 (C)。

### 抛物数据
- `parabolic_horn.py`、`parabolic_horn_inverse.py`：计算 horn map 及其逆的系数 A_n、B_n。
- `certify_horn_witness.py`、`horn-witness-certificate-zh.md`：严格认证逆 horn 位移函数在一个点非零；首模非零的解析证明见投稿版 Proposition horn-nonzero。

### 缺陷律与一阶项
- `deficit_param.py`、`deficit_modes.py`、`deficit_series.py`：以 p 为变量拟合 κ⁽ⁿ⁾。
- `mrr_derivative.py`、`mrr_second.py`：一阶与二阶系数的抛物点级数（主定理 D / Theorem E 的数值实现）。输出在 `data/mrr-*.txt`。

### 梯子（Kneser 型解沿 b+iy 逼近实轴）
- `c1_invariant.py`、`first_mode_check.py`、`kappa_ladder.py`、`theta_spectrum.py`。数据在 `_generated/separation/out5,out6`（未入 git）。

### 外部参考
- `_generated/fatou/fatou.gp` 是早期研究机上的历史路径，**当前工作树未包含**。原版来自 [gp-tetration 仓库](https://github.com/Lightrunnerwastaken/gp-tetration) 的 `src/fatou_backend/vendor/fatou.gp`，sha256 70559dafad8630543b09a2f0843e9e8e041c6b4968ae3546bfe549ced3adfdba。
- `_generated/fatou/run_*.gp`、`bnd_*.gp` 也是历史路径，**当前工作树未包含**；新的边界数据以仓库内下条脚本和 JSON 为准。
- `boundary_multiheight.py`、`data/boundary-multiheight.json`：在五个非整数高度重做边界两侧六底数比较；脚本校验原版 `fatou.gp` 的 SHA-256，记录 50 位原始值、最邻近两点的 70 位复算和插值诊断。运行：`python3 docs/boundary_multiheight.py --fatou /path/to/fatou.gp`。这是有限样本，不能代替 (P2)。
- 跑法：`gp -q run_xxx.gp`，精度 \p 40 下每个底数约 1–10 分钟。本机已装 PARI/GP 2.17.4。
- 文献 PDF：`_generated/mrr-lit/`（MRR、Christopher–Rousseau 等）。Paulsen 2019 全文在 `/Volumes/vaca/cp/download/tetration3 - Copy.pdf`。
- Paulsen 2026 后续论文：[Analyzing the function z↑↑a for fractional a](https://doi.org/10.1007/s10444-026-10300-z)，*Advances in Computational Mathematics* 52, article 25（2026-04-01）。[作者数据仓库](https://github.com/wpaulsen1/tetration/)含两个底数圆周、多个非整数高度的 100 位数值。已核对出版页摘要与数据说明；全文当前未取得，不能据摘要断言它证明了本项目 (P0)–(P2)，也不能把有限圆周数据当作参数局部一致界。

### 编译
- 论文用 `tectonic main.tex` 编译（本机没有 pdflatex）。第一次运行会下载字体，需要几分钟，看起来像卡住，其实不是。

---

## 5. 下一步要做什么（按优先级）

### 5.1 闭合最后的缺口：跨 Shell–Thron 边界的解析延拓（最重要，属研究级）

投稿版 §"Reduction of the continuation to Brjuno boundary points" 给出如下条件性归约。必须先证明两侧分支在共同的开 $z$ 域 $W$ 上到达某段边界弧，然后验证边界有界性和极限：

- **(P0) 分支延伸与识别**：证明从 $b>\eta$ 出发的 Paulsen 分支在连通外侧参数走廊上联合全纯，并到达边界邻域；同时证明靠近实区间 $(b_1,\eta)$ 的缝合解 $K^W$ 在连通内侧参数走廊上联合全纯地延伸到同一邻域。两个走廊都需有共同正则 $z$ 域 $W$。Prop weld-parameter 构造了整段实区间 $(1,\eta)$ 的局部底数圆盘，Theorem W1 另在 $(b_1,\eta)$ 给出定量 Wiener 界；它们**没有**到达任意选定的 Shell–Thron 边界弧。Paulsen Prop 3 与 §5 也没有给出所需的外侧走廊证明。
  - **整段实区间的内侧解析族（Prop weld-parameter，2026-09-28）**：固定任意 $b_0\in(1,\eta)$，$S_{b_0}([0,1])$ 紧含于吸引域且避开不动点，使 $T_b=R_b^{-1}\circ S_b$ 在参数与窄缝线环带上联合全纯。沿实轴 $T'_{b_0}>0$，故加厚后的缝合映射在足够窄的环带上单叶。缝合两张圆柱图卡并补上两端，得到全纯的三标记紧化球面族；Fischer–Grauert 局部平凡化和三点 Möbius 归一化给出 $K_b^W(0)=1$ 的联合全纯族。相邻圆盘由实底数切片唯一性粘合。这只给出**非定量的实轴开邻域**；没有证明内侧族到达 Shell–Thron 边界，也没有识别 Paulsen 族。
  - **整段实射线的外侧解析族（Prop exterior-real-parameter，2026-09-29）**：对 $b_0>\eta$，取最近实轴的一对共轭不动点 $L_\pm=u\pm iv$，令 $r=e^{u\log b}$、$\theta=v\log b\in(0,\pi)$。竖直弦 $u+ivt$ 的指数像是圆弧 $r e^{i\theta t}$，且 $|E_b'(L_\pm)|=\theta/\sin\theta>1$。弦与弧的区域按 $E_b$ 粘合，Koenigs 坐标补上两端，三标记球面族给出参数全纯的 Abel 坐标。实轴上 $E_b(x)>x$，动力图卡有限链覆盖 $1$ 到 $b$；反射性与对数步长 $+1$ 保证该坐标在正实轴严格递增。[Trappmann–Kouznetsov 2011](https://mizugadro.mydns.jp/PAPERS/2011uniabel.pdf) 的初始区域唯一性准则把它识别为经典 Kneser 支；证明在区域内任选 $d$ 作准则的标记，再沿实动力图卡移到 $w=1$，避免原文 Theorem 5 中“$d=1\in H$”对近尖点底数并不总成立的问题。每个紧实底数子区间有共同的复底数邻域和共同的 $[0,1]$ 复高度邻域。这个结果只建立**实射线附近**的局部走廊，不提供到非尖点边界弧的宽度控制。
  - **近尖点外侧初始曲线的几何走廊（Prop exterior-curve-collar，2026-09-29）**：用 $\theta=p+iq$ 参数化最近实轴的不动点对，$r=e^{\theta\cot\theta}$、$a=\theta e^{-\theta\cot\theta}/\sin\theta$、$b=e^a$。弦与其指数像的交点条件化为 $s_\theta(t)=(e^{i\theta t}-\cos\theta)/(i\sin\theta)\in\mathbb R$；统一展开给出 $\operatorname{Im}s_\theta(t)=-(1-t^2)(p/2+O(|\theta|^2))<0$，因此在 $|q|\le Mp$ 的小锥内两弧不相交。上方乘子中性曲线为 $q_c(p)=p^2/6+O(p^3)$；在 $0\le q<q_c(p)$ 内两端仍排斥，无标记商曲面能沿真正的复底数楔形一直逼近该非尖点边界弧。这**排除了初始曲线提前自交这一几何障碍**，但没有构造 $w=1$ 的全路径标记或共同正则高度域；也没有得到边界一致的 Koenigs 尾估计。
  - **一条带标记的外侧路径（Prop exterior-marked-path，2026-09-29）**：用 `python3 docs/certify_exterior_mark.py` 可复现 Arb/Acb 外向舍入证书（python-flint 0.9.0 / FLINT 3.6.0；1000 个有理参数小段，80 位十进制精度）。沿 $\theta=1/10+iq$、$0\le q<q_c<1667/10^6$，上方乘子模方从 $>1$ 严格递减穿到 $<1$，下方乘子模方始终 $>1.003$；底数像的虚部导数 $>0.05$，所以路径不自交。对每个参数，$E_b^{28}(1)$ 经弦坐标变换后落在 $-0.01<\Re\zeta<0.04$、$-0.03<\Im\zeta<-0.01$，而对应圆弧在这段横坐标上低于 $-0.0396$、弦在虚部 $0$；因此该迭代点严格位于初始区域内，连同终点 $q=q_c$ 都有余量。它在外侧给出 $w=1$ 的全纯标记和**高度 $z=0$ 的归一化芽沿具体路径的解析运输**。证书不保证整段 $z\in[0,1]$ 的共同正则邻域、边界全纯极限或对一整段边界弧的运输，所以 (P0)–(P2) 仍未闭合。
    **已完成的外侧完整高度走廊**：`docs/certify_brjuno_exterior_mark.py` 认证指定 Brjuno 点 $\lambda_c=e^{2\pi i(\sqrt2-1)/26}$、其附近短边界弧上的第 28 次轨道落点和奇异轨道避让；逐次解析对数给出含 $w=1$ 的 Jordan 回拉域及缝边界等变式。`docs/certify_exterior_flat_cylinder.py` 证明整个商圆柱 $|\mu|<1/10$；Ahlfors–Bers 参数定理与宽盒证书给出跨非尖点边界的外侧归一化芽的联合全纯性。`docs/certify_exterior_frozen_abel.py` 在 $|\Im\theta|\le0.01$ 上严格验证 $|P-i|<0.18$、$\Im c>0.98$、$\|P_Y\|_\infty<0.004$、$\|F_{YY}\|_4<0.00025$。周期 Beurling 收缩、竖直差商和显式 Morrey 不等式进一步给 $|\partial_Y(h-h^0)|<0.041$，故精确缝线高度导数 $>0.93$，包括中性弧两侧。Prop exterior-single-crossing 的唯一横截条件遂成立，Cor exterior-full-height 给出边界附近共同连通 $W\supset[0,1]$ 的外侧联合全纯族。**这只完成 (P0) 的外侧完整高度子步骤**；内侧缝合支到同一弧的运输及分支识别仍未证明。
    **下一步的具体目标**：外侧的有限高度切触问题已由 Prop exterior-seam-monotonicity 在中性弧两侧的宽盒中排除，不再需要为它制作有限元网格。Cor exterior-wide-full-height 已把**同一个**完整高度外侧支沿宽盒送到严格内侧点 $\theta_0$；Prop interior-chord-overlap 认证外侧弦的非平凡子弧进入上方吸引域；Prop interior-sewing-circle 则在**同一点**独立认证下方正则曲线的完整缝合圆并构造局部内侧缝合族。这形成了两个可比较的局部全纯族，但**尚未证明它们相等**。原拟沿 $\theta=p+0.01i$、$0\le p\le0.1000435842$ 逐段保持下方正则圆为嵌入正斜率缝线；Prop interior-path-crossing 已在其中一个严格内侧参数认证真实横截自交与负实斜率，故**这条具体缝线运输方案不可行**。下一步应寻找避开自交位形的参数绕路，或建立允许更换缝线的抽象商曲面运输，再于 $\theta_0$ 比较两种统一化坐标或给出分离见证。现有 Prop weld-parameter 只给每个实 $1<b<\eta$ 附近的局部内侧族；边界 Brjuno 点上固定吸引域图卡会塌缩，故不能把局部 Koenigs 图卡界直接当作完整缝合解的参数界。Cor exterior-boundary-zero 已给外侧边界支在 $z=-1$ 的单零点和 $-2$ 对数绕行型，可排除非零后退标签的伪支；Cor exterior-boundary-normal 又给外侧边界小弧上的统一根隔离及 (P1) 外侧局部界。这些结果都不能单独识别 $K^W$。
    **新增的两条回归圆与两端芽**：Prop interior-quotient-loop 把 $S_{\theta_0}([0,1])$ 经 76/77 次前向像，严格放入外侧 Jordan 单胞并跨其胶合边一次，得到外侧商圆柱内的嵌入本质圆。Cor interior-two-returns 又用 14/15 次像构造一条不相交的回归圆；同一物理圆有不同的回归代表，不能把某次回归默认为规范商映射。Cor interior-end-germs 将下方 Poincaré、上方吸引正则解与外侧商球面的对应穿孔端逐一核对，均为一次局部芽。对于任何选定的回归圆，尚需证的图卡延伸位于该圆至上下穿孔端之间的**两段紧中间带**，或找到阻止延伸的具体单值/分支障碍；环形重叠加两端局部相容仍不能推出两张紧化球面的统一化坐标相等。
  - **实尖点不能作为直接穿越路径（Cor cusp-real-obstruction / Prop cusp-no-puiseux）**：Cor imaginary-profile 的首阶轮廓在某个固定非整数实高度 $x_*$ 非零，因此 $|\operatorname{Im}K_b^W(x_*)|\ge c\Lambda(b)$ 对全部充分靠近 $\eta$ 的 $b<\eta$ 成立。任何在 $b=\eta$ 附近单值全纯、并在 $b>\eta$ 的实底数上于实高度取实值的族，由 Schwarz 反射仍须在 $b<\eta$ 取实值，故不可能在那里等于缝合支。更强地，对每个充分小的非零实高度 $x$，$K^W_{\eta-t^q}(x)$ 对任意有限整数 $q\ge1$ 均无穿过 $t=0$ 的亚纯延拓：它与自身共轭反射的差非零，却沿 $t>0$ 比所有 $t$ 幂都小，无法是非零 Laurent 芽。若一对共轭绕行路径的解析延拓都存在，且一条给出缝合支，另一条必须给出其共轭支，固定 $x_*$ 处的支差至少为 $2c\Lambda$；这里并未证明两条路径存在。(P0) 若成立，其目标路径必须绕开这一实尖点；这不排除穿过非尖点边界弧。
  - **下方解析族不是目标缝合分支（Prop lower-backward-label）**：Lemma lower-chart 已保证 $S_b$ 在非尖点边界两侧局部联合全纯。它的导数处处非零并遗漏 $0$；Picard 定理于是保证对每个 $k\in\mathbb Z\setminus\{0\}$ 都有简单根 $c$ 使 $S_b(c)=1$ 且 $S_b(c-1)=2\pi i k/\log b$。隐函数定理把平移解 $G_b(z)=S_b(z+c(b))$ 全纯延过边界，整数 $k$ 沿参数支不变。实轴缝合解及其局部底数延拓却满足 $K_b^W(-1)=0$。故函数方程、$F(0)=1$ 与参数全纯性自身**不足以**选出所需的 (P0) 分支；若共同高度域包含 $-1$，下方整解甚至可由该后退值直接排除。此结论没有排除目标缝合解以其他机制延过边界。
  - **目标缝合支的首个后退奇性（Prop backward-log-monodromy）**：由上方正则解在 $z=0$ 的导数非零、缝合参数化局部共形及函数方程，可证每个实 $b\in(1,\eta)$ 的 $K_b^W$ 在 $z=-1$ 有单零点，邻近复底数仍然如此。因此由 $K_b^W(-1+t)=t u_b(t)$ 向 $z=-2+t$ 后退时必出现 $[\operatorname{Log}t+\log u_b(t)]/\log b$，绕行增量 $2\pi i/\log b$。这加强了 Cor backward-rigidity 的“不能全纯穿过 $-2$”为“不能在完整穿孔圆盘上单值亚纯”，并给出目标支的局部绕行型；仍未把它运到非尖点 Shell–Thron 边界。
  - **W1 局部统一性的补充（2026-09-28）**：$T_b(z)-z$ 为 1 周期函数，因此只需在闭高度带的 $0\le\Re z\le1$ 基本矩形上用紧性选出同一个参数圆盘，再以周期性覆盖无界的整条带。W2 原先选取 $D$ 的不等式足以吸收复参数扰动造成的 $M\mapsto2M$：压缩常数至多 $2\rho=1/2$，故 W1 可保持同一个 $D$ 与声明的带宽 $H-1/2$。两版论文已补全这些细节。此论证对每个实 $b_0\in(b_1,\eta)$ 给出某个局部圆盘，**没有**提供沿路径到达边界所需的半径下界。
  - **已闭合的下方图卡子步骤（Prop lower-transport / Cor global-lower）**：$g(\mu)=\mu e^{-\mu}$ 在闭单位圆盘单叶，因此对 $0<|\lambda|\le1$ 的已知不动点，其他不动点乘子都在 $|\mu|>1$。从实 $0<\lambda_0<1$ 的下方排斥乘子出发，沿任意有限长、避开 $0,1$ 的内侧乘子路径到非尖点边界 $\lambda_c$，由 $d\mu/d\lambda=((1-\lambda)/\lambda)\mu/(1-\mu)$ 的有界性排除有限路径上的逃逸；极限乘子仍排斥且简单。在割开圆盘 $\Omega=\mathbb D\setminus(-1,0]$ 上，单连通性消除路径单值性问题，得到从实支出发的整体全纯乘子 $\mu_2(\lambda)$、全纯 $\log\mu_2$，以及 $(\lambda,z)$ 联合全纯、对 $z$ 整的下方正则超函数 $S_\lambda$；它在非尖点边界（避开割口端点）局部延伸。上方吸引 Koenigs **局部**图卡在 $0<|\lambda|<1$ 也无共振，可随参数解析变化；剩余难点是两张图卡的重叠域及缝合曲线是否能沿路径保持。绕过 $0$ 的其他路径仍可能改变下方分支。**这未证明缝合修正或 $K^W$ 到达边界，更未证明 Paulsen 外侧族。**
  - **割口不可省略（Prop lower-monodromy）**：$\lambda\mapsto b=\exp(\lambda e^{-\lambda})$ 在单位圆盘单叶，$\lambda=0$ 对应 $b=1$。下方乘子与正则超函数可在穿孔圆盘的**通用覆盖**上整体全纯定义。沿小圆 $\lambda=\varepsilon e^{it}$ 绕 $0$ 共 $n$ 圈时，下方乘子始终满足 $|\mu|>1$；其终值满足 $\mu-\operatorname{Log}\mu=-\log\varepsilon+\varepsilon-2\pi i n$，此处 $\operatorname{Re}\mu>0$，故使用同一主值对数。不同 $n$ 的终值必不同；下方不动点与正则超函数也有无限阶绕行单值性障碍。因此不能在整个穿孔内侧底数域上定义同一支；(P0) 的参数走廊必须固定同伦类或使用割口。这是路径选择的真实限制，**不等于证明跨 Shell–Thron 边界的缝合延拓不可能**。
  - **上方归一化轨道已全域运输，有限落点例外集为空（Prop upper-orbit）**：利用指数映射“吸引不动点的直接吸引域含唯一有限奇异值 $0$”的定理（[Schleicher 2003, §2](https://www.math.stonybrook.edu/preprints/ims00-04.pdf)），在 $0<|\lambda|<1$ 的整个内侧乘子域证明 $E_b^{\circ n}(1)\to L_1=e^\lambda$，且对参数局部一致。把归一化 Koenigs 坐标沿该轨道回拉，得到 $c(\lambda)=\sigma_\lambda(1)$ 在穿孔圆盘全纯、$\sigma_\lambda'(1)\ne0$。若 $c=0$，奇异轨道有限步落到吸引不动点；但[Laubner–Schleicher–Vicol 2008, Thm. 3.1](https://doi.org/10.3934/dcds.2008.22.663) 保证每个有限奇异轨道的指数映射有一条由逃逸点组成的动力射线落到奇异值 $0$，与 $0$ 位于开吸引域矛盾，故 **$c(\lambda)$ 在整个穿孔圆盘无零点**。在 $\lambda=0$ 附近直接对 Koenigs 极限作一致估计，还得到 $c(\lambda)=-\lambda-\lambda^2/2+O(\lambda^3)$；因而 $c$ 在圆盘内仅有一个简单零点，$-c/\lambda$ 有全域归一化全纯对数，$c$ 绕 $0$ 的指标恰为 $1$。于是沿任意避开 $0$ 的紧内侧参数路径，上方正则超函数可在高度 $z=0$ 的共同小圆盘上联合全纯运输，且在更小的共同圆盘上对 $R_\lambda=1$ 有统一根隔离，并有 $R_\lambda,1/R_\lambda$ 的统一界。绕 $b=1$ 一圈时 $\log\lambda$ 增加 $2\pi i$，从而 $R_\lambda'(0)$ 改变 $2\pi i c(\lambda)/\sigma_\lambda'(1)$；上方归一化图卡也有无限阶绕行单值性障碍。仍没有保持到边界弧的统一半径，也没有运输两图卡的缝合修正。

  - **Brjuno 边界的归一化轨道回拉深度必发散（Cor entry-depth）**：[Rempe 2008, 引言中 Theorem 2 后的说明](https://doi.org/10.1515/CRELLE.2008.081) 指出指数映射一旦有 Siegel 盘，其唯一奇异值就在 Julia 集。这里 $w=0$ 是奇异值，故 $w=1=E_b(0)$ 及其每个有限前向迭代也在 Julia 集，不能位于边界的上方 Siegel 图卡中。由 Lemma radial-chart 的两侧一致收敛可严格推出：对任意固定回拉深度 $N$ 和固定小图卡半径 $s$，当 $\lambda=r\lambda_c\to\lambda_c$ 时，$E_{b(r)}^{\circ N}(1)$ 最终在图卡外；内侧轨道首次进入该图卡的步数 $m_s(r)\to\infty$。这排除了“固定有限步回拉上方图卡来延拓归一化解芽”的路线，**不排除缝合解通过其他机制跨边界延拓**。
  - **Brjuno 边界的吸引域内半径收缩（Prop basin-inradius）**：由上一条 $1\in J(E_{b_c})$；[Bergweiler 1993, Thm. 4](https://arxiv.org/pdf/math/9310226) 给出排斥周期点在 Julia 集稠密。取任意靠近 $1$ 的边界排斥周期点，隐函数定理将其延续到附近内侧参数；它始终在吸引域外。因此 $\operatorname{dist}(1,\mathbb C\setminus\mathcal A_\lambda)\to0$，其中 $\mathcal A_\lambda$ 是上不动点的直接吸引域。进一步还得 $\operatorname{dist}^{\mathrm{hyp}}_{\mathcal A_\lambda}(1,b(\lambda))\to\infty$：若该距离沿某序列有界，直接吸引域的单位圆盘通用覆盖可把 $1$ 和 $b(\lambda)$ 的原像放在固定紧圆盘内，与下面的图卡塌缩结论矛盾。为证明图卡塌缩，另选一个与 $1$ 保持正距离的边界排斥周期点，并延续为吸引域外的 $q_j$；任取靠近 $1$ 的吸引域外点 $p_j$。若固定连通高度域 $V\ni0$ 上的全纯映射 $G_j:V\to\mathcal A_{\lambda_j}$ 满足 $G_j(0)=1$，则 $(G_j-p_j)/(q_j-p_j)$ 遗漏 $0,1$ 且在原点趋零；Montel 与 Hurwitz 定理迫使 $G_j\to1$ 局部一致，**无须预设局部有界**。因此若 $1\in V$，则充分靠近边界时不存在同时满足 $G(0)=1$、$G(1)=b(\lambda)$ 且全域取值于 $\mathcal A_\lambda$ 的映射。这严格限制了 (P0)/(P1) 可采用的**固定高度、吸引域取值**的上方图卡。若归一化解确能在这样的固定连通高度域上存在，其高度像必与直接吸引域的边界（Julia 集的一部分）相交。目标缝合支能否到达这种固定域仍未证明；通过其他图卡延拓仍有可能。

  - **局部有界周期修正也不能保持固定缝合环带（Prop no-basin-collar）**：令 $\mathcal A_\lambda^{\rm all}$ 为上不动点的完整吸引域。对任意固定非空连通开集 $V\subset\mathbb C$ 且 $V+1=V$，以及任意内侧序列 $\lambda_j\to\lambda_c$，不存在局部一致有界的全纯 1 周期修正 $Q_j$，使 $S_{\lambda_j}(z+Q_j(z))\in\mathcal A_{\lambda_j}^{\rm all}$ 对全部 $z\in V$ 成立。证明：取极限 $Q_j\to Q$ 后，$\phi=z+Q$ 非常数，其像 $W=\phi(V)$ 开、连通且 $W+1=W$。若 $S_{\lambda_c}(W)$ 碰到 Julia 集，其开像包含排斥周期点；Rouché 定理使附近参数的同类周期点也落入吸引域，矛盾。故该像处于不变 Fatou 分量；由[指数映射 Fatou 分量分类](https://arxiv.org/pdf/math/0309107)只能是最大 Siegel 盘，而 Prop siegel-pullback(2) 排除完整周期域 $W$。取 $Q_j=0$ 即得先前的固定下方环带障碍。此结论不再要求有限步进入 Siegel 小图卡，但仍要求修正局部有界、同一个高度域与内侧吸引域取值；目标缝合解的延拓性未因此判定。

- **(P1) 局部一致有界性**：在 Shell–Thron 边界某段弧 Γ 两侧的邻域里，κ_b(z)（外侧，Paulsen 族）与 K^W_b(z)（内侧）对 $z\in W$ 的每个紧子集局部一致有界。
  - **较弱的 $H^1$ 范数替代条件（Prop hardy-reduction，2026-09-28 降至端点）**：对弧的局部拉直坐标 $s+it$、任意紧子弧 $I$ 及紧高度集 $V\Subset W$，只需两侧 $\sup_{0<|t|<\epsilon}\int_I\sup_{z\in V}|F_\pm(s+it,z)|\,ds<\infty$。局部 $H^1$ 定理给出 $L^1$ 边界迹；这些迹作为 $L^1(I)$ 值函数对 $z$ 全纯，故 (P2) 在有域内聚点的 $D$ 上成立便使两侧边界迹在整个 $W$ 上相等。分布意义的 $\bar\partial$ 拼接及 Weyl 引理随后给出联合全纯延拓。这**严格弱于逐点一致上界**，允许边界附近在参数方向有局部峰值；所需 $H^1$ 范数估计本身仍未证明，也不能由目前的有限数值采样推得。
    在仅使用“边界值几乎处处相等”的抽象拼接论证里，指数 $1$ 是门槛：$F_\pm(\xi,z)=1+z/\xi$ 对每个 $0<p<1$ 都有局部一致的水平 $L^p$ 界，且两侧边界值几乎处处相等、$F_\pm(\xi,0)=1$，但在 $\xi=0$ 有极点。该反例没有利用四则迭代方程，因此不排除用方程额外结构研究更弱的条件。
  - 难点：Γ 上有稠密的 Cremer 参数，要证明在它们附近解不会爆掉。
  - **新增充分条件（Lemma root-normal）**：若两族解在固定圆盘 $B(0,R)$ 及其左移 $B(-1,R)$ 上都有定义，且在 $B(0,R)$ 中 $F(z)=1$ 的唯一原像是 $z=0$，则函数方程使 $F$ 在圆盘内不取零。取归一化全纯对数 $g=\log F$ 后，$h=1/2+g/(4\pi i)$ 避开 $0,1$ 且 $h(0)=1/2$；Schottky 定理同时给出 $g,F,1/F$ 在所有较小圆盘上的局部一致界，即 (P1)。若 $F(-1)=0$，则 $g(z)=(\log b)F(z-1)$，所以在 $|\log b|$ 有正下界时左移圆盘上也有一致界；Cauchy 估计还给出 $|F'(0)|\le C/R$。反过来，若 $d_F$ 是最近的额外原像 $F(z)=1$ 到原点的距离，则 $|F'(0)|\min(R,d_F)\le C$：固定圆盘上的导数发散必迫使额外原像向原点碰撞，但导数有界并不能证明根隔离。这把 (P1) 的一种证明路线转成“归一化根在边界附近统一隔离”的几何问题；该根隔离目前未证。
  - **尖点附近的已证情形（Cor sewn-cusp-local）**：Theorem C 的吸引 Abel 坐标汇流在 $w=1$ 附近给出局部逆函数 $R_b\to F_\eta^{\mathrm{att}}$；W2 的周期修正 $P_b\to0$，故 $K_b^W\to F_\eta^{\mathrm{att}}$ 在固定复高度圆盘上局部一致收敛。极限在 $z=0$ 的导数非零，Rouché 定理给出固定小圆盘内的根隔离及 $K_b^W,1/K_b^W$ 一致界。这是 **实轴 $b\to\eta^-$、内侧缝合分支** 的结果；不能外推到任意 Brjuno 边界弧或 Paulsen 外侧分支。
  - **连通复底数尖点走廊（Cor cusp-corridor）**：利用 W1 在每个实底数处的联合全纯性，把小圆盘 $U_x$ 取成 $|b-x|<(\eta-x)/4$ 且 $\|K_b^W-K_x^W\|_{\overline{B(0,r)}}<\min(m,\eta-x)$；这些圆盘的并 $N_\eta$ 连通。上一条的实轴极限遂推广为 $b\to\eta$ 且 $b\in N_\eta$ 时的局部一致极限，并在整片 $N_\eta$ 上给出同一高度圆盘的根隔离与函数、倒数的统一界。**这没有量化走廊宽度**，因此不能用它声称已靠近某段非尖点 Shell–Thron 边界，更不等于 (P0) 或 (P1) 的完整证明。
    在连通的参数走廊内，若函数族在闭圆盘 $\overline{B(0,R)}$ 的邻域有定义，从某个已知基底出发（圆盘内仅有一个简单根 $z=0$），并严格排除整个走廊的固定圆周 $|z|=R$ 上出现 $F_b(z)=1$，辐角原理就会保持根数为 1，从而得到上述隔离。Cor sewn-cusp-local 已为**内侧缝合分支**在靠近实尖点的基底提供这种起点与固定圆盘。待证的是沿连续参数走廊直到 Γ 的内侧圆周排除；外侧在已构造的非尖点小弧附近由 Cor exterior-boundary-normal 获得统一根隔离。有限基底采样不足以证明内侧隔离。
  - 可能思路：用缝合构造中 P、Q 的一致界，配合转移映射 T 的模估计；或者用极值长度（模）方法，从缝合面的几何直接给出界。
  - **原文核查**：Paulsen 2019 Prop 3 首先把 Kneser 共形统一化随实底数的实解析性当作显然事实，未单独给出参数依赖证明；现已由 Prop exterior-real-parameter 用初始区域的参数全纯粘合补上**实轴局部**证明。该文继而把实底数上的不动点竖直极限搬到复底数路径；Cor exterior-uniform-tails 已补上实射线**局部**的参数一致尾项，但沿复底数路径直到边界的统一尾项估计仍缺。§5 又从每个有限 Kouznetsov 求积近似随 $b$ 连续，直接推出极限跨边界连续，缺少关于 $b$ 的局部一致收敛估计。故不能把该文的解析延拓结论当成现成定理使用。投稿版的 Paulsen 评注和 §bndtest 已明确指出这些缺口。
  - **可替代的严格近似判据（Prop approx-continuation）**：设一条连通复底数走廊 $\Omega$ 同时碰到实区间 $(\eta,\infty)$ 和目标内侧开集，$W$ 是共同的连通正则高度域，$D\subset W$ 在域内有聚点。若有限近似 $A_N$ 在 $\Omega\times W$ 联合全纯且对 $N$ 局部一致有界，并在每个实底数 $b\in\Omega\cap(\eta,\infty)$、每个 $z\in D$ 收敛到经典 Kneser 值，则二变量 Montel 加两次恒等定理使**整个序列**在 $\Omega\times W$ 局部一致收敛为联合全纯族。若同一序列还在内侧某个非空开集的 $D$ 上收敛到 $K^W$，便直接完成分支识别。有限次求积在固定对数／反图卡分支且归一化分母非零的参数小片上局部全纯；但对**所有**求积阶数和迭代次数共同适用、并跨过目标边界弧的分支安全走廊，以及参数局部一致上界，均**未证明**。算法的逐点收敛或连续性不能代替。明确的反例是 $a_N(b)=\exp[-N-N^3(b-b_0)^2]$：每个实 $b$ 上趋零，却在任意固定 $b_0+iy$（$y\ne0$）发散。这个判据把 Paulsen 论证欠缺的估计表述为可审核的任务，但尚未建立 (P0)。
  - **两端的整数分支标签（Lemma end-spectrum）**：令 $\varepsilon=+1$ 或 $-1$ 指上／下端，选 $0<\varepsilon\operatorname{Im}\ell<2\pi$，并假设 $F(x+\varepsilon iy)\to L$ 对 $0\le x\le1$ 一致。则局部 Koenigs 坐标严格写成 $\sigma(F(z))=e^{\ell z}q^m h(q)$，其中 $q=e^{\varepsilon2\pi iz}$、$m\ge0$、$h(0)\ne0$。证明把 $e^{-\ell z}\sigma(F(z))$ 降到穿孔 $q$ 圆盘，利用竖直极限排除负 Laurent 模。“Abel 时间 $z+$有界周期修正”恰对应 $m=0$。这不只是形式上的可能：对任一排斥不动点，整 Poincaré 函数 $P$ 给出每个 $m\ge0$ 的精确整函数解 $F_m(z)=P(c e^{(\ell+\varepsilon2\pi im)z})$，它们均满足同一**单侧**极限；不必满足 $F(0)=1$ 或另一端极限，所以不是对 Paulsen 全部假设的反例。若已有共同高半带上的联合全纯参数族，常数模 $a_0(b)$ 全纯；从非零种子出发，$m=0$ 局部保持，走廊上的零点至多离散。Cor exterior-end-labels 已证明**经典外侧支两端都是 $m=0$ 且首系数非零**，提供了这个种子；Cor exterior-uniform-tails 更在每个紧实底数子区间的共同上下半带给出参数一致的指数收敛。把这些界运到非尖点边界所需的复参数走廊、半带和统一常数仍未建立，(P0) 未闭合。两端标签是分支识别所需的附加数据。
  - **另一篇预印本的适用范围**：[Vey 2025，Theorem 7](https://www.researchgate.net/publication/391941916_Holomorphic_Extension_of_Tetration_to_Complex_Bases_and_Heights_via_Schroder's_Equation) 声称用 $F(z)=\psi^{-1}(s^z\psi(1))$ 得到所有复高度上的唯一解。但其 Step 1 只证明 $\psi^{-1}$ 在 $0$ 附近局部存在，没有证明 $s^z\psi(1)$ 对所有 $z\in\mathbb C$ 留在这张逆图卡；Step 2 用正整数处的吻合调用恒等定理，而正整数在复平面内无聚点。周期性时间扰动 $F(z+\epsilon(e^{2\pi iz}-1))$ 已给出同一整数值的局部反例。因此该证明不能用来填补本文 (P0) 的跨底数解析延拓或唯一性缺口；这里评议的是所列论证，不是断言该预印本的所有其他结果皆错。

- **(P2) Brjuno 点两侧极限相等**：取 $W$ 内一个有域内聚点的可数集合 $D$；对 $D$ 中每个 $z$，在几乎处处 Brjuno 边界点，两侧径向极限存在且相等（非 Brjuno 点测度为零）。(P1) 的局部一致界配合 Montel 正规族和恒等定理，会把这结论扩展到整个 $W$。
  - 已证的局部步骤：以 $v=(\log b)(w-L)$ 换元，指数映射在上不动点附近**精确**化为 $f_\lambda(v)=\lambda(e^v-1)$。Lemma radial 配合 [Marmi–Carminati 2008](https://doi.org/10.24033/bsmf.2565) 的乘子圆锥一致估计，给出 Brjuno 点两侧上图卡在固定小圆盘内向 Siegel 图卡收敛。Lemma boundary-repelling 利用 $g(\mu)=\mu e^{-\mu}$ 在闭单位圆盘上的单叶性，证明整个 $0<|\lambda|\le1$ 区域里其他不动点的乘子都满足 $|\mu|>1$；Prop lower-transport 将选定下方不动点从实轴沿内侧路径运到非尖点边界；Lemma lower-chart 随后用逆迭代的正规收敛，证明下方 Koenigs 图卡连同整个排斥正则超函数 $S_b(z)$ 在 $(b,z)$ 上局部联合全纯，且两侧向边界收敛。这补齐了原来“下图卡一致双曲”的未证断言，但没有运输完整的缝合解。
  - 还要证：
    1. **原先设想的边界缝合带不存在。** 取固定的小 Siegel 盘 $\mathcal D_\rho$，令 $\Omega_\rho=\{z\in\mathbb C:\exists n\in\mathbb Z_{\ge0},\ S(z+n)\in\mathcal D_\rho\}$。Prop siegel-pullback 证明了 $\Omega_\rho$ 非空（回拉坐标确有零点）、其回拉坐标单值全纯，且在每个紧子集上从边界两侧径向收敛；但它还证明 $\Omega_\rho$ 不含任何完整水平带，甚至不含平移 $z\mapsto z+1$ 不变的连通缝线。关键是小 Siegel 盘在所有有限前像的并中仍是独立的连通分支；一条完整缝线若在前像并内，平移后必与 Siegel 盘相交，便只能全部落在盘内，而 $S(z-n)\to L_2$ 排除了后者。最大 Siegel 盘亦然。
       进一步地，$S_{b_c}$ 的确有 $S_{b_c}(z)=1$ 的根（Picard 定理），但这些归一化根全在 $\Omega_\rho$ 外：$1$ 的每次前向迭代都在 Julia 集，永远进不了 Siegel 图卡。Prop siegel-pullback 所说的“回拉坐标有零点”对应的是 $S_{b_c}(z)=L_1$，不能误当作解族归一化点 $S_{b_c}(z)=1$。
       新增 Cor no-uniform-sewing 将此写成参数逼近的紧性障碍：在固定完整水平带上，周期性下方时间修正若局部一致有界，就不可能在每个紧集上以一致有限步数、留出固定图卡半径余量进入上方 Siegel 图卡。因此不能用这类统一回拉估计来证明 (P1) 或 (P2)；这不排除直接控制完整解函数的其他方法。
    2. 因此不能沿用“局部图卡收敛 + 固定边界转移映射的 Carathéodory 核收敛”来证明 (P2)。需寻找不要求边界存在完整 Siegel 缝合带的方法，直接控制两侧缝合解或底数参数上的极限；该步骤仍完全未证。
  - 数值上：在 α = (√2−1)/5 的边界点，现已对 $z\in\{1/6,1/3,1/2,2/3,5/6\}$ 的两侧六个底数重算 `fatou.gp` 的**逐底数点值构造**；四次留一插值误差不超过 $1.7\cdot10^{-12}$，两侧各自二次外推到边界的差为 $2.9\cdot10^{-9}$ 至 $7.1\cdot10^{-9}$，邻近两点的 50/70 位复算差小于 $5\cdot10^{-50}$（§bndtest 与 `data/boundary-multiheight.json`）。这仍只是有限高度、单个边界点、有限距离的点值相容性证据；没有证明这些点值属于 Paulsen 的底数解析延拓族，尤其五个高度没有域内聚点，不能满足 (P2)。Siegel 级数加有限前向回拉只能检验局部图卡，不能在整条缝线上计算边界转移映射。后续实验应使用趋于域内点的非整数序列，并检查其他 Brjuno 边界点、参数接近方向和精度稳定性。
  - **范围限制**：回拉图卡的局部收敛不能推出缝合解极限，且完整 Siegel 缝合带已被严格排除。投稿版 Prop chart-boundary 还证明：局部图卡 $H_\lambda$ 不能作为 $(\lambda,v)$ 的联合全纯函数跨过单位圆上任何有理旋转点；否则 $f_\lambda^{\circ q}$ 将在某个单位根参数处恒等于恒等映射，与指数函数的周期性矛盾。有理旋转点稠密，所以不能通过逐个图卡的全纯延拓解决跨边界问题；最终缝合解中仍可能发生抵消。Marmi–Carminati 给出的 monogenic 正则性与此相符。§bndtest 的有限采样只与光滑拼接相容，不能排除更小的跳跃或高阶非解析项。

有了 (P0)(P1)(P2)，由 Prop brjuno（Fatou 定理 + H^∞ 版 Painlevé 粘合 + 恒等定理），就得到 κ = K^W 在开集上成立，主定理 C 变成无条件的，整条链闭合。

**勘误（2026-09-28）**：旧版 Prop brjuno 的 (P1) 只要求某个 $z_0$ 处有界，(P2) 也只在该点比较；这不足以推出解族的解析延拓。特别是 $z_0=0$ 满足旧条件，而两种解在此恒等于 1。旧版还默认两侧分支都已到达边界邻域，现将这一步单列为 (P0)。两版论文已把 (P1) 改为开 $z$ 域上的一致有界条件；(P2) 只需在有域内聚点的可数集上验证，并由 Montel–Hartogs 补足整个解族的联合全纯性论证。边界点 $K(1/2)$ 的数值比较仍只是在一个点上的证据，不能单独验证修正后的 (P2)。

**检验点选择**：任意非负整数高度 $n$ 上，两族解只要满足同一归一化和函数方程，就自动等于 $E_b^{\circ n}(1)$；它们在这些点的全部底数导数也自动相同。若两族仍位于 $k=0$ 的后退支，Cor backward-rigidity 还说明 $z=-1$ 的值及全部底数导数也自动为零。Cor conjugate-sewn-jump 更给出实际的两条局部解析解：它们共享这些整数值、零标签及 $-2$ 的对数绕行型，但在固定非整数实高度相差至少 $2c\Lambda$。连所有整数高度的有限阶 $z$ 导数都不足以区分一般解：$F_\epsilon(z)=F(z+\epsilon(e^{2\pi iz}-1)^{m+1})$ 与 $F$ 在这些点有同阶喷流，且仍满足函数方程，却通常在非整数高度不同；该扰动不一定保留缝高类。因此整数高度的吻合对 (P2) 没有判别力。应选 $W$ 内趋于域内一点的非整数序列，例如当 $0$ 有邻域包含于 $W$ 时取 $z_j=1/j$（$j\ge2$），并同时检查参数接近方向与精度稳定性。

**追加勘误（2026-09-28）**：`docs/base-analyticity-zh.md` 早期把 Paulsen 2019 §5 的跨边界全纯说成已证明的定理，现已撤回该判定。有限精度的非零差值也不能代替解析延拓证明。应以本节 (P0)–(P2) 的状态为准。

投稿版的摘要、引言与数值节也已统一记号：无条件定理研究的是缝合解 $K^W$；Paulsen 的底数延拓族及其边界值仍属条件性对象。`fatou.gp` 和本仓库的梯子程序只作逐底数构造，不能据此声称已实现底数上的解析延拓。先前稿中“未能读到 Paulsen 2019 原文”的陈述已删除；原文现已核查。

**建议**：这一步最好找 Siegel 盘 / 小分母方向的专家合作（Yoccoz 学派、Buff–Chéritat、Pérez-Marco 一系）。可参考的文献方向：Yoccoz 关于 Brjuno 条件最优性的证明（用到线性化域共形半径作为参数的有界全纯函数及其径向极限，思路与 (P2) 同构）；Buff–Chéritat 关于 Siegel 盘大小连续性的工作。

### 5.2 与 Paulsen 的往来（已进行，待跟进）

- 2026-09-26：我们去信索要 Paulsen 2019 全文，并询问唯一性条件。
- 2026-09-28：他回信并附全文。当天我们回信（Gmail 原线程，纯文本），内容三点：
  1. 指出 Prop 2 的反例，并说明缝高条件如何修补；
  2. 询问第 5 节跨边界延拓有没有严格证明、他是否认为这仍是开放问题；
  3. 表示愿意合作，并提出可以寄预印本和代码。
- **待办**：等他回复。若后续通信，应澄清：40 位吻合只检验两种逐底数实现一致；§bndtest 的六底数、五高度数据也只说明 `fatou.gp` 点值在所测尺度上与平滑接合相容，**不能说“两侧解析拼接已检验到 $10^{-13}$”**，更不能识别这些点值为 Paulsen 的底数延拓族。没有新的授权时不要代作者发信。
- 发送任何邮件都必须先得到李光浩本人明确同意。

### 5.3 投稿前的收尾

1. **找人类专家审读**。证明经过多轮 AI 对抗审稿，但还没有人类同行审过。重点请人看三处：Lemma band 的轨道估计、刻画定理 (ii) 中缝合曲面的 Hausdorff 性与落点论证、主定理 D/E 的一致模型构造。
2. **选期刊**。候选：Nonlinearity、Ergodic Theory and Dynamical Systems，或 Advances in Computational Mathematics（Paulsen 发文的期刊）。选定后换成对应模板。
3. **公开代码**。整理 `docs/` 中相关脚本，公开到 GitHub 或 Zenodo，把论文 "Code and data availability" 一节改成链接。
4. **致谢措辞**。论文目前写了"证明经过 AI 辅助的对抗性审稿"。是否保留由作者决定；多数期刊要求披露 AI 使用。
5. **挂 arXiv**。属于公开发布，必须由作者本人操作，或者明确授权后才能代办。

### 5.4 可选的加强

- **首模解析非零性已解决（2026-09-28）**：Chéritat, *Near Parabolic Renormalization for Unicritical Holomorphic Maps*, Arnold Math. J. 8 (2022), Def. 8、Thm. 9、Cor. 11、Lemma 87（[DOI](https://doi.org/10.1007/s40598-020-00172-6)）。对 $f(u)=e^u-1$，负实轴属于即刻抛物吸引盆 $A$；$f$ 的唯一有限奇异值 $-1$ 是沿此轴的渐近值，且 $f$ 无临界点。Lemma 87 排除 $f|_A$ 产生别的奇异值，故 $f\in S_\infty$。Cor. 11 使其上方抛物重整化仍属于 $S_\infty$，仅有一个吸引花瓣；上方重整化正是逆 horn map 的指数投影（差一个非零线性缩放），其二次系数为 $2\pi iB_1$，因此 $B_1\ne0$。两版论文已加 Proposition horn-nonzero；**十进制下界仍未认证**。
- **一点严格数值证书**：`docs/certify_horn_witness.py` 用 FLINT/Arb 区间和有理解析尾项界，证明在 $u=11i/20$ 有 $\operatorname{Im}\Phi_{\rm rep}>3.095$，$\operatorname{Re}(\Phi_{\rm att}-\Phi_{\rm rep})>3\cdot10^{-10}$，每条尾项小于 $4.075\cdot10^{-31}$；推导见 `docs/horn-witness-certificate-zh.md`。这独立证明 horn 位移不恒为零，但**单独并不隔离首模**；首模非零采用上条解析证明。
- **待做的数值认证**：给 $|B_1|$、B₂、a 及 fatou 对照值严格包络。仓库里已有 `certify_theta_*` 一套区间工具可以借用，但它们目前没有认证抛物 horn 系数。先前“一点 + 一条线”的 Cauchy 判别法仍可用于给出 $|B_1|$ 的显式正下界；当前一点已严格认证，整条 $\operatorname{Im}z=1$ 上的定义域与统一界未认证。
- **κ⁽¹⁾ 的闭式**：PSLQ 没有找到简单闭式。可以从 Gevrey 性和复苏（resurgence）结构方向研究。
- **小位移反例的数值证书（非必需）**：Remark paulsen 已有不依赖数值的严格反例；若想保留上表的具体小位移近似，可另用区间算术认证该特定根。

---

## 6. 踩过的坑（务必读）

1. **复底数必须用精确十进制解析。** Python 的 `complex("1.2+0.1j")` 会把 1.2 圆成双精度，与精确十进制算出的不动点不一致（E(L) − L ≈ 6e-15），把所有复底数对照卡在 1e-16~1e-20。正确做法：用 `kneser._bases.base_value(normalize_base(...))`，再用 Newton 迭代抛光不动点。
2. **S(z) 的回拉步数。** 当 log λ₂ 是复数时，m 要满足 (Re(z·log λ₂) − log r)/Re(log λ₂)；写成 Re((z log λ₂ − log r)/log λ₂) 是错的。
3. **移动缝线时只平移 S 时间的输入**，R 时间的输出不能动。否则根的选择全错。
4. **fatou.gp 不做真正的解析延拓。** 它在每个底数上独立构造两侧 θ-映射解。与它吻合只说明实现一致，不能当作延拓的证据。
5. **缝高条件是必要的，不是技术性假设。** 平移根 c_j 给出的解同样有两侧表示，但 \|c₁\| ≍ Λ^{1+j}；b=1.3 处的数值是 log\|c₁\|/log Λ = 1.0585 / 2.0585 / 3.0585。
6. **R（吸引点的 Poincaré 函数）不是整函数。** K^W 在 R 表示区里有割线副本 (−∞,−2] + ikh（k ≥ 1）；S 才是整函数。
7. **缺陷律必须用 MRR 参数 p。** 用 ε 或 η−b 做有限区间拟合，会得出假的指数（1.74、2）和假的常数（0.01013）。
8. **Paulsen 2019 的 Prop 2 不能直接引用。** 它的唯一性是错的，引用前先看 Remark paulsen。Paulsen–Cowgill 2017（实底数 b > η）不受影响。
9. **tectonic 首次编译会下载字体**，要等几分钟，不是卡死。
10. **Gmail 自动化**：点正文框要按坐标点，按元素 ref 点击常常拿不到焦点，字符会落到页面上，"?" 还会触发快捷键帮助。先输入一小段测试，确认进了正文再输入全文。发送前逐段核对，**必须先得到用户明确同意**。
11. **实底数的虚高度极限不能沿用复底数断言。** 当 $b\in(1,\eta)$ 为实数时，上下两张正则时间图卡的乘子对数均为实数；固定实部后，图卡在虚高度方向呈周期行为，一般不收敛到两个不动点。W1 所用 $\operatorname{Im}z\to\pm\infty$ 极限只在有符号虚部的非实底数邻域成立。因此不能用“两个不同实极限 + Schwarz 反射”来证明实底数上的 $K_b^W$ 不取实值。现已有 Cor sewn-nonreal 的正确证明：由 $c_1\ne0$ 与上方时间修正的单边 Fourier 谱推出，在 $z=0$ 附近任意实区间存在非实值；它只适用于已构造的内侧缝合族。

---

## 7. 仓库状态提醒

**2026-09-29 补充**：`docs/paulsen-global-qc-transport-zh.md` 给出一条新的无条件结果：从一个尖点月牙域出发，利用乘子坐标上的显式 Beltrami 系数，在整个上半 ST 区域构造归一化、随底数全纯的拟共形共轭，并把月牙商面及标记高度芽搬运到每个内点。关键系数满足 \(|(\Log q-\Log q_0)/(\Log q+\overline{\Log q_0})|<1\)。这仍**没有**证明搬运族与稿件的尖点族作为参数芽相同；缺的是相邻月牙域的保标记轨道比较引理。不要据此把 Paulsen 与 \(K^W\) 的全域识别改写成无条件定理。

截至本文档写成时，以下工作**尚未提交到 git**：
- `docs/paper-submission/`（整个目录）
- 新脚本：`transition_map.py`、`eta_*.py`、`weld_*.py`、`confluence_check.py`、`deficit_*.py`、`mrr_*.py`
- 数据：`data/eta-sweep.txt`、`data/mrr-*.txt`
- `docs/mrr-first-order-zh.md`，以及本交接文档
- `docs/paper-separation/` 的修改

最近一次提交是 `e732ef0`。建议接手后先由作者确认，再统一提交。注意：`formal/` 和 `_generated/` 按惯例不入 git。

---

## 8. 如果你只有一小时

1. 读投稿版 PDF 的引言（主定理 A–D）和 "Open problems" 一节。
2. 读本文 §5.1，理解 (P0)(P1)(P2) 及新增的两个下图卡引理。
3. 跑一遍 `python3 docs/transition_map.py 1.3 40`，再跑 `python3 docs/eta_approach.py 0.9 1.5`，确认环境正常、能复现关键数值。
4. 查看 Gmail 里 Paulsen 线程有没有新回复。
