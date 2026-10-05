# 超运算有没有工业应用

2026-10-02。文献核对笔记。本文不声称新定理，也不声称复现了任何产线系统。

> 四级及以上的超运算，作为产线上要计算的一种新算术，没有工业落地。
> 和它同一个函数方程的「分数次迭代」有过一次真实的工业尝试：
> 已知整条产线，反推其中一架相同的机器。

前三级已经是工业基础设施，不必再论证。加法、乘法、乘方对应计数、比例和增长；整数指令、浮点和对数尺都建在这三级上。下面只讨论第零级、第四级，以及再往上的整数阶与连续阶。

---

## 1. 整数高阶：记号和压测

整数高度的幂塔长得比工业量快。本仓库里底数 \(e\) 的五级运算，高度 2 已经是

\[
e\uparrow\uparrow\uparrow 2 = 2075.968\ldots
\]

再高一个整数高度就是以这个数为高度的幂塔。传感器、账本和控制回路都不在这个数量级上。数值见 [超运算阶梯纲领](hyperoperation-program-zh.md) §3.2。

文献里对得上号的用途，都停在「把巨大的数写短」或「压测递归」：

- Ackermann 函数从 Sundblad（BIT，1971）起被用来考察编译器会不会把深层递归优化掉。它是基准程序，不是产品功能。
- Rubtsov 等人（IOP Conf. Ser.: Mater. Sci. Eng. **994** 012040，2020）提出用超对数做「超格式」编码超大数，并把零级运算 zeration 写成绝对值、符号函数和布尔运算的算术公式。布尔运算和条件分支已经在指令集里。这篇是工程会议论文，没有后续的数值标准或芯片采用这种格式。
- Furuya–Kida（Algorithms **12** 159，2019）用幂塔分解 Church 数词，证明 λ 项大小可以压到 \(O((\mathrm{slog}_2 n)\log n/\log\log n)\)，并在 \(n\lesssim 10^4\) 上与二进制表示做了比较。作者自己把它接到高阶压缩（重复模式编成 Church 数词）上。这是 λ 演算里的紧凑编码实验，整数幂塔在这里是分解工具。

零级运算同样是记号。zeration 把 `max`、符号和条件分支重写成一种优先级低于加法的运算，表达力没有超出已有的布尔代数。Rubtsov 文末建议把它放进微处理器基本指令集，这是提议。

## 2. 常被引成「应用」的四篇

Hooshmand 式连续幂塔的综述 arXiv:2105.00247 把下面四篇列为 tetration 的应用。核对原文题目和摘要之后，它们各自是：

| 文献 | 原文在做什么 |
|---|---|
| Scott–Mann–Martínez，AAECC 2006 | 把 Lambert \(W\) 推广到广义相对论与量子力学里的某类方程。无穷幂塔与 \(W\) 有公式关系，这篇算的是推广后的 \(W\)。 |
| Sun–Wandelt–Linke，Proc. ICE Transport 2017（在线 2016） | 空中导航航线网的拓扑。综述称其中用到「连接度」；原文不是一套在调度系统里求幂塔的程序。 |
| Khetkeeree–Chansamorn，ITC-CSCC 2019 | 用二阶 tetration 多项式做信号重建，和最近邻、线性、三次插值比 PSNR。这是一种插值核的会议实验。 |
| Furuya–Kida 2019 | 见上一节：Church 数词的紧凑表示。 |

这四篇都没有在产线、器件或数值标准里调用 Kneser 幂塔或五级运算。

## 3. 一次真实的工业尝试：轧钢中间板形

能进工厂的是更一般的问题。已知整步映射 \(T\)，求 \(T^{1/n}\)，使复合 \(n\) 次回到 \(T\)。

Lars Kindermann 的博士论文把热轧带钢写成这个模型。一条轧线有多架相同机架，入口和出口板形能测，机架之间测不到。整线是 \(T\)，单架是 \(T\) 的迭代根。实现是权值共享的神经网络（加上一个迭代的线性模型），不是解析半指数。

学位论文著录了一项西门子专利：WO 99/42232（1999），*Process and device for determining an intermediate section of a metal strip*，发明人 Kindermann、Protzel、Schmid、Gramckow。论文正文的原话是：此项方法已获专利，当时处于工业试验（*industrielle Erprobung*）。他后来的英文方法笔记写成「已由一家大公司获得专利，并已用于工业生产」。

本笔记核对到的是学位论文里的专利著录和这两句状态描述，没有独立核实该专利在 2026 年仍装在哪条轧线上。

Kouznetsov 提出过另一条物理对应：光纤中的量随长度变化，可以写成指数映射的分数次迭代。这是建模提议，没有对应的器件标准。

## 4. 同一函数方程已经以别的名字在跑

工业里稳定在用的，是这个思想的线性版本和数据驱动版本。

- **转移矩阵的根。** 年度信用迁移、设备状态、客户生命周期要拆成半年或一季，就是求 Markov 矩阵 \(A\) 使 \(A^2=P\)。根可能不存在、不唯一，或出现负元，不能解释成概率。
- **矩阵对数与分数次幂。** 旋转插到一半角度、滤波做半强度、扩散做半个时间单位，线性时就是 \(T^t=\exp(t\log T)\)。动画和图形学里的中间帧属于这一类。
- **离散动力系统嵌进连续流。** 过程仿真和粗采样时间序列的加密采样。线性自回归看谱：特征值要允许实的分数次幂。非线性情形没有通用闭式，Kindermann 用网络近似。
- **Koopman 线性化与动态模态分解。** 「把迭代变成线性算子的作用」已经是数据驱动建模的日常工具。它和 Abel / Schröder / Carleman 坐标是同一条路，对象是可测的有限维状态。参见 [无限方程组](essay-infinite-systems-zh.md) 里对 Koopman / DMD 的定位。

这四条有测量、有业务解释，而且通常有不动点或谱分解，所以根选得出来。

更宽的一份「半步」清单（Markov 嵌入、动画中间帧、滤波的半强度、以及存在性 / 唯一性 / 稳定性四条障碍）写在 [分数次迭代和半迭代有没有实际工业应用？](../references/kneser1950/fractional-iteration-applications-zh.md)。那篇的对象是一般的 \(T^{1/2}\)，不是幂塔。

## 5. 和本仓库对象的距离

Kneser 半指数 \(\vartheta(\vartheta(x))=e^x\)，以及五级上两个候选解的差，是这个函数方程最难的标准样例：实轴上没有不动点，增长极快，实解析不够唯一，典范解要靠复解析规范。

五级、底数 \(e\)、高度 \(1/2\) 上，本仓库已经把两个解分开（[纲领](hyperoperation-program-zh.md) §4.5）：

```
正则 / Koenigs    1.63232474043606…
Kneser 型         1.63235385715702…
D(1/2)            2.9117e-5
```

同一份测量还给出构造本身的失效边界：底数低于

\[
b_c = 1.63532449671528
\]

时，五级的 Kneser 型解不存在（§4.10–§4.11）。六级、七级的临界底数又依赖于五级选了哪一个解，非唯一性往上传染。

这三件事就是高阶超运算进不了工业标准的原因，只是换了工业语言：

1. **有的底数上构造不存在。** 标准要先声明定义域。
2. **同一高度上两个解析候选差一个可测的量。** 标准若不固定分支，两个实现会对不上。
3. **值域立刻离开物理量。** 高度 2 已经是两千上下，下一个整数高度是幂塔。

所以可计算的半指数、幂塔和五级运算，证明的是「连续迭代族可以造到这一级，并且不同构造之间的差可以测」。它们不对应一条要调用这些函数的产线。

## 6. 边界

- 第一到第三级是工业算术。
- 第零级和第四级及以上的整数超运算，停留在记号、编码实验和递归压测。Furuya–Kida 的 Church 数词压缩是其中最具体的算法结果，实验范围到大约 \(10^4\)。
- 分数次迭代作为「把离散一步拆成连续时间」有工业价值。已核实的硬件以外的一次尝试是西门子轧钢专利 WO 99/42232；论文当时的用语是工业试验。其余成熟落地发生在矩阵根、算子分数幂和 Koopman 模型里。
- 解析半指数、Kneser 幂塔和五级运算没有对应的工业计算任务。

## 参考文献

- Y. Sundblad, *The Ackermann function. A theoretical, computational, and formula manipulative study*, BIT 11 (1971).
- K. A. Rubtsov, I. S. Konstantinov, S. A. Lazarev, K. A. Polshchykov, V. E. Kiselev, *Application of hyperoperations for engineering practice*, IOP Conf. Ser.: Mater. Sci. Eng. 994 (2020) 012040.
- I. Furuya, T. Kida, *Compaction of Church Numerals*, Algorithms 12 (2019) 159.
- T. C. Scott, R. B. Mann, R. E. Martínez, *General relativity and quantum mechanics: towards a generalization of the Lambert W function*, AAECC 17 (2006) 41–47.
- X. Sun, S. Wandelt, F. Linke, *On the topology of air navigation route systems*, Proc. ICE — Transport 170 (2017) 46–59.
- S. Khetkeeree, C. Chansamorn, *Signal Reconstruction using Second Order Tetration Polynomial*, ITC-CSCC 2019.
- L. Kindermann, *Neuronale Netze zur Berechnung Iterativer Wurzeln und Fraktionaler Iterationen*, 博士论文。专利著录 WO 99/42232（1999）。
- L. Kindermann, *A framework for solving functional equations with neural networks*（英文方法笔记；其中把该轧钢方法写成已用于生产）。
- arXiv:2105.00247，连续高度幂塔的一篇显式公式论文；上文四篇「应用」由其引言列出。
- 本仓库：[hyperoperation-program-zh.md](hyperoperation-program-zh.md)，五级两解之差与临界底数；[fractional-iteration-applications-zh.md](../references/kneser1950/fractional-iteration-applications-zh.md)，一般分数次迭代的工业场景。
