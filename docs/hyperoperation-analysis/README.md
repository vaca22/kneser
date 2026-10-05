# 超运算分析学

**修订版：2026-10-05，v0.8。** 中文 Markdown 书本与研究工程。初版日期为 2026-10-04。

超运算分析学研究超运算及其连续延伸在**底数、迭代高度、运算层级**三个方向上的结构。我们以这个名字建立自己的研究纲领、教材、问题库与复现流程；它的学术地位由后续成果和研究共同体形成。

从 [完整书稿](BOOK.md) 开始阅读。分章源文件在 [chapters](chapters/00-preface.md)，研究证明在 [research](research/001-rational-time-identifiability.md)。

## 已完成的书稿与研究

- 序言、十二章正文、术语与文献附录；各章包含定义、例子、推导或证明、研究问题与练习。
- 研究 R001：周期时间变换、有限有理时刻的不可辨识性、一个无理时刻的整体刚性，以及函数值接近但生成元不接近的构造。
- 研究 R002：超函数随下层映射变化的一阶响应，归约为差分方程；给出保持两个端点的仿射模型及数值验证。
- 研究 R003：有限 Fourier 带宽下的定量刚性、最优 `L²` 常数，以及无理时间近共振下的生成元不稳定性。
- 研究 R004：复层级的周期重参数化、有限数据盲区、闭一形式与可交换方向、生成元和二阶响应，以及两个全局障碍。
- 研究 R005：指定渐近规范下的响应存在唯一性、稳定性与截断界，显式共振/临界项，以及实际固定端点的局部非线性超函数族。
- 研究 R006：真实指数在底数 `1.3` 附近的联合全纯参数族、统一 Koenigs 收敛界、主对数延拓域、实高度范围、虚周期与真实源项的响应选解。
- 研究 R007：固定底数1.3、实层级3至5的实际光滑族，完整跨层后继，平坦接合的解析障碍、全纯接合的无限 Taylor 条件，以及负一高度共同截面的不相容性。
- 研究 R008：开放 Banach 函数空间上的实际 Fréchet 全纯后继、单射紧线性化、显式近盲方向及指定空间的局部复时间流障碍。
- 研究 R009：有界复层级的整数唯一性、无限 Pick 存在判据、条件式联合全纯与自动后继，以及真实锚点的精确复域范数障碍。
- 研究 R010：无界半平面值的条件式全局层级、Cayley 自动后继、零高度局部延拓、共同复域的周期/折角障碍，以及真实高层复高度失败诊断。
- [全局构造审计](GLOBAL-CONSTRUCTION.md)：区分高度迭代与层级连续化，给出目标域、实际完成状态和八项验收条件。
- 修正 Julia 协变的飞行时间陈述，补上正尺度归一化、连通区间假设及 Schröder–Abel 对数分支相容条件。
- 独立脚本、实验 JSON、结果报告、命题登记表与下一步验收条件。

R001–R010 提供有明确假设的完整推导。其机制来自经典 Abel 方程、周期自由度、线性化、Fourier 方法、Pick 插值与复分析；**尚未完成优先权检索，不能据此宣称世界首次发现**。R007 给出实际光滑实层级有限带，R008 建立开放空间的真实后继并排除一种流嵌入路线，R009–R010 给出圆盘/半平面自映射类的无限构造判据，并探查真实复高度的有限失败。真实阶梯尚未验证这些无限条件；全纯连续复层级的全局构造仍未完成，文档验证通过不等于该存在性问题已解决。

## 阅读路线

| 路线 | 章节 |
|---|---|
| 入门 | 1 → 2 → 3 → 4 |
| 层级研究 | 5 → 7 → 8 → 9 |
| 本轮研究 | 4 → 10 → 11，随后读 R001/R002 |
| 持续推进 | 12 → [研究台账](research/README.md) → [命题登记表](CLAIMS.md) |
| 复层级与全局边界 | 2 → 9 → [R004](research/004-complex-rank-geometry.md) → [全局审计](GLOBAL-CONSTRUCTION.md) |
| 响应的存在与实际变形 | 5 → 11.8 → [R005](research/005-boundary-selected-response.md) |
| 真实复底数与虚周期 | 6.5 → 11.9 → [R006](research/006-exponential-parameter-family.md) |
| 实际实层级与解析接缝 | 9.6 → 11.10 → [R007](research/007-rank-bands-and-seams.md) |
| 开放函数空间与流障碍 | 5.5 → 9.7 → 11.11 → [R008](research/008-analytic-successor-and-compactness.md) |
| 有界复层级与自动后继 | 9.8 → 11.12 → [R009](research/009-bounded-rank-interpolation.md) |
| 半平面值与共同复域的风险 | 9.9 → 11.13 → [R010](research/010-halfplane-rank-and-domain-probes.md) |

## 复现

在仓库根目录运行；脚本也支持从任意目录用绝对路径执行。

```sh
python3 docs/hyperoperation-analysis/experiments/rational_time.py
python3 docs/hyperoperation-analysis/experiments/linear_response.py
python3 docs/hyperoperation-analysis/experiments/quantitative_rigidity.py
python3 docs/hyperoperation-analysis/experiments/complex_rank_geometry.py
python3 docs/hyperoperation-analysis/experiments/boundary_selected_response.py
python3 docs/hyperoperation-analysis/experiments/exponential_parameter_family.py
python3 docs/hyperoperation-analysis/experiments/rank_bands_and_seams.py
python3 docs/hyperoperation-analysis/experiments/analytic_successor_compactness.py
python3 docs/hyperoperation-analysis/experiments/bounded_rank_pick.py
python3 docs/hyperoperation-analysis/experiments/rank_domain_probe.py
python3 docs/hyperoperation-analysis/build_book.py
python3 docs/hyperoperation-analysis/check_book.py
```

十个实验入口需要 `mpmath`；部分实验通过绝对路径加载本仓库 `src/kneser` 或既有阶梯脚本。R005 有有限求和模块，R006 有指数参数族与坐标尾界，R007 有实际实层级带模块，R008 有真实方向导数模块，R009 有有限 Pick/Schur 插值及精确有理两点证书，R010 检验实际复高度与两种自映射类。本书不修改计算库和既有研究文档。JSON 记录精度、参数、误差与输入哈希；普通浮点实验不是区间证书，R010 的有理证书仅认证记录的小数矩阵。运行 `experiments/plot_rank_domain.py` 可用 matplotlib 重建 [复域图](figures/rank-domain.png)。

## 编辑约定

修改分章源文件后运行 `build_book.py`。`BOOK.md` 为生成的单文件版；构建器调整相对链接并保持公式原文。更新结果必须同时更新研究台账和命题状态。已有研究中的复杂证明在本书中只作为带来源的材料，未在本轮独立复核的结论标为 `[仓]`。
