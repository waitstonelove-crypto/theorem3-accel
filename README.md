# Theorem 3：加速度级推广的 Lean 4 形式化证明

把 Li, Zhang & Jin (2017, TNNLS) *Kinematic Control of Redundant Manipulators Using Neural
Networks* 的速度级控制律推广到**加速度级**（论文结论声明的 future work），并用 Lean 4
（v4.32.2 + Mathlib v4.32.2）机器验证。配套数值仿真见
[puma560-reproduction](https://github.com/waitstonelove-crypto/puma560-reproduction)
的 `exp5_accel/`（四组实验：定常调节 / 圆轨迹跟踪 / 非凸 Ω_a / 噪声鲁棒性）。

## 文件

| 文件 | 内容 |
|------|------|
| `Core.lean` | 最小基础设施：欧氏内积/范数（eNorm）、vecDiv、右伪逆 rpinv（JJ†=I）、投影平移不等式（任意集，无需凸性）、Lyapunov 导数机器、`eNorm_coord_le`、`abs_inner_le_half_add` |
| `Theorem3.lean` | 控制律、闭环恒等式、衰减界、主定理 theorem3、估计器、比较引理真证明、离流形界、时变估计器不等式 |
| `lakefile.toml` | 标准 lake 项目，`path = "../../mathlib"` 引用共享 Mathlib |
| `build.sh` | 直调 lean.exe 构建（复用共享 Mathlib 编译产物） |

## 构建

```
lake build          # 标准方式（需先有共享 Mathlib：D:\AI\lean\mathlib 含 .lake 编译产物）
# 或
bash build.sh       # 直调 lean.exe（LEAN_PATH 指向共享 Mathlib）
```

## 定理 3 陈述

控制输入 `a = θ̈ ∈ Ω_a`（关节加速度约束，**允许非凸**），运动学 `r̈ = Jθ̈ + J̇θ̇`。

```
s  = ė + αe                         （降阶辅助变量，α > 0）
q  = r̈_d − J̇θ̇ − (α+β)ė − αβe       （参考加速度，PD 反馈嵌入，β > 0）
a  = P_Ωa(−ε⁻¹Jᵀs + J⁺q)，ε > 0     （控制律，J⁺q = rpinv J hJ *ᵥ q）
ζẇ = q − JJᵀw                       （估计器，不动点 Jᵀw* = J⁺q，无需矩阵求逆）
```

**定理 3（`theorem3`）**：若 `rank(J) = m`（JJᵀ 可逆）、可行性 `J⁺q(t) ∈ Ω_a` 逐点成立、
`α, β, ε > 0`，则闭环满足：

```
ṡ = J[P_Ωa(z) − J⁺q] − βs，  z = −ε⁻¹Jᵀs + J⁺q
V̇₂ = −ε⟨z−y, P_Ωa(z)−y⟩ − β‖s‖² ≤ −2βV₂，  V₂ = ‖s‖²/2
```

⟹ `s → 0`（指数率 β），进而由 `s = ė + αe` 得 `e = r − r_d → 0`。

**保留性质**：Ω_a 非凸仍允许（投影平移不等式仅需 `y ∈ Ω_a`）；无积分器（噪声下误差
不累积）；`J̇θ̇` 运动学耦合补偿；无需 `y ∈ int(Ω)`（衰减直接来自 `−β‖s‖²` 项）。

## 验证的引理链（Theorem3.lean）

1. `V2_accel_algebra` — 伴随代数：`⟨s, J(P(z)−y)⟩ = −ε⟨z−y, P(z)−y⟩`
2. `V2_accel_decay` — `⟨s, J(P(z)−y)⟩ ≤ −(ε/2)‖P(z)−y‖²`（投影平移不等式）
3. `q_algebra` — 参考加速度代数：`q + J̇θ̇ − r̈_d + αė = −β(ė + αe)`
4. `closed_loop_identity` — 闭环恒等式（关键：`JJ⁺ = I` ⟹ `J·(J⁺q) = q`）
5. `V2_s_decay` — `⟨s, J(P(z)−y) − βs⟩ ≤ −β‖s‖²`
6. `comp_lemma_convergence` — **比较引理真证明**（Gronwall，非 axiom）：
   W(t)=e^{ct}·V(t)，W' ≤ 0 ⟹ 反单调 ⟹ V(t) ≤ V(0)e^{−ct} ⟹ 收敛
7. `theorem3` — 组装：`s → 0` ∧ `e → 0`
8. `estimator_frozen_q` — 冻结 q：`ζẇ = q₀ − JJᵀw` ⟹ `JJᵀw(t) → q₀`（指数）
9. `V2_off_manifold` — 离流形交叉项界：`V̇₂ ≤ −β‖s‖² + (ε/2)‖Jᵀw−J⁺q‖²`
   （2xy ≤ x²+y² 技巧，无需 Cauchy–Schwarz）
10. `estimator_V1_diff_ineq` — 时变 q：`V̇₁ ≤ −(2c/ζ−1)·½‖x‖² + ½L²`（‖q̇‖≤L）

## Axiom 清单（1 个，其余全部机器验证）

| axiom | 内容 | 说明 |
|-------|------|------|
| `lin_ode_input_convergence` | `ė = −αe + s`（α > 0）且 `s → 0` ⟹ `e → 0` | 卷积解需 Fubini/积分理论，暂 axiom 化 |

`comp_lemma_convergence`（原 axiom）已真证；`exp_convergence` 已由它推导。零 sorry。

## 数值验证（exp5_accel，PUMA 560，MATLAB）

| 实验 | 结果 |
|------|------|
| 定常调节 | 稳态 ‖e‖ = 2.9e-15 m，关节静止 |
| 圆轨迹跟踪 | 加速度级 RMS = 0.0130 m vs 速度级 Eq.41 = 0.0131 m |
| 非凸 Ω_a | RMS = 0.0131 m，a ∈ Ω_a 全程 100% |
| 噪声（σ=0.01 m） | 稳态 RMS = 0.0012 m，有界不累积 |

## 备注（未形式化）

- 估计器时变 q 的实用收敛结论（代数层不等式已证，收敛结论未形式化）
- 零空间关节漂移抑制（任务空间结论不受影响）
- `lin_ode_input_convergence` 的卷积解
