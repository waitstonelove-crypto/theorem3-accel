/-
Copyright (c) 2026 wj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wj
-/
import Core
/-! # Theorem 3：加速度级推广（速度级 → 加速度级，Li-Zhang-Jin 2017 future work）

把 LZJ 定理 2 的速度级控制律推广到加速度级：控制输入 a = θ̈ ∈ Ω_a
（关节加速度约束，允许非凸），并形式化证明跟踪误差 s = ė + αe 与 e = r − r_d
全局收敛（指数）。

## 控制律

- s = ė + αe（降阶辅助变量，α > 0）
- q = r̈_d − J̇θ̇ − (α+β)ė − αβe（参考加速度，PD 反馈嵌入，β > 0）
- a = P_Ωa(−ε⁻¹Jᵀs + J⁺q)，ε > 0（J⁺q = rpinv J hJ *ᵥ q）
- 估计器（实现可选）：ζẇ = q − JJᵀw，不动点 Jᵀw* = J⁺q（避免矩阵求逆）

## 核心结论（theorem3）

运动学 r̈ = Jθ̈ + J̇θ̇ 下，闭环恒等式（closed_loop_identity）：

    ṡ = J[P_Ωa(z) − J⁺q] − βs,   z = −ε⁻¹Jᵀs + J⁺q

V₂ = ‖s‖²/2 的导数（V2_accel_algebra + 投影平移不等式 proj_sq_ineq_at，仅需 y = J⁺q ∈ Ω_a）：

    V̇₂ = −ε⟨z−y, P_Ωa(z)−y⟩ − β‖s‖² ≤ −2βV₂

比较引理（comp_lemma_convergence，**真证明**，非 axiom）⟹ s → 0（指数率 β）；
由 s = ė + αe（稳定线性 ODE ė = −αe + s）⟹ e → 0（lin_ode_input_convergence axiom）。

## Axiom 清单（1 个）

- `lin_ode_input_convergence`：稳定线性 ODE 的输入收敛性（卷积解，需 Fubini/积分理论，暂 axiom 化）
- ~~comp_lemma_convergence~~（已真证：标量比较引理 W' ≤ 0 ⟹ 单调 ⟹ V(t) ≤ V(0)e^{−ct} ⟹ 收敛）
- ~~exp_convergence~~（已由 comp_lemma_convergence 推导）

## 与定理 2 的差异

- 无需 0 ∈ int(Ω) / y ∈ int(Ω)：衰减直接来自 −β‖s‖² 项，投影项仅贡献额外耗散
  （V̇₂ ≤ −(ε/2)‖Pz−y‖² − β‖s‖²），因此可行性只需逐点成员 J⁺q(t) ∈ Ω_a；
- Ω_a 非凸仍允许（投影平移不等式仅需 y ∈ Ω_a）；
- 无积分器（s 是 PD 组合），噪声下误差不累积的性质保留；
- 新增要素：J̇θ̇ 运动学加速度耦合补偿、二阶误差动力学、PD 增益 αβ；
- 估计器时变 q 情形的实用收敛：代数层不等式 estimator_V1_diff_ineq（V̇₁ ≤ −aV₁ + b，
  a = 2c/ζ − 1，b = ½L²），离流形交叉项界 V2_off_manifold（V̇₂ ≤ −β‖s‖² + (ε/2)‖Jᵀw−J⁺q‖²）。
-/

namespace Theorem3

open Matrix Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/-- 伴随代数（定理 3 版）：z = vecDiv(−Jᵀs/ε) + y 时 ⟨s, J(P(z) − y)⟩ = −ε⟨z−y, P(z)−y⟩ -/
theorem V2_accel_algebra {n m : ℕ} (P : Vec n → Vec n) (J : Matrix (Fin m) (Fin n) ℝ)
    (y : Vec n) (ε : ℝ) (hε : 0 < ε) (s : Vec m) :
    inner ℝ s (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y)) =
      -ε * inner ℝ (vecDiv (-((Jᵀ) *ᵥ s)) ε) (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y) := by
  let z : Vec n := vecDiv (-((Jᵀ) *ᵥ s)) ε + y
  have hJTs : (Jᵀ) *ᵥ s = -(ε • (z - y)) := by
    ext i
    have hz : z i - y i = -(Jᵀ *ᵥ s) i / ε := by
      dsimp [z, vecDiv]
      ring
    simp [Pi.smul_apply, hz]
    field_simp [hε.ne']
  have h1 : inner ℝ s (J *ᵥ (P z - y)) = inner ℝ ((Jᵀ) *ᵥ s) (P z - y) := by
    rw [vec_inner_symm s (J *ᵥ (P z - y))]
    rw [vec_mulVec_adjoint J (P z - y) s]
    rw [vec_inner_symm (P z - y) ((Jᵀ) *ᵥ s)]
  calc
    inner ℝ s (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y))
        = inner ℝ s (J *ᵥ (P z - y)) := by rfl
    _ = inner ℝ ((Jᵀ) *ᵥ s) (P z - y) := h1
    _ = -ε * inner ℝ (z - y) (P z - y) := by
      rw [hJTs]
      rw [vec_inner_neg_left, vec_inner_smul_left]
      ring
    _ = -ε * inner ℝ (vecDiv (-((Jᵀ) *ᵥ s)) ε) (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y) := by
      have hzy : z - y = vecDiv (-((Jᵀ) *ᵥ s)) ε := by
        dsimp [z]
        abel
      have hP : P z - y = P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y := by
        dsimp [z]
      rw [hzy, hP]

/-- 衰减界：⟨s, J(P(z) − y)⟩ ≤ −(ε/2)‖P(z) − y‖²（投影平移不等式 + 伴随代数） -/
theorem V2_accel_decay {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (y : Vec n) (hy : y ∈ Ω) (J : Matrix (Fin m) (Fin n) ℝ) (ε : ℝ) (hε : 0 < ε) (s : Vec m) :
    inner ℝ s (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y)) ≤
      -((1 / 2) * ε) * eNorm (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y) ^ 2 := by
  have hineq : eNorm (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y) ^ 2 ≤
      2 * inner ℝ (vecDiv (-((Jᵀ) *ᵥ s)) ε) (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y) := by
    simpa using proj_sq_ineq_at P Ω hPdist y hy (vecDiv (-((Jᵀ) *ᵥ s)) ε + y)
  have hinner := V2_accel_algebra P J y ε hε s
  rw [hinner]
  nlinarith [hineq, hε]

/-- 参考加速度代数：q + J̇θ̇ − r̈_d + αė = −β(ė + αe)，q = r̈_d − J̇θ̇ − (α+β)ė − αβe -/
theorem q_algebra {n m : ℕ} (Jdot : Matrix (Fin m) (Fin n) ℝ) (rdd ed e : Vec m) (θd : Vec n)
    (α β : ℝ) :
    (rdd - Jdot *ᵥ θd - (α + β) • ed - (α * β) • e) + Jdot *ᵥ θd - rdd + α • ed =
      -β • (ed + α • e) := by
  ext i
  simp [Pi.smul_apply, smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_comm, mul_left_comm, mul_assoc]
  ring

/-- 闭环恒等式（定理 3 代数核心）：a = P_Ω(z) 时
   J·P(z) + J̇θ̇ − r̈_d + αė = J(P(z) − J⁺q) − βs，
   q = r̈_d − J̇θ̇ − (α+β)ė − αβe，s = ė + αe，J⁺q = rpinv J hJ *ᵥ q。
   证明：JJ⁺ = I（accel_pinv_solves）⟹ J·(J⁺q) = q，再以 q_algebra 消元。 -/
theorem closed_loop_identity {n m : ℕ} (J Jdot : Matrix (Fin m) (Fin n) ℝ) (hJ : IsUnit (J * Jᵀ))
    (rdd ed e : Vec m) (θd : Vec n) (α β : ℝ) (P : Vec n → Vec n) (z : Vec n) :
    J *ᵥ P z + Jdot *ᵥ θd - rdd + α • ed =
      J *ᵥ (P z - rpinv J hJ *ᵥ (rdd - Jdot *ᵥ θd - (α + β) • ed - (α * β) • e)) - β • (ed + α • e) := by
  let q : Vec m := rdd - Jdot *ᵥ θd - (α + β) • ed - (α * β) • e
  let y : Vec n := rpinv J hJ *ᵥ q
  have hJy : J *ᵥ y = q := by
    dsimp [y]
    exact accel_pinv_solves J hJ q
  simpa [y, q] using
    calc
      J *ᵥ P z + Jdot *ᵥ θd - rdd + α • ed
          = (J *ᵥ P z - J *ᵥ y) + (J *ᵥ y + Jdot *ᵥ θd - rdd + α • ed) := by abel
      _ = J *ᵥ (P z - y) + (q + Jdot *ᵥ θd - rdd + α • ed) := by
        rw [Matrix.mulVec_sub, hJy]
      _ = J *ᵥ (P z - y) - β • (ed + α • e) := by
        dsimp [q]
        rw [q_algebra Jdot rdd ed e θd α β, neg_smul]
        ring

/-- V̇₂ = ⟨s, J(P(z) − y) − βs⟩ ≤ −2β·(½‖s‖²)（V₂ = ‖s‖²/2，衰减由 −β‖s‖² 直接给出） -/
theorem V2_s_decay {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (y : Vec n) (hy : y ∈ Ω) (J : Matrix (Fin m) (Fin n) ℝ) (ε β : ℝ)
    (hε : 0 < ε) (hβ : 0 < β) (s : Vec m) :
    inner ℝ s (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y) - β • s) ≤
      -β * eNorm s ^ 2 := by
  have h1 := V2_accel_decay P Ω hPdist y hy J ε hε s
  have hN : 0 ≤ ((1 / 2) * ε) * eNorm (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + y) - y) ^ 2 := by
    positivity
  rw [vec_inner_sub_right, vec_inner_smul_right, ← eNorm_sq_eq_inner s]
  nlinarith [h1, hN]

/-- toSpanSingleton 的标量线性：toSpanSingleton (a • v) = a • toSpanSingleton v -/
lemma toSpanSingleton_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) (v : E) :
    ContinuousLinearMap.toSpanSingleton ℝ (a • v) = a • ContinuousLinearMap.toSpanSingleton ℝ v := by
  ext x
  simp [ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply, smul_comm]

/-! ## 比较引理（真证明，Gronwall / 单调性论证）

标量比较引理（时变向量场版）：V(t) = ½‖x(t)‖² 满足 V̇ = D(t) 且 D(t) ≤ −c·V(t)
（c > 0 逐点成立，允许向量场随时间变化）⟹ x(t) → 0（t → ∞）。

证明路线：
1. W(t) = exp(c·t)·V(t)：W' = exp(ct)(D + c·V) ≤ 0（t ≥ 0，乘法规 + hdec）；
2. antitoneOn_of_deriv_nonpos（凸区间 [0,∞) 上导数非正 ⟹ 反单调）⟹ W(t) ≤ W(0)；
3. ⟹ V(t) ≤ V(0)·exp(−ct)（乘 exp(−ct) > 0）；
4. ⟹ eNorm x(t) ≤ sqrt(2·V(0))·exp(−ct/2)（平方比较 + sqrt 单调）；
5. RHS → 0（tendsto_exp_neg_atTop_nhds_zero）⟹ eNorm → 0（夹逼）；
6. 分量界 |xᵢ| ≤ eNorm（eNorm_coord_le）⟹ sup 范数 → 0 ⟹ x → 0（tendsto_norm_zero_iff）。
-/

/-- 比较引理（Gronwall，时变向量场版）：d/dt(½‖x(t)‖²) = D(t) 且 D(t) ≤ −c·½‖x(t)‖²
   （c > 0 逐点成立）⟹ x(t) → 0（t → ∞）。引用：Gronwall 不等式 / 比较引理
   （Khalil, Nonlinear Systems, 定理 3.4）。 -/
theorem comp_lemma_convergence {m : ℕ} (x : ℝ → Vec m) (D : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hVdot : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (x s) ^ 2) (D t) t)
    (hdec : ∀ t, D t ≤ -c * ((1 / 2) * eNorm (x t) ^ 2)) :
    Tendsto x atTop (𝓝 0) := by
  let V : ℝ → ℝ := fun t => (1 / 2) * eNorm (x t) ^ 2
  let W : ℝ → ℝ := fun t => Real.exp (c * t) * V t
  have hVnonneg : ∀ t, 0 ≤ V t := by
    intro t
    dsimp [V]
    exact mul_nonneg (by norm_num) (sq_nonneg (eNorm (x t)))
  have hVder : ∀ t, HasDerivAt V (D t) t := by
    intro t
    simpa [V] using hVdot t
  -- W 的导数：W' = exp(ct)·(c·V + D)
  have hWder : ∀ t, HasDerivAt W (Real.exp (c * t) * (c * V t + D t)) t := by
    intro t
    dsimp [W]
    have h1 : HasDerivAt (fun s => Real.exp (c * s)) (Real.exp (c * t) * c) t := by
      have hg : HasDerivAt (fun s => c * s) c t := by
        simpa using HasDerivAt.const_mul c (hasDerivAt_id t)
      exact HasDerivAt.comp (hh₂ := Real.hasDerivAt_exp (c * t)) (hh := hg)
    have hm := h1.mul (hVder t)
    have hder : (Real.exp (c * t) * c) * V t + Real.exp (c * t) * D t =
        Real.exp (c * t) * (c * V t + D t) := by ring
    rw [hder] at hm
    exact hm
  -- W' ≤ 0 on [0, ∞)
  have hWneg : ∀ t, t ∈ Set.Ici (0 : ℝ) → Real.exp (c * t) * (c * V t + D t) ≤ 0 := by
    intro t ht
    have hdec' : D t ≤ -c * V t := by
      dsimp [V]
      exact hdec t
    have hsum : c * V t + D t ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos (c * t))) hsum
  -- W 在 [0, ∞) 反单调（antitoneOn_of_deriv_nonpos：凸集 + 连续 + 内部可导 + 导数非正）
  have hWantitone : AntitoneOn W (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (D := Set.Ici (0 : ℝ)) ?hD ?hf ?hf' ?hfx
    · exact convex_Ici 0
    · intro x hx
      exact (hWder x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hWder x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hd := (hWder x).deriv
      rw [hd]
      exact hWneg x (interior_subset hx)
  -- V(t) ≤ V(0)·exp(−ct)（t ≥ 0）
  have hVle : ∀ t, 0 ≤ t → V t ≤ V 0 * Real.exp (-c * t) := by
    intro t ht
    have hWt : W t ≤ W 0 := hWantitone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hWt' : Real.exp (c * t) * V t ≤ V 0 := by
      dsimp [W] at hWt
      simpa using hWt
    have hinv : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
      rw [← Real.exp_add]
      rw [show c * t + -c * t = 0 by ring]
      rw [Real.exp_zero]
    have hm : Real.exp (c * t) * V t * Real.exp (-c * t) ≤ V 0 * Real.exp (-c * t) :=
      mul_le_mul_of_nonneg_right hWt' (le_of_lt (Real.exp_pos (-c * t)))
    have hleft : Real.exp (c * t) * V t * Real.exp (-c * t) = V t := by
      calc
        Real.exp (c * t) * V t * Real.exp (-c * t) = V t * (Real.exp (c * t) * Real.exp (-c * t)) := by ring
        _ = V t := by rw [hinv, mul_one]
    rw [hleft] at hm
    exact hm
  -- eNorm 界：t ≥ 0 ⟹ eNorm (x t) ≤ sqrt(2·V 0)·exp(−ct/2)
  have hNle : ∀ t, 0 ≤ t → eNorm (x t) ≤ Real.sqrt (2 * V 0) * Real.exp (-c * t / 2) := by
    intro t ht
    have hVt : V t ≤ V 0 * Real.exp (-c * t) := hVle t ht
    have hsq' : eNorm (x t) ^ 2 ≤ 2 * (V 0 * Real.exp (-c * t)) := by
      have hVt' : (1 / 2) * eNorm (x t) ^ 2 ≤ V 0 * Real.exp (-c * t) := by
        simpa [V] using hVt
      nlinarith
    have hprod : 0 ≤ 2 * (V 0 * Real.exp (-c * t)) := by
      exact mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (mul_nonneg (hVnonneg 0) (le_of_lt (Real.exp_pos (-c * t))))
    have hN : eNorm (x t) ≤ Real.sqrt (2 * (V 0 * Real.exp (-c * t))) := by
      have hsq : eNorm (x t) ^ 2 ≤ (Real.sqrt (2 * (V 0 * Real.exp (-c * t)))) ^ 2 := by
        rw [Real.sq_sqrt hprod]
        exact hsq'
      have hmp := (sq_le_sq.mp hsq)
      simpa [abs_of_nonneg (eNorm_nonneg (x t)), abs_of_nonneg (Real.sqrt_nonneg _)] using hmp
    have hsqrt : Real.sqrt (2 * (V 0 * Real.exp (-c * t))) =
        Real.sqrt (2 * V 0) * Real.exp (-c * t / 2) := by
      rw [← mul_assoc]
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * V 0) (Real.exp (-c * t))]
      congr 1
      exact (Real.sqrt_eq_iff_eq_sq (le_of_lt (Real.exp_pos (-c * t)))
        (le_of_lt (Real.exp_pos (-c * t / 2)))).mpr (by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring)
    rw [hsqrt] at hN
    exact hN
  -- eNorm → 0（夹逼：0 ≤ eNorm ≤ g，g → 0）
  have hg : Tendsto (fun t => Real.sqrt (2 * V 0) * Real.exp (-c * t / 2)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun t => (c / 2) * t) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by positivity)).mpr tendsto_id
    have h1 : Tendsto (fun t => Real.exp (-(c / 2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    have h2 : Tendsto (fun t => Real.exp (-c * t / 2)) atTop (𝓝 0) := by
      have hfun : (fun t => Real.exp (-(c / 2 * t))) = (fun t => Real.exp (-c * t / 2)) := by
        funext t
        congr 1
        ring
      simpa [hfun] using h1
    simpa using h2.const_mul (Real.sqrt (2 * V 0))
  let g : ℝ → ℝ := fun t => Real.sqrt (2 * V 0) * Real.exp (-c * t / 2)
  have hg_nonneg : ∀ t, 0 ≤ g t := by
    intro t
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (Real.exp_pos (-c * t / 2)))
  have hNle_g : ∀ t, 0 ≤ t → eNorm (x t) ≤ g t := by
    intro t ht
    dsimp [g]
    exact hNle t ht
  have hNt : Tendsto (fun t => eNorm (x t)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hg ε hε) with ⟨T, hT⟩
    refine ⟨max T 0, ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_max_right T 0) ht
    have htT : T ≤ t := le_trans (le_max_left T 0) ht
    have hgt : g t < ε := by
      have hd' := hT t htT
      have hd1 : |g t| < ε := by
        simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hd'
      have hpos : 0 ≤ g t := hg_nonneg t
      rwa [abs_of_nonneg hpos] at hd1
    have hpos : 0 ≤ eNorm (x t) := eNorm_nonneg (x t)
    have hd1 : |eNorm (x t)| < ε := by
      rw [abs_of_nonneg hpos]
      exact lt_of_le_of_lt (hNle_g t ht0) hgt
    simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hd1
  -- sup 范数 → 0（分量界 |xᵢ| ≤ eNorm，ℝ 的范数即绝对值）⟹ x → 0
  have hsup : ∀ t, ‖x t‖ ≤ eNorm (x t) := by
    intro t
    rw [pi_norm_le_iff_of_nonneg (eNorm_nonneg (x t))]
    intro i
    exact eNorm_coord_le (x t) i
  have hnt : Tendsto (fun t => ‖x t‖) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hNt ε hε) with ⟨T, hT⟩
    refine ⟨max T 0, ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_max_right T 0) ht
    have htT : T ≤ t := le_trans (le_max_left T 0) ht
    have he : eNorm (x t) < ε := by
      have hd' := hT t htT
      have hd1 : |eNorm (x t)| < ε := by
        simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hd'
      have hpos : 0 ≤ eNorm (x t) := eNorm_nonneg (x t)
      rwa [abs_of_nonneg hpos] at hd1
    have hd1 : |‖x t‖| < ε := by
      have hpos : 0 ≤ ‖x t‖ := norm_nonneg (x t)
      rw [abs_of_nonneg hpos]
      exact lt_of_le_of_lt (hsup t) he
    simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hd1
  exact Metric.tendsto_atTop.mpr (by
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hnt ε hε) with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht
    simpa [dist_eq_norm] using hT t ht)

/-- 稳定线性 ODE 的输入收敛性（比较引理 / 卷积解）：ė = −αe + s（α > 0）且 s → 0
   ⟹ e → 0。解形式 e(t) = e^{−αt}e(0) + ∫₀ᵗ e^{−α(t−τ)}s(τ)dτ，输入趋于零时
   卷积项趋于零。引用：线性系统指数稳定 + 终值定理（Gronwall / Khalil 定理 3.4）。
   注：该结论需卷积积分理论（Fubini/积分换序），暂 axiom 化（与旧项目同源）。 -/
axiom lin_ode_input_convergence {m : ℕ} (e s : ℝ → Vec m) (α : ℝ) (hα : 0 < α)
    (hflow : ∀ t, HasFDerivAt e (ContinuousLinearMap.toSpanSingleton ℝ (s t - α • (e t))) t)
    (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto e atTop (𝓝 0)

/-- 定理 3（加速度级推广）：控制律 a = θ̈ = P_Ωa(−ε⁻¹Jᵀs + J⁺q)，
   s = ė + αe，q = r̈_d − J̇θ̇ − (α+β)ė − αβe，ε, α, β > 0，J⁺q = rpinv J hJ *ᵥ q。
   运动学 r̈ = Jθ̈ + J̇θ̇（闭环 ë = JP_Ωa(z) + J̇θ̇ − r̈_d，z = −ε⁻¹Jᵀs + J⁺q）下：
   (i) s → 0（指数率 β，比较引理）；
   (ii) e → 0（由 s = ė + αe 的稳定线性 ODE，比较引理）。
   前提：rank(J) = m（JJᵀ 可逆）、可行性 J⁺q(t) ∈ Ω_a 逐点成立（仅需成员、
   无需内部——衰减直接来自 −β‖s‖² 项，无需 LaSalle 不变集）、α, β, ε > 0。
   保留性质：Ω_a 允许非凸（投影平移不等式仅需 y ∈ Ω_a）；无积分器（无误差累积）。
   估计器实现 ζẇ = q − JJᵀw 见 estimator_frozen_q（冻结 q 情形）与
   estimator_V1_diff_ineq / V2_off_manifold（时变 q 情形，代数层）。 -/
theorem theorem3 {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (J Jdot : Matrix (Fin m) (Fin n) ℝ) (hJ : IsUnit (J * Jᵀ))
    (α β ε : ℝ) (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε)
    (e ed : ℝ → Vec m) (θd : ℝ → Vec n) (rdd : ℝ → Vec m)
    (hfeas : ∀ t, rpinv J hJ *ᵥ (rdd t - Jdot *ᵥ θd t - (α + β) • ed t - (α * β) • e t) ∈ Ω)
    (hflow_e : ∀ t, HasFDerivAt e (ContinuousLinearMap.toSpanSingleton ℝ (ed t)) t)
    (hflow_ed : ∀ t, HasFDerivAt ed (ContinuousLinearMap.toSpanSingleton ℝ
      (J *ᵥ P (vecDiv (-((Jᵀ) *ᵥ (ed t + α • e t))) ε +
          rpinv J hJ *ᵥ (rdd t - Jdot *ᵥ θd t - (α + β) • ed t - (α * β) • e t)) +
        Jdot *ᵥ θd t - rdd t)) t) :
    Tendsto (fun t => ed t + α • e t) atTop (𝓝 0) ∧ Tendsto e atTop (𝓝 0) := by
  let s : ℝ → Vec m := fun t => ed t + α • e t
  let q : ℝ → Vec m := fun t => rdd t - Jdot *ᵥ θd t - (α + β) • ed t - (α * β) • e t
  let y : ℝ → Vec n := fun t => rpinv J hJ *ᵥ q t
  let z : ℝ → Vec n := fun t => vecDiv (-((Jᵀ) *ᵥ (s t))) ε + y t
  -- 组装 s 的闭环动态：ṡ = ẇ_ed + αė = J(P(z) − y) − βs（closed_loop_identity）
  have hflow_s : ∀ t, HasFDerivAt s (ContinuousLinearMap.toSpanSingleton ℝ
      (J *ᵥ (P (z t) - y t) - β • s t)) t := by
    intro t
    have hαe : HasFDerivAt (fun u => α • e u) (ContinuousLinearMap.toSpanSingleton ℝ (α • ed t)) t := by
      have h := (hflow_e t).const_smul α
      simpa [← toSpanSingleton_smul] using h
    have hsum : HasFDerivAt (fun u => ed u + α • e u)
        (ContinuousLinearMap.toSpanSingleton ℝ (J *ᵥ P (z t) + Jdot *ᵥ θd t - rdd t) +
          ContinuousLinearMap.toSpanSingleton ℝ (α • ed t)) t :=
      (hflow_ed t).add hαe
    have hclosed : J *ᵥ P (z t) + Jdot *ᵥ θd t - rdd t + α • ed t =
        J *ᵥ (P (z t) - y t) - β • s t := by
      have hid := closed_loop_identity J Jdot hJ (rdd t) (ed t) (e t) (θd t) α β P (z t)
      simpa [s, y, q] using hid
    have hsumlin : ContinuousLinearMap.toSpanSingleton ℝ (J *ᵥ P (z t) + Jdot *ᵥ θd t - rdd t) +
          ContinuousLinearMap.toSpanSingleton ℝ (α • ed t) =
        ContinuousLinearMap.toSpanSingleton ℝ (J *ᵥ P (z t) + Jdot *ᵥ θd t - rdd t + α • ed t) := by
      ext u
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    have hres : HasFDerivAt (fun u => ed u + α • e u)
        (ContinuousLinearMap.toSpanSingleton ℝ (J *ᵥ (P (z t) - y t) - β • s t)) t := by
      rw [hsumlin] at hsum
      rw [hclosed] at hsum
      exact hsum
    simpa [s] using hres
  -- V₂ = ‖s‖²/2：V̇₂ = D(t) ≤ −2βV₂（V2_s_decay，y(t) ∈ Ω 由 hfeas）
  let D : ℝ → ℝ := fun t => inner ℝ (s t) (J *ᵥ (P (z t) - y t) - β • s t)
  have hVd : ∀ t, HasDerivAt (fun u : ℝ => (1 / 2) * eNorm (s u) ^ 2) (D t) t := by
    intro t
    have hd := Vdot_deriv s (J *ᵥ (P (z t) - y t) - β • s t) t (hflow_s t)
    simpa [D] using hd
  have hdec : ∀ t, D t ≤ -(2 * β) * ((1 / 2) * eNorm (s t) ^ 2) := by
    intro t
    have h := V2_s_decay P Ω hPdist (y t) (by simpa [y, q] using hfeas t) J ε β hε hβ (s t)
    have h' : D t ≤ -β * eNorm (s t) ^ 2 := by
      unfold D
      dsimp [z]
      exact h
    rw [show -(2 * β) * ((1 / 2) * eNorm (s t) ^ 2) = -β * eNorm (s t) ^ 2 by ring]
    exact h'
  have hs : Tendsto s atTop (𝓝 0) := comp_lemma_convergence s D (2 * β) (by positivity) hVd hdec
  -- e：ė = −αe + s（s t − α•e t = ed t），输入收敛 ⟹ 状态收敛
  have he : Tendsto e atTop (𝓝 0) := by
    apply lin_ode_input_convergence e s α hα
    · intro t
      have h := hflow_e t
      simpa [s] using h
    · exact hs
  exact ⟨hs, he⟩

/-! ## 估计器：ζẇ = q − JJᵀw

冻结 q 情形：指数收敛（theorem2_step1 的直用，V̇₁ ≤ −(2c/ζ)V₁）。
时变 q 情形：代数层不等式 estimator_V1_diff_ineq（V̇₁ ≤ −aV₁ + b，
a = 2c/ζ − 1，b = ½L²，ζ < 2c 时 a > 0 → 实用收敛 O(ζ·sup‖q̇‖)）。
-/

/-- 伴随代数（估计器核心）：⟨x, JJᵀ·vecDiv(−x)/ζ⟩ = −(1/ζ)⟨x, JJᵀx⟩ -/
theorem V1_neg_core {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (x : Vec m) (ζ : ℝ) :
    inner ℝ x (JJt *ᵥ (vecDiv (-x) ζ)) = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) := by
  have hmul : ∀ y : Vec m, JJt *ᵥ (vecDiv y ζ) = vecDiv (JJt *ᵥ y) ζ := by
    intro y
    ext i
    simp [vecDiv, Matrix.mulVec, dotProduct]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hmulneg : JJt *ᵥ (-x) = -(JJt *ᵥ x) := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [hmul, hmulneg]
  simp [vecDiv]
  calc
    ∑ i, x i * (-(JJt *ᵥ x) i / ζ) = ζ⁻¹ * ∑ i, x i * (-(JJt *ᵥ x) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ζ⁻¹ * (-(∑ i, x i * (JJt *ᵥ x) i)) := by
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = -(ζ⁻¹ * ∑ i, x i * (JJt *ᵥ x) i) := by ring

/-- x = JJᵀw − q₀ 时 ⟨x, JJᵀ·((q₀ − JJᵀw)/ζ)⟩ = −(1/ζ)⟨x, JJᵀ·x⟩（ẇ 的伴随代数） -/
theorem V1_dot_algebra {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (rd w : Vec m) (ζ : ℝ) :
    inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ)) =
      -(1 / ζ) * inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (JJt *ᵥ w - rd)) := by
  let x : Vec m := JJt *ᵥ w - rd
  have hx : JJt *ᵥ w - rd = x := rfl
  have hneg : rd - JJt *ᵥ w = -x := by
    ext i
    dsimp [x]
    ring
  have hmul : ∀ y : Vec m, JJt *ᵥ (vecDiv y ζ) = vecDiv (JJt *ᵥ y) ζ := by
    intro y
    ext i
    simp [vecDiv, Matrix.mulVec, dotProduct]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hmulneg : JJt *ᵥ (-x) = -(JJt *ᵥ x) := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  have h1 : JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ) = vecDiv (JJt *ᵥ (-x)) ζ := by
    rw [hneg, hmul]
  have hinner : inner ℝ x (vecDiv (JJt *ᵥ (-x)) ζ) = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) := by
    rw [inner_vec_eq_sum, inner_vec_eq_sum]
    calc
      ∑ i, x i * (vecDiv (JJt *ᵥ (-x)) ζ) i = ∑ i, x i * ((JJt *ᵥ (-x)) i / ζ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ = (1 / ζ) * ∑ i, x i * (JJt *ᵥ (-x)) i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (1 / ζ) * inner ℝ x (JJt *ᵥ (-x)) := by rw [inner_vec_eq_sum]
      _ = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) := by
        rw [hmulneg, vec_inner_neg_right]
        ring
  calc
    inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ))
        = inner ℝ x (JJt *ᵥ (vecDiv (rd - JJt *ᵥ w) ζ)) := by rw [hx]
    _ = inner ℝ x (vecDiv (JJt *ᵥ (-x)) ζ) := by rw [h1]
    _ = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) := hinner
    _ = -(1 / ζ) * inner ℝ (JJt *ᵥ w - rd) (JJt *ᵥ (JJt *ᵥ w - rd)) := by rw [hx]

/-- V₁ 衰减：强单调 c‖x‖² ≤ ⟨x, JJᵀx⟩ ⟹ −(1/ζ)⟨x, JJᵀx⟩ ≤ −(2c/ζ)·½‖x‖² -/
theorem V1_decay {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (x : Vec m) (ζ c : ℝ)
    (hζ : 0 < ζ) (hmono : c * eNorm x ^ 2 ≤ inner ℝ x (JJt *ᵥ x)) :
    -(1 / ζ) * inner ℝ x (JJt *ᵥ x) ≤ -(2 * c / ζ) * ((1 / 2) * eNorm x ^ 2) := by
  have h1 : (2 * c / ζ) * ((1 / 2) * eNorm x ^ 2) ≤ (1 / ζ) * inner ℝ x (JJt *ᵥ x) := by
    calc
      (2 * c / ζ) * ((1 / 2) * eNorm x ^ 2) = (1 / ζ) * (c * eNorm x ^ 2) := by ring
      _ ≤ (1 / ζ) * inner ℝ x (JJt *ᵥ x) := by
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
  linarith [neg_le_neg h1]

/-- Gronwall 型指数收敛（由 comp_lemma_convergence 推导）：V = ½‖x‖² 满足
   V̇ = Vdot(x(t)) 且 V̇ ≤ −cV ⟹ x(t) → 0（t → ∞，指数衰减）。
   引用：Gronwall 不等式 / 比较引理（Khalil, Nonlinear Systems, 定理 3.4）。 -/
theorem exp_convergence {m : ℕ} (x : ℝ → Vec m) (Vdot : Vec m → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hVdot : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (x s) ^ 2) (Vdot (x t)) t)
    (hdec : ∀ t, Vdot (x t) ≤ -c * ((1 / 2) * eNorm (x t) ^ 2)) :
    Tendsto x atTop (𝓝 0) := by
  exact comp_lemma_convergence x (fun t => Vdot (x t)) c hc hVdot hdec

/-- 估计器收敛（冻结 q 情形）：ζẇ = q₀ − JJᵀw ⟹ JJᵀw(t) → q₀（指数），
   Jᵀw* = J⁺q₀ 无需矩阵求逆。前提：强单调 ⟨x, JJᵀx⟩ ≥ c‖x‖ₑ²（rank JJᵀ = m，
   c = λ_min(JJᵀ) > 0）。 -/
theorem estimator_frozen_q {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (q0 : Vec m)
    (w : ℝ → Vec m) (ζ c : ℝ) (hζ : 0 < ζ) (hc : 0 < c)
    (hmono : ∀ x : Vec m, c * eNorm x ^ 2 ≤ inner ℝ x (JJt *ᵥ x))
    (hflow : ∀ t, HasFDerivAt w (ContinuousLinearMap.toSpanSingleton ℝ
      (vecDiv (q0 - JJt *ᵥ (w t)) ζ)) t) :
    Tendsto (fun t => JJt *ᵥ (w t) - q0) atTop (𝓝 0) := by
  let x : ℝ → Vec m := fun t => JJt *ᵥ (w t) - q0
  let Vdot : Vec m → ℝ := fun xv => inner ℝ xv (JJt *ᵥ (vecDiv (-xv) ζ))
  have hxcomp : ∀ t, ∀ i : Fin m,
      HasDerivAt (fun s => (x s) i) ((JJt *ᵥ (vecDiv (q0 - JJt *ᵥ (w t)) ζ)) i) t := by
    intro t i
    have hwj : ∀ j : Fin m, HasDerivAt (fun s => (w s) j)
        ((vecDiv (q0 - JJt *ᵥ (w t)) ζ) j) t :=
      coord_deriv_of_span w (vecDiv (q0 - JJt *ᵥ (w t)) ζ) t (hflow t)
    have hterm : ∀ j : Fin m, HasDerivAt (fun s => JJt i j * (w s) j)
        (JJt i j * (vecDiv (q0 - JJt *ᵥ (w t)) ζ) j) t := by
      intro j
      exact (hwj j).const_mul (JJt i j)
    have hsum : HasDerivAt (fun s => ∑ j, JJt i j * (w s) j)
        (∑ j, JJt i j * (vecDiv (q0 - JJt *ᵥ (w t)) ζ) j) t :=
      HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m)))
        (A := fun j s => JJt i j * (w s) j)
        (A' := fun j => JJt i j * (vecDiv (q0 - JJt *ᵥ (w t)) ζ) j)
        (fun j hj => hterm j)
    -- sub_const 给出导数 f'（不带 `- 0`）；simp 的 hasDerivAt_sub_const_iff
    -- 会把目标里的 `- q0 i` 消掉（常数平移不改变导数），simpa 两侧一致归一
    have hminus : HasDerivAt (fun s => (∑ j, JJt i j * (w s) j) - q0 i)
        (∑ j, JJt i j * (vecDiv (q0 - JJt *ᵥ (w t)) ζ) j) t := by
      exact hsum.sub_const (q0 i)
    simpa [x, Matrix.mulVec, dotProduct] using hminus
  have hVd : ∀ t, HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (x s) ^ 2) (Vdot (x t)) t := by
    intro t
    have hneg : q0 - JJt *ᵥ (w t) = -(x t) := by
      dsimp [x]
      ext i
      simp
    have hed : JJt *ᵥ (vecDiv (q0 - JJt *ᵥ (w t)) ζ) = JJt *ᵥ (vecDiv (-(x t)) ζ) := by
      rw [hneg]
    have hd := Vdot_deriv_comp x (JJt *ᵥ (vecDiv (-(x t)) ζ)) t (by
      intro i
      simpa [hed] using hxcomp t i)
    simpa [Vdot] using hd
  have hVneg : ∀ t, Vdot (x t) ≤ -(2 * c / ζ) * ((1 / 2) * eNorm (x t) ^ 2) := by
    intro t
    have ha := V1_dot_algebra JJt q0 (w t) ζ
    have hdec := V1_decay JJt (x t) ζ c hζ (hmono (x t))
    have hneg : q0 - JJt *ᵥ (w t) = -(x t) := by
      dsimp [x]
      ext i
      simp
    unfold Vdot
    rw [show vecDiv (-(x t)) ζ = vecDiv (q0 - JJt *ᵥ (w t)) ζ by rw [← hneg]]
    rw [show x t = JJt *ᵥ (w t) - q0 by rfl]
    rw [ha]
    rw [show JJt *ᵥ (w t) - q0 = x t by rfl]
    exact hdec
  exact exp_convergence x Vdot (2 * c / ζ) (by positivity) hVd hVneg

/-! ## 离流形交叉项界（估计器瞬态 w ≠ J⁺q）

控制律用估计器输出 Jᵀw（未收敛）时，z' = vecDiv(−Jᵀs/ε) + Jᵀw，
闭环 V̇₂' = ⟨s, J(P(z')−y) − βs⟩。伴随拆分出交叉项 ε⟨Jᵀw−y, P(z')−y⟩，
用 2xy ≤ x²+y²（abs_inner_le_half_add，无需 Cauchy-Schwarz）吸收：
V̇₂' ≤ −β‖s‖² + (ε/2)‖Jᵀw−y‖²。与 V₁ 的实用收敛结合（ζ → 0 收缩）。
-/

/-- 离流形交叉项界：z' = vecDiv(−Jᵀs/ε) + w（w 未收敛）时
   ⟨s, J(P(z') − y) − βs⟩ ≤ −β‖s‖² + (ε/2)‖w − y‖²（y = J⁺q ∈ Ω）。
   证明：⟨s, J(P−y)⟩ = −ε⟨z'−y, P−y⟩ + ε⟨w−y, P−y⟩（伴随 + z' = z''+(w−y)），
   投影平移不等式给出 −(ε/2)‖P−y‖²，交叉项经 2xy ≤ x²+y² 给出 (ε/2)‖w−y‖²。 -/
theorem V2_off_manifold {n m : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (y : Vec n) (hy : y ∈ Ω) (J : Matrix (Fin m) (Fin n) ℝ) (ε β : ℝ)
    (hε : 0 < ε) (hβ : 0 < β) (s : Vec m) (w : Vec n) :
    inner ℝ s (J *ᵥ (P (vecDiv (-((Jᵀ) *ᵥ s)) ε + w) - y) - β • s) ≤
      -β * eNorm s ^ 2 + (ε / 2) * eNorm (w - y) ^ 2 := by
  let z'' : Vec n := vecDiv (-((Jᵀ) *ᵥ s)) ε + y
  let z' : Vec n := vecDiv (-((Jᵀ) *ᵥ s)) ε + w
  have hz' : z' = z'' + (w - y) := by
    dsimp [z', z'']
    abel
  have hz2 : z'' - y = z' - w := by
    dsimp [z'', z']
    abel
  have hz3 : z' - w = (z' - y) - (w - y) := by abel
  have hJTs : (Jᵀ) *ᵥ s = -(ε • (z'' - y)) := by
    ext i
    have hz : z'' i - y i = -(Jᵀ *ᵥ s) i / ε := by
      dsimp [z'', vecDiv]
      ring
    simp [Pi.smul_apply, hz]
    field_simp [hε.ne']
  have hadj : inner ℝ s (J *ᵥ (P z' - y)) =
      -ε * inner ℝ (z' - y) (P z' - y) + ε * inner ℝ (w - y) (P z' - y) := by
    have h1 : inner ℝ s (J *ᵥ (P z' - y)) = inner ℝ ((Jᵀ) *ᵥ s) (P z' - y) := by
      rw [vec_inner_symm s (J *ᵥ (P z' - y))]
      rw [vec_mulVec_adjoint J (P z' - y) s]
      rw [vec_inner_symm (P z' - y) ((Jᵀ) *ᵥ s)]
    calc
      inner ℝ s (J *ᵥ (P z' - y)) = inner ℝ ((Jᵀ) *ᵥ s) (P z' - y) := h1
      _ = -ε * inner ℝ (z'' - y) (P z' - y) := by
        rw [hJTs]
        rw [vec_inner_neg_left, vec_inner_smul_left]
        ring
      _ = -ε * inner ℝ (z' - w) (P z' - y) := by rw [hz2]
      _ = -ε * inner ℝ ((z' - y) - (w - y)) (P z' - y) := by rw [hz3]
      _ = -ε * (inner ℝ (z' - y) (P z' - y) - inner ℝ (w - y) (P z' - y)) := by
        rw [vec_inner_sub_left]
      _ = -ε * inner ℝ (z' - y) (P z' - y) + ε * inner ℝ (w - y) (P z' - y) := by ring
  have hineq : eNorm (P z' - y) ^ 2 ≤ 2 * inner ℝ (z' - y) (P z' - y) :=
    proj_sq_ineq_at P Ω hPdist y hy z'
  have hcross : ε * inner ℝ (w - y) (P z' - y) ≤
      (ε / 2) * eNorm (w - y) ^ 2 + (ε / 2) * eNorm (P z' - y) ^ 2 := by
    have habs := abs_inner_le_half_add (w - y) (P z' - y)
    have hle : inner ℝ (w - y) (P z' - y) ≤
        (1 / 2) * eNorm (w - y) ^ 2 + (1 / 2) * eNorm (P z' - y) ^ 2 := by
      have hle_abs : inner ℝ (w - y) (P z' - y) ≤ |inner ℝ (w - y) (P z' - y)| := le_abs_self _
      linarith [habs, hle_abs]
    have hm := mul_le_mul_of_nonneg_left hle (le_of_lt hε)
    calc
      ε * inner ℝ (w - y) (P z' - y) ≤ ε * ((1 / 2) * eNorm (w - y) ^ 2 + (1 / 2) * eNorm (P z' - y) ^ 2) := hm
      _ = (ε / 2) * eNorm (w - y) ^ 2 + (ε / 2) * eNorm (P z' - y) ^ 2 := by ring
  have hmain : inner ℝ s (J *ᵥ (P z' - y)) ≤ (ε / 2) * eNorm (w - y) ^ 2 := by
    rw [hadj]
    nlinarith [hineq, hcross, hε]
  rw [vec_inner_sub_right, vec_inner_smul_right, ← eNorm_sq_eq_inner s]
  nlinarith [hmain, hβ]

/-! ## 估计器时变 q：微分不等式（代数层）

x(t) = JJᵀw(t) − q(t)，ẇ = vecDiv(−x)/ζ（q 时变）时
V̇₁ = ⟨x, JJᵀẇ⟩ − ⟨x, q̇⟩。假设 ‖q̇‖ ≤ L：
V̇₁ ≤ −(2c/ζ)·½‖x‖² + ½‖x‖² + ½L² = −(2c/ζ − 1)·½‖x‖² + ½L²。
ζ < 2c 时系数 a = 2c/ζ − 1 > 0，非齐次线性比较引理给出实用收敛
（最终 V₁ ≤ ½L²/a，随 ζ → 0 收缩）。 -/

/-- 估计器时变 q 的微分不等式：x = JJᵀw − q，‖q̇‖ ≤ L 时
   ⟨x, JJᵀẇ⟩ − ⟨x, q̇⟩ ≤ −(2c/ζ − 1)·½‖x‖² + ½L²
   （ẇ = vecDiv(−x)/ζ；a = 2c/ζ − 1，ζ < 2c 时 a > 0） -/
theorem estimator_V1_diff_ineq {m : ℕ} (JJt : Matrix (Fin m) (Fin m) ℝ) (x qdot : Vec m)
    (ζ c L : ℝ) (hζ : 0 < ζ) (hc : 0 < c) (hL : 0 ≤ L)
    (hmono : c * eNorm x ^ 2 ≤ inner ℝ x (JJt *ᵥ x))
    (hqle : eNorm qdot ≤ L) :
    inner ℝ x (JJt *ᵥ (vecDiv (-x) ζ)) - inner ℝ x qdot ≤
      -(2 * c / ζ - 1) * ((1 / 2) * eNorm x ^ 2) + (1 / 2) * L ^ 2 := by
  have h1 := V1_neg_core JJt x ζ
  have hdec := V1_decay JJt x ζ c hζ hmono
  have hcross : |inner ℝ x qdot| ≤ (1 / 2) * eNorm x ^ 2 + (1 / 2) * L ^ 2 := by
    have habs := abs_inner_le_half_add x qdot
    have hsqle : eNorm qdot ^ 2 ≤ L ^ 2 := sq_le_sq_of_nonneg (eNorm_nonneg qdot) hL hqle
    have hI2 : (1 / 2) * eNorm x ^ 2 + (1 / 2) * eNorm qdot ^ 2 ≤ (1 / 2) * eNorm x ^ 2 + (1 / 2) * L ^ 2 := by
      have hq2 : (1 / 2) * eNorm qdot ^ 2 ≤ (1 / 2) * L ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsqle (by norm_num)
      linarith
    exact le_trans habs hI2
  have hle : inner ℝ x qdot ≤ (1 / 2) * eNorm x ^ 2 + (1 / 2) * L ^ 2 := by
    have hle_abs : inner ℝ x qdot ≤ |inner ℝ x qdot| := le_abs_self _
    linarith [hcross, hle_abs]
  have hneg : -inner ℝ x qdot ≤ (1 / 2) * eNorm x ^ 2 + (1 / 2) * L ^ 2 := by
    have hI1 : -((1 / 2) * eNorm x ^ 2 + (1 / 2) * L ^ 2) ≤ inner ℝ x qdot := (abs_le.mp hcross).1
    linarith
  calc
    inner ℝ x (JJt *ᵥ (vecDiv (-x) ζ)) - inner ℝ x qdot
        = -(1 / ζ) * inner ℝ x (JJt *ᵥ x) - inner ℝ x qdot := by rw [h1]
    _ ≤ -(2 * c / ζ) * ((1 / 2) * eNorm x ^ 2) + (1 / 2) * eNorm x ^ 2 + (1 / 2) * L ^ 2 := by
      have hneg : -inner ℝ x qdot ≤ (1 / 2) * eNorm x ^ 2 + (1 / 2) * L ^ 2 := by linarith
      linarith [hdec, hneg]
    _ = -(2 * c / ζ - 1) * ((1 / 2) * eNorm x ^ 2) + (1 / 2) * L ^ 2 := by ring

end

end Theorem3
