/-
Copyright (c) 2026 wj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wj
-/
import Mathlib
/-! # Core 最小基础设施（独立项目 theorem3 专用）

定理 3（加速度级推广）形式化所需的最小引理库：欧氏内积与范数（eNorm）、
逐分量除法 vecDiv、右伪逆 rpinv（JJ† = I）、投影平移不等式（任意集，无需凸性）、
Lyapunov 导数机器。全部为根命名空间定义（本项目自包含，不依赖外部项目）。
-/

open Matrix
open scoped BigOperators

abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Vec 的欧氏内积：⟨x, y⟩ = ∑ x_i y_i（Mathlib 对 `Fin n → ℝ` 无 Inner 实例） -/
instance instInnerVec {n : ℕ} : Inner ℝ (Vec n) where
  inner x y := ∑ i, x i * y i

/-- 内积按定义展开为逐分量乘积和 -/
@[simp]
theorem inner_vec_eq_sum {n : ℕ} (x y : Vec n) : inner ℝ x y = ∑ i, x i * y i := by
  rfl

lemma vec_inner_add_left {n : ℕ} (a b x : Vec n) :
    inner ℝ (a + b) x = inner ℝ a x + inner ℝ b x := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum, inner_vec_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change (a i + b i) * x i = a i * x i + b i * x i
  ring

lemma vec_inner_add_right {n : ℕ} (x a b : Vec n) :
    inner ℝ x (a + b) = inner ℝ x a + inner ℝ x b := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum, inner_vec_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change x i * (a i + b i) = x i * a i + x i * b i
  ring

lemma vec_inner_symm {n : ℕ} (x y : Vec n) : inner ℝ x y = inner ℝ y x := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm (x i) (y i)

lemma vec_inner_smul_left {n : ℕ} (a : ℝ) (x y : Vec n) :
    inner ℝ (a • x) y = a * inner ℝ x y := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  calc
    ∑ i, (a • x) i * y i = ∑ i, a * (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
      ring
    _ = a * ∑ i, x i * y i := by rw [Finset.mul_sum]

lemma vec_inner_smul_right {n : ℕ} (a : ℝ) (x y : Vec n) :
    inner ℝ x (a • y) = a * inner ℝ x y := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  calc
    ∑ i, x i * (a • y) i = ∑ i, a * (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
      ring
    _ = a * ∑ i, x i * y i := by rw [Finset.mul_sum]

lemma vec_inner_neg_left {n : ℕ} (x y : Vec n) : inner ℝ (-x) y = - inner ℝ x y := by
  simpa using vec_inner_smul_left (-1) x y

lemma vec_inner_neg_right {n : ℕ} (x y : Vec n) : inner ℝ x (-y) = - inner ℝ x y := by
  rw [vec_inner_symm, vec_inner_neg_left, vec_inner_symm]

lemma vec_inner_sub_left {n : ℕ} (a b x : Vec n) :
    inner ℝ (a - b) x = inner ℝ a x - inner ℝ b x := by
  rw [sub_eq_add_neg, vec_inner_add_left, vec_inner_neg_left]
  ring

lemma vec_inner_sub_right {n : ℕ} (x a b : Vec n) :
    inner ℝ x (a - b) = inner ℝ x a - inner ℝ x b := by
  rw [sub_eq_add_neg, vec_inner_add_right, vec_inner_neg_right]
  ring

/-- 伴随性：⟨Ax, y⟩ = ⟨x, Aᵀy⟩ -/
lemma vec_mulVec_adjoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Vec n) (y : Vec m) :
    inner ℝ (A *ᵥ x) y = inner ℝ x (Aᵀ *ᵥ y) := by
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  change ∑ i, (∑ j, A i j * x j) * y i = ∑ j, x j * (∑ i, A i j * y i)
  calc
    ∑ i, (∑ j, A i j * x j) * y i = ∑ i, ∑ j, A i j * x j * y i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    _ = ∑ j, ∑ i, A i j * x j * y i := by rw [Finset.sum_comm]
    _ = ∑ j, x j * (∑ i, A i j * y i) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        ∑ i, A i j * x j * y i = ∑ i, x j * (A i j * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = x j * ∑ i, A i j * y i := by rw [Finset.mul_sum]

/-- 欧氏范数：‖x‖ₑ = sqrt(∑ x_i²)（Mathlib 默认范数是 sup 范数，与内积不相容） -/
noncomputable def eNorm {n : ℕ} (x : Vec n) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- eNorm 平方恒等式：‖x‖ₑ² = ⟨x, x⟩ -/
theorem eNorm_sq_eq_inner {n : ℕ} (x : Vec n) : eNorm x ^ 2 = inner ℝ x x := by
  unfold eNorm
  rw [Real.sq_sqrt]
  · rw [inner_vec_eq_sum]
    congr 1
    ext i
    ring
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem eNorm_nonneg {n : ℕ} (x : Vec n) : 0 ≤ eNorm x := by
  unfold eNorm
  exact Real.sqrt_nonneg _

theorem eNorm_eq_zero_iff {n : ℕ} (x : Vec n) : eNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    have hsqrt : Real.sqrt (∑ i, x i ^ 2) = 0 := by simpa [eNorm] using h
    have hsum : ∑ i, x i ^ 2 = 0 := by
      have : (Real.sqrt (∑ i, x i ^ 2)) ^ 2 = 0 := by rw [hsqrt]; norm_num
      simpa [Real.sq_sqrt hs] using this
    have hzero : ∀ i, x i = 0 := by
      intro i
      have hi : x i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp hsum i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hi
    ext i
    exact hzero i
  · intro h
    simp [h, eNorm]

/-- 通用恒等式：‖X − B‖ₑ² = ‖X‖ₑ² − 2⟨X,B⟩ + ‖B‖ₑ² -/
theorem eNorm_sub_sq {n : ℕ} (X B : Vec n) :
    eNorm (X - B) ^ 2 = eNorm X ^ 2 - 2 * inner ℝ X B + eNorm B ^ 2 := by
  rw [eNorm_sq_eq_inner, eNorm_sq_eq_inner, eNorm_sq_eq_inner]
  rw [vec_inner_sub_left]
  rw [vec_inner_sub_right]
  rw [vec_inner_sub_right]
  rw [vec_inner_symm B X]
  ring

theorem eNorm_neg {n : ℕ} (x : Vec n) : eNorm (-x) = eNorm x := by
  unfold eNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith [sq_nonneg (b - a), hab]

theorem eNorm_smul {n : ℕ} (a : ℝ) (x : Vec n) : eNorm (a • x) = |a| * eNorm x := by
  unfold eNorm
  calc
    Real.sqrt (∑ i, (a • x) i ^ 2) = Real.sqrt (a ^ 2 * ∑ i, x i ^ 2) := by
      congr 1
      calc
        ∑ i, (a • x) i ^ 2 = ∑ i, (a * x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp
        _ = ∑ i, a ^ 2 * x i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = a ^ 2 * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]
    _ = Real.sqrt (a ^ 2) * Real.sqrt (∑ i, x i ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg a)]
    _ = |a| * Real.sqrt (∑ i, x i ^ 2) := by rw [Real.sqrt_sq_eq_abs]

/-- 分量界：|x i| ≤ ‖x‖ₑ（单分量平方 ≤ 平方和） -/
theorem eNorm_coord_le {n : ℕ} (x : Vec n) (i : Fin n) : |x i| ≤ eNorm x := by
  unfold eNorm
  have hle : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j => x j ^ 2)
      (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hsq : (|x i|) ^ 2 ≤ (Real.sqrt (∑ j, x j ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))]
    simpa [sq_abs] using hle
  have habs : |x i| ≤ Real.sqrt (∑ j, x j ^ 2) := by
    have hmp := (sq_le_sq.mp hsq)
    simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using hmp
  exact habs

/-- 2|xy| ≤ x²+y² 的逐项形式：|aᵢbᵢ| ≤ ½aᵢ² + ½bᵢ² -/
theorem abs_mul_le_half_add {a b : ℝ} : |a * b| ≤ (1 / 2) * a ^ 2 + (1 / 2) * b ^ 2 := by
  have h : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg (|a| - |b|)
  have habs : |a| * |b| ≤ (1 / 2) * a ^ 2 + (1 / 2) * b ^ 2 := by
    have ha : |a| ^ 2 = a ^ 2 := by rw [sq_abs]
    have hb : |b| ^ 2 = b ^ 2 := by rw [sq_abs]
    nlinarith [h, ha, hb]
  simpa [abs_mul] using habs

/-- 内积绝对值界（2xy ≤ x²+y²，无需 Cauchy-Schwarz）：
   |⟨a,b⟩| ≤ ½‖a‖ₑ² + ½‖b‖ₑ² -/
theorem abs_inner_le_half_add {n : ℕ} (a b : Vec n) :
    |inner ℝ a b| ≤ (1 / 2) * eNorm a ^ 2 + (1 / 2) * eNorm b ^ 2 := by
  rw [inner_vec_eq_sum]
  rw [eNorm_sq_eq_inner a, eNorm_sq_eq_inner b]
  rw [inner_vec_eq_sum, inner_vec_eq_sum]
  have h1 : |∑ i, a i * b i| ≤ ∑ i, |a i * b i| :=
    Finset.abs_sum_le_sum_abs (fun i => a i * b i) Finset.univ
  have h2 : ∑ i, |a i * b i| ≤ (1 / 2) * ∑ i, a i * a i + (1 / 2) * ∑ i, b i * b i := by
    calc
      ∑ i, |a i * b i| = ∑ i, |a i| * |b i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
      _ ≤ ∑ i, ((1 / 2) * (a i * a i) + (1 / 2) * (b i * b i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have h : 0 ≤ (|a i| - |b i|) ^ 2 := sq_nonneg (|a i| - |b i|)
        have ha : |a i| ^ 2 = a i * a i := by rw [sq_abs, pow_two]
        have hb : |b i| ^ 2 = b i * b i := by rw [sq_abs, pow_two]
        nlinarith [h, ha, hb]
      _ = (1 / 2) * ∑ i, a i * a i + (1 / 2) * ∑ i, b i * b i := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith [h1, h2]

/-- 向量逐分量除以标量（`Vec n → ℝ` 无标量除法实例） -/
noncomputable def vecDiv {n : ℕ} (x : Vec n) (c : ℝ) : Vec n := fun i => x i / c

/-- 右伪逆 J† = Jᵀ(JJᵀ)⁻¹（要求 JJᵀ 可逆，即 J 行满秩） -/
noncomputable def rpinv {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ)
    (_h : IsUnit (J * Jᵀ)) : Matrix (Fin n) (Fin m) ℝ :=
  Jᵀ * (J * Jᵀ)⁻¹

/-- 关键恒等式：JJ† = I_m -/
theorem rpinv_mul_eq_one {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ)) :
    J * rpinv J h = 1 := by
  rw [rpinv, ← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv (J * Jᵀ) ((Matrix.isUnit_iff_isUnit_det (J * Jᵀ)).1 h)

/-- J·(J†w) = w（加速度级约束 Jθ̈ = q 的满足性） -/
theorem accel_pinv_solves {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) (h : IsUnit (J * Jᵀ))
    (w : Vec m) :
    J *ᵥ (rpinv J h *ᵥ w) = w := by
  simp [Matrix.mulVec_mulVec, rpinv_mul_eq_one J h, Matrix.one_mulVec]

/-- 投影平移不等式：y ∈ Ω 时 ‖P z − y‖ₑ² ≤ 2⟨z − y, P z − y⟩
   （从投影最小距离性质 ‖Pz − z‖ ≤ ‖y − z‖ 配平方；任意集 Ω，无需凸性） -/
theorem proj_sq_ineq_at {n : ℕ} (P : Vec n → Vec n) (Ω : Set (Vec n))
    (hPdist : ∀ z y : Vec n, y ∈ Ω → eNorm (P z - z) ≤ eNorm (y - z))
    (y0 : Vec n) (hy0 : y0 ∈ Ω) (z : Vec n) :
    eNorm (P z - y0) ^ 2 ≤ 2 * inner ℝ (z - y0) (P z - y0) := by
  have h1 : eNorm (P z - z) ≤ eNorm (y0 - z) := hPdist z y0 hy0
  have h1sq : eNorm (P z - z) ^ 2 ≤ eNorm (y0 - z) ^ 2 := by
    exact sq_le_sq_of_nonneg (eNorm_nonneg (P z - z)) (eNorm_nonneg (y0 - z)) h1
  have hsub : P z - z = (P z - y0) - (z - y0) := by abel
  have hsq := eNorm_sub_sq (P z - y0) (z - y0)
  have hsq' : eNorm (P z - z) ^ 2 = eNorm (P z - y0) ^ 2 - 2 * inner ℝ (P z - y0) (z - y0) + eNorm (z - y0) ^ 2 := by
    rw [hsub]
    exact hsq
  have hyn : eNorm (y0 - z) = eNorm (z - y0) := by
    simpa using eNorm_neg (z - y0)
  have hsq2 : eNorm (P z - y0) ^ 2 - 2 * inner ℝ (P z - y0) (z - y0) + eNorm (z - y0) ^ 2 ≤ eNorm (z - y0) ^ 2 := by
    rw [← hsq']
    rw [hyn] at h1sq
    exact h1sq
  have hcore : eNorm (P z - y0) ^ 2 ≤ 2 * inner ℝ (P z - y0) (z - y0) := by
    nlinarith
  rw [vec_inner_symm]
  exact hcore

/-- HasFDerivAt 的分量导数：HasFDerivAt w (toSpanSingleton ed) t ⟹ 每分量 (w s) j 的导数为 ed j -/
lemma coord_deriv_of_span {m : ℕ} (w : ℝ → Vec m) (ed : Vec m) (t : ℝ)
    (hflow : HasFDerivAt w (ContinuousLinearMap.toSpanSingleton ℝ ed) t) :
    ∀ j : Fin m, HasDerivAt (fun s : ℝ => (w s) j) (ed j) t := by
  intro j
  let π : Vec m →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hgdiff : DifferentiableAt ℝ (fun v : Vec m => π v) (w t) := π.differentiableAt
  have hediff : DifferentiableAt ℝ w t := hflow.differentiableAt
  have hfc := fderiv_comp (g := fun v : Vec m => π v) (f := w) (x := t) hgdiff hediff
  have hπ : fderiv ℝ (fun v : Vec m => π v) (w t) = π := π.fderiv
  have hfe : fderiv ℝ w t = ContinuousLinearMap.toSpanSingleton ℝ ed := hflow.fderiv
  have hcoord : fderiv ℝ (fun s : ℝ => (w s) j) t = ContinuousLinearMap.toSpanSingleton ℝ (ed j) := by
    calc
      fderiv ℝ (fun s : ℝ => (w s) j) t = fderiv ℝ (fun s : ℝ => π (w s)) t := by rfl
      _ = (fderiv ℝ (fun v : Vec m => π v) (w t)).comp (fderiv ℝ w t) := hfc
      _ = π.comp (ContinuousLinearMap.toSpanSingleton ℝ ed) := by rw [hπ, hfe]
      _ = ContinuousLinearMap.toSpanSingleton ℝ (ed j) := by
        ext u
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, π]
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => (w s) j) t := by
    fun_prop
  have hder : deriv (fun s : ℝ => (w s) j) t = ed j := by
    rw [show deriv (fun s : ℝ => (w s) j) t = (fderiv ℝ (fun s : ℝ => (w s) j) t) 1 by
      rfl]
    rw [hcoord]
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  simpa [hder] using hdiff.hasDerivAt

/-- V = ‖e‖²/2 沿轨迹的导数（逐分量导数版本）：
   d/dt (½‖e(t)‖²) = ⟨e(t), ed⟩，前提是 e 的每个分量导数存在且为 ed i -/
theorem Vdot_deriv_comp {m : ℕ} (e : ℝ → Vec m) (ed : Vec m) (t : ℝ)
    (hcomp : ∀ i : Fin m, HasDerivAt (fun s : ℝ => (e s) i) (ed i) t) :
    HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (inner ℝ (e t) ed) t := by
  have hmul : ∀ i : Fin m, HasDerivAt (fun s : ℝ => (e s) i * (e s) i) (2 * (e t) i * ed i) t := by
    intro i
    have hm := (hcomp i).mul (hcomp i)
    have hval : ed i * (e t) i + (e t) i * ed i = 2 * (e t) i * ed i := by ring
    convert hm using 1 <;> try rfl
    exact hval.symm
  have hsum : HasDerivAt (fun s : ℝ => ∑ i : Fin m, (e s) i * (e s) i)
      (∑ i : Fin m, 2 * (e t) i * ed i) t := by
    convert (HasDerivAt.sum (u := Finset.univ) (fun i hi => hmul i)) using 1 <;> try rfl
    · funext s
      rw [Finset.sum_apply]
  have hhalf := hsum.const_mul (1 / 2)
  have hsq : ∀ s : ℝ, eNorm (e s) ^ 2 = ∑ i : Fin m, (e s) i * (e s) i := by
    intro s
    rw [eNorm_sq_eq_inner, inner_vec_eq_sum]
  have hval : (1 / 2) * ∑ i : Fin m, 2 * (e t) i * ed i = inner ℝ (e t) ed := by
    rw [inner_vec_eq_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  convert hhalf using 1 <;> try rfl
  · funext s
    rw [hsq]
  · exact hval.symm

/-- V = ‖e‖²/2 沿轨迹的导数（HasFDerivAt 版本）：d/dt (½‖e(t)‖²) = ⟨e(t), ė(t)⟩ -/
theorem Vdot_deriv {m : ℕ} (e : ℝ → Vec m) (ed : Vec m) (t : ℝ)
    (hflow : HasFDerivAt e (ContinuousLinearMap.toSpanSingleton ℝ ed) t) :
    HasDerivAt (fun s : ℝ => (1 / 2) * eNorm (e s) ^ 2) (inner ℝ (e t) ed) t := by
  exact Vdot_deriv_comp e ed t (coord_deriv_of_span e ed t hflow)
