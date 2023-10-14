/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne, Alexander Bentkamp
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Probability.Notation

/-!
# Gaussian distributions over ℝ

We define a Gaussian measure over the reals.

## Main definitions

* `gaussianPdfReal`: the function `μ v x ↦ (1 / (sqrt (2 * pi * v))) * exp (- (x - μ)^2 / (2 * v))`,
  which is the probability density function of a Gaussian distribution with mean `μ` and
  variance `v` (when `v ≠ 0`).
* `gaussianPdf`: `ℝ≥0∞`-valued pdf, `gaussianPdf μ v x = ENNReal.ofReal (gaussianPdfReal μ v x)`.
* `gaussianReal`: a Gaussian measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `gaussianPdf μ v` with respect to the Lebesgue measure.

## Main results

* `gaussianReal_add_const`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `X + y` is Gaussian with mean `μ + y` and variance `v`.
* `gaussianReal_const_mul`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `c * X` is Gaussian with mean `c * μ` and variance `c^2 * v`.

-/

open scoped ENNReal NNReal Real

namespace MeasureTheory

end MeasureTheory

open MeasureTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

namespace ProbabilityTheory

section GaussianPdf

/-- Probability density function of the gaussian distribution with mean `μ` and variance `v`. -/
noncomputable
def gaussianPdfReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  ((1 : ℝ) / (Real.sqrt (2 * Real.pi * v))) * rexp (- (x - μ)^2 / (2 * v))

lemma gaussianPdfReal_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPdfReal μ v =
      fun x ↦ ((1 : ℝ) / (Real.sqrt (2 * Real.pi * v))) * rexp (- (x - μ)^2 / (2 * v)) := rfl

@[simp]
lemma gaussianPdfReal_zero_var (m : ℝ) : gaussianPdfReal m 0 = 0 := by
  ext1 x
  simp [gaussianPdfReal]

/-- The gaussian pdf is positive when the variance is not zero. -/
lemma gaussianPdfReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPdfReal μ v x := by
  rw [gaussianPdfReal]
  positivity

/--The gaussian pdf is nonnegative. -/
lemma gaussianPdfReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ gaussianPdfReal μ v x := by
  rw [gaussianPdfReal]
  positivity

/-- The gaussian pdf is measurable. -/
lemma measurable_gaussianPdfReal (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPdfReal μ v) :=
  (((measurable_id.add_const _).pow_const _).neg.div_const _).exp.const_mul _

/-- The gaussian pdf is strongly measurable. -/
lemma stronglyMeasurable_gaussianPdfReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (gaussianPdfReal μ v) :=
  (measurable_gaussianPdfReal μ v).stronglyMeasurable

lemma integrable_gaussianPdfReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (gaussianPdfReal μ v) := by
  rw [gaussianPdfReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : ℝ → ℝ := fun x ↦ (1 : ℝ) / Real.sqrt (2 * π * ↑v) * rexp (- x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x ↦ (1 : ℝ) / Real.sqrt (2 * π * ↑v) * rexp (- (2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul ((1 : ℝ) / Real.sqrt (2 * π * ↑v))
      simp [lt_of_le_of_ne (zero_le _) (Ne.symm hv)]
    ext x
    simp only [gt_iff_lt, zero_lt_two, zero_le_mul_left, NNReal.zero_le_coe, Real.sqrt_mul',
      one_div, mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul,
      mul_eq_mul_left_iff, Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero,
      NNReal.coe_eq_zero, hv, false_or]
    rw [mul_comm]
    left
    field_simp
  exact Integrable.comp_sub_right hg μ

/-- The gaussian distribution pdf integrates to 1 when the variance is not zero.  -/
lemma lintegral_gaussianPdfReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (gaussianPdfReal μ v x) = 1 := by
  rw [←ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPdfReal μ v) ℙ :=
    (stronglyMeasurable_gaussianPdfReal μ v).aestronglyMeasurable
  have hf : 0 ≤ₐₛ gaussianPdfReal μ v := ae_of_all _ (gaussianPdfReal_nonneg μ v)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPdfReal, gt_iff_lt, zero_lt_two, zero_le_mul_right, ge_iff_le, one_div,
    Nat.cast_ofNat, integral_mul_left]
  rw [integral_sub_right_eq_self (μ := ℙ) (fun a ↦ rexp (-a ^ 2 / ((2 : ℝ) * v))) μ]
  simp only [gt_iff_lt, zero_lt_two, zero_le_mul_right, ge_iff_le, div_eq_inv_mul, mul_inv_rev,
    mul_neg]
  simp_rw [←neg_mul]
  rw [neg_mul, integral_gaussian, ← Real.sqrt_inv, ←Real.sqrt_mul]
  · field_simp
    ring
  · positivity

/-- The gaussian distribution pdf integrates to 1 when the variance is not zero.  -/
lemma integral_gaussianPdfReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPdfReal μ v x = 1 := by
  have h := lintegral_gaussianPdfReal_eq_one μ hv
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPdfReal _ _)
    (ae_of_all _ (gaussianPdfReal_nonneg _ _)), ← ENNReal.ofReal_one] at h
  rwa [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussianPdfReal_nonneg _ _)) zero_le_one]

lemma gaussianPdfReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    gaussianPdfReal μ v (x - y) = gaussianPdfReal (μ + y) v x := by
  simp only [gaussianPdfReal]
  rw [@sub_add_eq_sub_sub_swap]

lemma gaussianPdfReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    gaussianPdfReal μ v (c⁻¹ * x) = |c| * gaussianPdfReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) x := by
  simp only [gaussianPdfReal._eq_1, gt_iff_lt, zero_lt_two, zero_le_mul_left, NNReal.zero_le_coe,
    Real.sqrt_mul', one_div, mul_inv_rev, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_pos]
  rw [← mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  · field_simp
    rw [Real.sqrt_sq_eq_abs]
    ring_nf
    calc (Real.sqrt ↑v)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt π)⁻¹
      = (Real.sqrt ↑v)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt π)⁻¹ * (|c| * |c|⁻¹) := by
          rw [mul_inv_cancel, mul_one]
          simp only [ne_eq, abs_eq_zero, hc, not_false_eq_true]
    _ = (Real.sqrt ↑v)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt π)⁻¹ * |c| * |c|⁻¹ := by ring
  · congr 1
    field_simp
    congr 1
    ring

/-- The pdf of a Gaussian distribution on ℝ with mean `μ` and variance `v`. -/
noncomputable
def gaussianPdf (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gaussianPdfReal μ v x)

lemma gaussianPdf_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPdf μ v = fun x ↦ ENNReal.ofReal (gaussianPdfReal μ v x) := rfl

@[simp]
lemma gaussianPdf_zero_var (μ : ℝ) : gaussianPdf μ 0 = 0 := by
  ext
  simp [gaussianPdf]

lemma gaussianPdf_pos (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : 0 < gaussianPdf μ v x := by
  rw [gaussianPdf, ENNReal.ofReal_pos]
  exact gaussianPdfReal_pos _ _ _ hv

@[measurability]
lemma measurable_gaussianPdf (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPdf μ v) :=
  (measurable_gaussianPdfReal _ _).ennreal_ofReal

@[simp]
lemma lintegral_gaussianPdf_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, gaussianPdf μ v x = 1 :=
  lintegral_gaussianPdfReal_eq_one μ h

end GaussianPdf

section GaussianReal

/-- A Gaussian distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPdf μ v)

@[simp]
lemma gaussianReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v = volume.withDensity (gaussianPdf μ v) := if_neg hv

@[simp]
lemma gaussianReal_zero_var (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := if_pos rfl

instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [h]

lemma gaussianReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) :
    gaussianReal μ v s = ∫⁻ x in s, gaussianPdf μ v x := by
  rw [gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ hs]

lemma gaussianReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPdfReal μ v x) := by
  rw [gaussianReal_apply _ hv hs, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_gaussianPdfReal _ _).restrict
  · exact ae_of_all _ (gaussianPdfReal_nonneg _ _)

lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v ≪ ℙ := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _

lemma gaussianReal_absolutelyContinuous' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ℙ ≪ gaussianReal μ v := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  refine withDensity_absolutelyContinuous' ?_ ?_ ?_
  · exact (measurable_gaussianPdf _ _).aemeasurable
  · exact ae_of_all _ (fun _ ↦ gaussianPdf_pos _ hv _)
  · exact ae_of_all _ (fun _ ↦ ENNReal.ofReal_ne_top)

lemma rnDeriv_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∂(gaussianReal μ v)/∂ℙ =ₐₛ gaussianPdf μ v := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact Measure.rnDeriv_withDensity _ (measurable_gaussianPdf μ v)

end GaussianReal

section Transformations

variable {Ω : Type} [MeasureSpace Ω] {μ : ℝ} {v : ℝ≥0}

lemma _root_.MeasurableEmbedding.gaussianReal_comap_apply (hv : v ≠ 0)
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f)
    {f' : ℝ → ℝ} (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (gaussianReal μ v).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPdfReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPdf_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPdfReal_nonneg _ _)) (integrable_gaussianPdfReal _ _)

lemma _root_.MeasurableEquiv.gaussianReal_map_symm_apply (hv : v ≠ 0) (f : ℝ ≃ᵐ ℝ) {f' : ℝ → ℝ}
    (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (gaussianReal μ v).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPdfReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPdf_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPdfReal_nonneg _ _)) (integrable_gaussianPdfReal _ _)

lemma gaussianReal_map_add_const (y : ℝ) :
    (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v := by
  by_cases hv : v = 0
  · simp only [hv, ne_eq, not_true, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.add_const _) _
  let e : ℝ ≃ᵐ ℝ :=
  { toFun := fun x ↦ x - y
    invFun := fun x ↦ x + y
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp
    measurable_toFun := measurable_id'.add_const _
    measurable_invFun := measurable_id'.add_const _}
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  suffices (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v by exact this
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_neg, abs_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, one_mul, ne_eq]
  rw [gaussianReal_apply_eq_integral _ hv hs']
  simp_rw [gaussianPdfReal_sub _ y]

lemma gaussianReal_add_const {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v)
    (hXm : Measurable X) (y : ℝ) :
    Measure.map (fun ω ↦ X ω + y) ℙ = gaussianReal (μ + y) v := by
  change Measure.map ((fun ω ↦ ω + y) ∘ X) ℙ = gaussianReal (μ + y) v
  rw [← Measure.map_map (measurable_id'.add_const _) hXm, hX, gaussianReal_map_add_const y]

lemma gaussianReal_map_const_mul (c : ℝ) :
    (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  by_cases hv : v = 0
  · simp only [hv, mul_zero, ne_eq, not_true, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.const_mul c) μ
  by_cases hc : c = 0
  · simp only [hc, zero_mul, ne_eq, abs_zero, mul_eq_zero]
    rw [Measure.map_const]
    simp only [ne_eq, measure_univ, one_smul, mul_eq_zero]
    convert (gaussianReal_zero_var 0).symm
    simp only [ne_eq, zero_pow', mul_eq_zero, hv, or_false]
    rfl
  let e : ℝ ≃ᵐ ℝ :=
  { toFun := fun x ↦ c⁻¹ * x
    invFun := fun x ↦ c * x
    left_inv := fun x ↦ by simp [hc]
    right_inv := fun x ↦ by simp [hc]
    measurable_toFun := measurable_id'.const_mul _
    measurable_invFun := measurable_id'.const_mul _}
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  suffices (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) by
    exact this
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, ne_eq, mul_eq_zero]
  rw [gaussianReal_apply_eq_integral _ _ hs']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_eq]
    simp [hc]
  simp_rw [gaussianPdfReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel]
  rwa [ne_eq, abs_eq_zero]

lemma gaussianReal_const_mul {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v)
    (hXm : Measurable X) (c : ℝ) :
    Measure.map (fun ω ↦ c * X ω) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  change Measure.map ((fun ω ↦ c * ω) ∘ X) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v)
  rw [← Measure.map_map (measurable_id'.const_mul c) hXm, hX]
  exact gaussianReal_map_const_mul c

end Transformations


end ProbabilityTheory