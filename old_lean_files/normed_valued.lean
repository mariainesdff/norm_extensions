import rank_one_valuation
import seminormed_rings
import analysis.special_functions.pow
--import analysis.normed.field.basic
--import ring_theory.algebraic
import topology.algebra.valuation

noncomputable theory

open_locale nnreal

variables {K : Type*} [hK : normed_field K]
include hK

/- class is_nonarchimedean' {α : Type*} [add_group α] (f : α → ℝ≥0) : Prop := 
(add_le : ∀ a b, f (a + b) ≤ max (f a) (f b)) -/

def valuation_from_norm (h : is_nonarchimedean nnnorm) : valuation K ℝ≥0 := 
{ to_fun    := nnnorm,
  map_zero' := nnnorm_zero,
  map_one'  := nnnorm_one,
  map_mul'  := nnnorm_mul,
  map_add_le_max' := λ x y, h.add_le nnnorm_zero x y, }

lemma valuation_from_norm_apply (h : is_nonarchimedean nnnorm) (x : K):
  valuation_from_norm h x = ∥ x ∥₊ := rfl

instance foo : normed_add_comm_group K := non_unital_normed_ring.to_normed_add_comm_group

def normed_field.to_valued (h : is_nonarchimedean (nnnorm : K → ℝ≥0)) : valued K ℝ≥0 :=
{ v := valuation_from_norm h,
  is_topological_valuation := λ U,
  begin
    rw metric.mem_nhds_iff,
    refine ⟨λ h, _, λ h, _⟩, 
    { obtain ⟨ε, hε, h⟩ := h,
      use units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε),
      intros x hx,
      exact h (mem_ball_zero_iff.mpr hx) },
    { obtain ⟨ε, hε⟩ := h,
      use [(ε : ℝ), nnreal.coe_pos.mpr (units.zero_lt _)],
      intros x hx,
      exact hε  (mem_ball_zero_iff.mp hx) },
  end,
  ..hK.to_uniform_space,
  ..non_unital_normed_ring.to_normed_add_comm_group }

omit hK

variables {L : Type*} [hL : field L] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
  [val : valued L Γ₀] [hv : is_rank_one val.v]
include hL val hv

def norm_def {e : ℝ} (he0 : 0 < e)  : L → ℝ :=
λ x : L, mult_with_top_R_to_R_monoid_with_zero_hom he0 (is_rank_one_hom val.v (valued.v x))

lemma norm_def_nonneg {e : ℝ} (he0 : 0 < e) (x : L) : 0 ≤ norm_def he0 x := 
begin
  simp only [norm_def, mult_with_top_R_to_R_monoid_with_zero_hom, monoid_with_zero_hom.coe_mk,
    mult_with_top_R_to_R],
  split_ifs,
  { exact le_refl _ },
  { exact real.rpow_nonneg_of_nonneg (le_of_lt he0) _ }
end

lemma norm_def_add_le {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (x y : L) : 
  norm_def he0 (x + y) ≤ max (norm_def he0 x) (norm_def he0 y) := 
begin
  simp only [norm_def, mult_with_top_R_to_R_monoid_with_zero_hom, monoid_with_zero_hom.coe_mk],
  rw le_max_iff,
  simp only [strict_mono.le_iff_le (mult_with_top_R_to_R_strict_mono he0 he1),
    strict_mono.le_iff_le (is_rank_one_strict_mono val.v)],
  rw ← le_max_iff,
  exact valuation.map_add_le_max' val.v _ _,
end

lemma norm_def_eq_zero  {e : ℝ} (he0 : 0 < e) {x : L} (hx : norm_def he0 x = 0) : x = 0 :=
begin
  simp only [norm_def, mult_with_top_R_to_R_monoid_with_zero_hom, monoid_with_zero_hom.coe_mk,
    mult_with_top_R_to_R] at hx,
  split_ifs at hx with h0 hn0,
  { rw [← order_dual.of_dual_bot, order_dual.of_dual_inj,  ← to_add_of_add ⊥,
      function.injective.eq_iff multiplicative.to_add.injective, ← order_dual.of_dual_top] at h0,
    exact (valuation.zero_iff _).mp (is_rank_one_hom_zero valued.v h0), },
  { rw real.rpow_eq_zero_iff_of_nonneg (le_of_lt he0) at hx,
    exact absurd hx.1 (ne_of_gt he0) },
end

def valued_field.to_normed_field {e : ℝ} (he0 : 0 < e) (he1 : e < 1) : normed_field L := 
{ norm               := norm_def he0,
  dist               := λ x y, norm_def he0 (x - y),
  dist_self          := λ x,
  begin
    simp only [sub_self, norm_def, valuation.map_zero, (is_rank_one_hom val.v).map_zero],
    exact (mult_with_top_R_to_R_monoid_with_zero_hom he0).map_zero',
  end,
  dist_comm          := λ x y, by { simp only [norm_def], rw [← neg_sub, valuation.map_neg] },
  dist_triangle      := λ x y z, 
  begin
    simp only [← sub_add_sub_cancel x y z],
    exact le_trans (norm_def_add_le he0 he1 _ _)
      (max_le_add_of_nonneg (norm_def_nonneg he0 _) (norm_def_nonneg he0 _)),
  end,
  eq_of_dist_eq_zero := λ x y hxy, eq_of_sub_eq_zero (norm_def_eq_zero he0 hxy),
  dist_eq            := λ x y, rfl,
  norm_mul'          := λ x y, by simp only [norm_def, map_mul],
  to_uniform_space := valued.to_uniform_space,
  uniformity_dist := sorry,
  ..hL, }