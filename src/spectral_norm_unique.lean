import pow_mult_faithful
import seminorm_from_const
import spectral_norm

noncomputable theory

open_locale nnreal

variables {K : Type*} [nontrivially_normed_field K] [complete_space K] {L : Type*} [hL: field L]
  [algebra K L] (h_alg : algebra.is_algebraic K L)

include hL

lemma spectral_norm.unique' {f : algebra_norm K L} (hf_pm : is_pow_mul f)
  (hf_na : is_nonarchimedean f) (hna : is_nonarchimedean (norm : K → ℝ)) :
  f = spectral_alg_norm h_alg hna := 
begin
  apply eq_of_pow_mult_faithful f hf_pm _
    (spectral_alg_norm_is_pow_mul h_alg hna),
  intro x,
  set E : Type* := id K⟮x⟯ with hEdef,
  letI hE : field E := (by rw [hEdef, id.def] ; apply_instance),
  letI : algebra K E := K⟮x⟯.algebra,

  set id1 : K⟮x⟯ →ₗ[K] E := 
  { to_fun := id,
    map_add' := λ x y, rfl,
    map_smul' := λ r x, rfl, },

  set id2 : E →ₗ[K] K⟮x⟯ := 
  { to_fun := id,
    map_add' := λ x y, rfl,
    map_smul' := λ r x, rfl },

  set hs_norm : ring_norm E:=
  { to_fun    := (λ y : E, spectral_norm h_alg (id2 y : L)),
    map_zero' := by rw [map_zero, subfield.coe_zero, spectral_norm_zero],
    add_le'   := λ a b, 
    by simp only [← spectral_alg_norm_def _ hna,subfield.coe_add]; exact map_add_le_add _ _ _, 
    neg'      := λ a, 
      by simp only [← spectral_alg_norm_def _ hna, subfield.coe_neg, map_neg, map_neg_eq_map],
    mul_le'  := λ a b, 
    by simp only [← spectral_alg_norm_def _ hna, subfield.coe_mul]; exact map_mul_le_mul _ _ _,
    eq_zero_of_map_eq_zero' := λ a ha,
    begin
      simp only [←spectral_alg_norm_def _ hna, linear_map.coe_mk, id.def, map_eq_zero_iff_eq_zero,
        algebra_map.lift_map_eq_zero_iff] at ha,
      exact ha,
    end },

  letI n1 : normed_ring E := norm_to_normed_ring hs_norm,

  letI N1 : normed_space K E := 
  { norm_smul_le := λ k y,
    begin
      change (spectral_alg_norm h_alg hna (id2 (k • y) : L) : ℝ) ≤ 
        ‖ k ‖ * spectral_alg_norm h_alg hna (id2 y : L),
      simp only [linear_map.coe_mk, id.def, intermediate_field.coe_smul, map_smul_eq_mul],
    end,
    ..K⟮x⟯.algebra },

  set hf_norm : ring_norm K⟮x⟯ := 
  { to_fun := λ y, f((algebra_map K⟮x⟯ L) y),
    map_zero' := map_zero _,
    add_le'  := λ a b, map_add_le_add _ _ _,
    neg' := λ y, by { simp only [map_neg, map_neg_eq_map] },
    mul_le'  := λ a b, map_mul_le_mul _ _ _,
    eq_zero_of_map_eq_zero' := λ a ha,
    begin
      simp only [map_eq_zero_iff_eq_zero, map_eq_zero] at ha,
      exact ha
    end },

  letI n2 : normed_ring K⟮x⟯ := norm_to_normed_ring hf_norm,

  letI N2 : normed_space K K⟮x⟯ :=
  { norm_smul_le :=  λ k y,
    begin
      change (f ((algebra_map K⟮x⟯ L) (k • y)) : ℝ) ≤ ‖ k ‖ * f (algebra_map K⟮x⟯ L y),
      have : (algebra_map ↥K⟮x⟯ L) (k • y) = k • (algebra_map ↥K⟮x⟯ L y),
      { rw [← is_scalar_tower.algebra_map_smul K⟮x⟯ k y, smul_eq_mul, map_mul, 
          ← is_scalar_tower.algebra_map_apply K ↥K⟮x⟯ L, algebra.smul_def] }, 
      rw [ this, map_smul_eq_mul],
    end,
    ..K⟮x⟯.algebra },

  haveI hKx_fin : finite_dimensional K ↥K⟮x⟯ := intermediate_field.adjoin.finite_dimensional 
    (is_algebraic_iff_is_integral.mp (h_alg x)),
  haveI : finite_dimensional K E := hKx_fin,

  set Id1 : K⟮x⟯ →L[K] E := ⟨id1, id1.continuous_of_finite_dimensional⟩ with hId1,
  set Id2 : E →L[K] K⟮x⟯ := ⟨id2, id2.continuous_of_finite_dimensional⟩ with hId2,
 
  have hC1 : ∃ (C1 : ℝ), 0 < C1 ∧ ∀ (y : K⟮x⟯), ‖ id1 y ‖ ≤ C1 * ‖ y ‖ := 
  Id1.is_bounded_linear_map.bound,
  have hC2 : ∃ (C2 : ℝ), 0 < C2 ∧ ∀ (y : E), ‖ id2 y ‖ ≤ C2 * ‖ y ‖ := 
  Id2.is_bounded_linear_map.bound,

  obtain ⟨C1, hC1_pos, hC1⟩ := hC1,
  obtain ⟨C2, hC2_pos, hC2⟩ := hC2,
  use [C2, C1, hC2_pos, hC1_pos],
  rw forall_and_distrib,
  split,
  { intro y, exact hC2 ⟨y, (intermediate_field.algebra_adjoin_le_adjoin K _) y.2⟩ },
  { intro y, exact hC1 ⟨y, (intermediate_field.algebra_adjoin_le_adjoin K _) y.2⟩ },
end

lemma spectral_norm.unique_field_norm_ext {f : mul_ring_norm L} 
  (hf_ext : function_extends (norm : K → ℝ) f) (hf_na : is_nonarchimedean f) 
  (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) :
  f x = spectral_norm h_alg x := 
begin
  set g : algebra_norm K L := 
  { smul' := λ k x, by simp only [mul_ring_norm.to_fun_eq_coe, algebra.smul_def, map_mul, hf_ext k],
    mul_le' := λ x y, by simp only [mul_ring_norm.to_fun_eq_coe, map_mul_le_mul], 
    ..f },
  have hg_pow : is_pow_mul g := mul_ring_norm.is_pow_mul _,
  have hgx : f x = g x := rfl,
  rw [hgx, spectral_norm.unique' h_alg hg_pow hf_na hna], refl,
end

def alg_norm_from_const (hna : is_nonarchimedean (norm : K → ℝ)) 
  (h1 : (spectral_alg_norm h_alg hna).to_ring_seminorm 1 ≤ 1) {x : L}
  (hx : 0 ≠ spectral_alg_norm h_alg hna x) : 
  algebra_norm K L  :=
{ smul' := λ k y,
  begin
    have h_mul : ∀ (y : L), spectral_norm h_alg ((algebra_map K L k) * y) = 
      spectral_norm h_alg (algebra_map K L k) * spectral_norm h_alg y,
    { intro y, 
      rw [spectral_norm.extends h_alg, ← algebra.smul_def,
        ← spectral_alg_norm_def h_alg hna, map_smul_eq_mul _ _ _],
      refl, },
    have h : spectral_norm h_alg (algebra_map K L k) = 
      seminorm_from_const h1 hx (spectral_norm_is_pow_mul h_alg hna) (algebra_map K L k),
    {  rw seminorm_from_const_apply_of_is_mul h1 hx _ h_mul, refl, }, 
    simp only [ring_norm.to_fun_eq_coe, seminorm_from_const_ring_norm_of_field_def],
    rw [← spectral_norm.extends h_alg, algebra.smul_def, h],
    exact seminorm_from_const_is_mul_of_is_mul _ _ _ h_mul _,
  end,
  ..(seminorm_from_const_ring_norm_of_field h1 hx.symm (spectral_alg_norm_is_pow_mul h_alg hna)) }

lemma alg_norm_from_const_def (hna : is_nonarchimedean (norm : K → ℝ)) 
  (h1 : (spectral_alg_norm h_alg hna).to_ring_seminorm 1 ≤ 1) {x y : L}
  (hx : 0 ≠ spectral_alg_norm h_alg hna x) : 
  alg_norm_from_const h_alg hna h1 hx y = 
    seminorm_from_const h1 hx (spectral_norm_is_pow_mul h_alg hna) y := 
rfl

def spectral_mul_alg_norm (hna : is_nonarchimedean (norm : K → ℝ)) : 
  mul_algebra_norm K L  :=
{ map_one' := spectral_alg_norm_is_norm_one_class h_alg hna,
  map_mul' := λ x y, begin
  simp only [algebra_norm.to_fun_eq_coe],
    by_cases hx : spectral_alg_norm h_alg hna x = 0,
    { rw [hx, zero_mul],
      rw [map_eq_zero_iff_eq_zero] at hx ⊢,
      rw [hx, zero_mul],  },
    { have hf1 : (spectral_alg_norm h_alg hna).to_ring_seminorm 1 ≤ 1 := 
      spectral_alg_norm_is_norm_le_one_class h_alg hna,
      set f : algebra_norm K L := alg_norm_from_const h_alg hna hf1 (ne.symm hx) with hf,
      have hf_pow : is_pow_mul f := seminorm_from_const_is_pow_mul hf1 (ne.symm hx)
        (spectral_norm_is_pow_mul h_alg hna),
      have hf_na : is_nonarchimedean f := 
      seminorm_from_const_is_nonarchimedean _ _ _ (spectral_norm_is_nonarchimedean h_alg hna),
      rw [← spectral_norm.unique' h_alg hf_pow hf_na, hf],
      simp only [alg_norm_from_const_def],
      exact seminorm_from_const_c_is_mul _ _ _ _, }
  end,
  ..spectral_alg_norm h_alg hna }

lemma spectral_mul_ring_norm_def (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) : 
  spectral_mul_alg_norm h_alg hna x = spectral_norm h_alg x := 
rfl

def spectral_norm_to_normed_field (h : is_nonarchimedean (norm : K → ℝ)) : normed_field L := 
{ norm      := λ (x : L), (spectral_norm h_alg x : ℝ),
  dist      := λ (x y : L), (spectral_norm h_alg (x - y) : ℝ),
  dist_self := λ x, by { simp only [sub_self, spectral_norm_zero] },
  dist_comm := λ x y, by { simp only [dist], rw [← neg_sub, spectral_norm_neg h_alg h] },
  dist_triangle := λ x y z, begin
    simp only [dist_eq_norm],
    rw ← sub_add_sub_cancel x y z,
    exact add_le_of_is_nonarchimedean (spectral_norm_nonneg h_alg)
      (spectral_norm_is_nonarchimedean h_alg h) _ _, 
  end,
  eq_of_dist_eq_zero := λ x y hxy,
  begin
    simp only [← spectral_mul_ring_norm_def _ h] at hxy,
    rw ← sub_eq_zero,
    exact mul_algebra_norm.eq_zero_of_map_eq_zero' _ _ hxy,
  end,
  dist_eq := λ x y, by refl,
  norm_mul' := λ x y, by { simp only [← spectral_mul_ring_norm_def _ h], exact map_mul _ _ _ },
  ..hL }

def spectral_norm_to_normed_add_comm_group (h_alg : algebra.is_algebraic K L)
  (h : is_nonarchimedean (norm : K → ℝ)) : normed_add_comm_group L := 
begin
  haveI : normed_field L := spectral_norm_to_normed_field h_alg h,
  apply_instance,
end

def spectral_norm_to_seminormed_add_comm_group (h_alg : algebra.is_algebraic K L)
  (h : is_nonarchimedean (norm : K → ℝ)) : seminormed_add_comm_group L := 
begin
  haveI : normed_field L := spectral_norm_to_normed_field h_alg h,
  apply_instance,
end

noncomputable! def spectral_norm_to_normed_space (h_alg : algebra.is_algebraic K L)
  (h : is_nonarchimedean (norm : K → ℝ)) : 
  @normed_space K L _ (spectral_norm_to_seminormed_add_comm_group h_alg h) := 
{ norm_smul_le := λ r x,
  begin
    change spectral_alg_norm h_alg h (r • x) ≤ ‖ r ‖*(spectral_alg_norm h_alg h x),
    exact le_of_eq (map_smul_eq_mul _ _ _),
  end,
  ..(infer_instance : module K L) }

def ms (h : is_nonarchimedean (norm : K → ℝ)) : metric_space L := 
(spectral_norm_to_normed_field h_alg h).to_metric_space

def us (h : is_nonarchimedean (norm : K → ℝ)) : 
  uniform_space L := (ms h_alg h).to_uniform_space -- normed_field.to_uniform_space

noncomputable! instance spectral_norm_complete_space (h : is_nonarchimedean (norm : K → ℝ)) 
  (h_fin : finite_dimensional K L) : @complete_space L (us h_alg h) := 
@finite_dimensional.complete K _ L (spectral_norm_to_normed_add_comm_group h_alg h) 
    (spectral_norm_to_normed_space h_alg h) _ h_fin
