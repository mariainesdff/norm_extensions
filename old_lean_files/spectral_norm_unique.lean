import spectral_norm

noncomputable theory

open_locale nnreal

variables {K : Type*} [nontrivially_normed_field K]  [complete_space K] {L : Type*} [hL: field L]
  [algebra K L] (h_alg : algebra.is_algebraic K L)

include hL

lemma spectral_norm.unique' {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) (hf_na : is_nonarchimedean f)
  (hna : is_nonarchimedean (λ k : K, ∥k∥₊)) :
  f = spectral_norm h_alg  := 
begin
  apply eq_of_pow_mult_faithful (normed_field.to_is_mul_norm K) hf_pow hf_alg_norm 
    (spectral_norm.is_pow_mult h_alg hna) (spectral_norm.is_algebra_norm h_alg hna),
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

  have hs_norm : is_norm (λ y : E, spectral_norm h_alg (id2 y : L)) :=
  { zero := by rw [map_zero, subfield.coe_zero, spectral_norm.zero],
    add  := λ a b, by rw [map_add]; exact (spectral_norm.is_algebra_norm h_alg hna).add _ _,
    mul  := λ a b, by simp only [linear_map.coe_mk, id.def, subfield.coe_mul]; 
      exact (spectral_norm.is_algebra_norm h_alg hna).mul _ _,
    ne_zero := λ a ha,
    begin
      apply (spectral_norm.is_algebra_norm h_alg hna).ne_zero,
      simp only [linear_map.coe_mk, id.def, ne.def, add_submonoid_class.coe_eq_zero],
      exact ha,
    end},

  have hs_neg : ∀ y : E, spectral_norm h_alg (id2 (-y) : L) = spectral_norm h_alg (id2 y : L),
  { intro y,
    simp only [linear_map.coe_mk, id.def, subfield.coe_neg],
    exact (spectral_norm.is_nonarchimedean h_alg hna).neg (spectral_norm.zero h_alg) _ },

  letI n1 : normed_ring E := norm_to_normed_ring hs_norm hs_neg,

  letI N1 : normed_space K E := 
  { norm_smul_le := λ k y,
    begin
      change (spectral_norm h_alg (id2 (k • y) : L) : ℝ) ≤ ∥ k ∥ * spectral_norm h_alg (id2 y : L),
      simp only [linear_map.coe_mk, id.def, intermediate_field.coe_smul],
      rw (spectral_norm.is_algebra_norm _ hna).smul,
      exact le_refl _,
    end,
    ..K⟮x⟯.algebra },

  have hf_norm : is_norm (λ y, f((algebra_map K⟮x⟯ L) y)) := 
  { zero := by rw [map_zero, hf_alg_norm.zero],
    add  := λ a b, by rw [map_add]; exact hf_alg_norm.add _ _,
    mul  := λ a b, by rw [map_mul]; exact hf_alg_norm.mul _ _,
    ne_zero := λ a ha, hf_alg_norm.ne_zero _ ((ring_hom.map_ne_zero _).mpr ha) },

  have hf_neg : ∀ y, f((algebra_map K⟮x⟯ L) (-y)) = f((algebra_map K⟮x⟯ L) y),
  { intro y,
    rw map_neg, exact hf_na.neg hf_alg_norm.zero _ },

  letI n2 : normed_ring K⟮x⟯ := norm_to_normed_ring hf_norm hf_neg,

  letI N2 : normed_space K K⟮x⟯ :=
  { norm_smul_le :=  λ k y,
    begin
      change (f ((algebra_map K⟮x⟯ L) (k • y)) : ℝ) ≤ ∥ k ∥ * f (algebra_map K⟮x⟯ L y),
      have : (algebra_map ↥K⟮x⟯ L) (k • y) = k • (algebra_map ↥K⟮x⟯ L y),
      { rw [← is_scalar_tower.algebra_map_smul K⟮x⟯ k y, smul_eq_mul, map_mul, 
          ← is_scalar_tower.algebra_map_apply K ↥K⟮x⟯ L, algebra.smul_def] }, 
      rw [this, hf_alg_norm.smul],
      exact le_refl _,
    end,
    ..K⟮x⟯.algebra },

  haveI hKx_fin : finite_dimensional K ↥K⟮x⟯ := intermediate_field.adjoin.finite_dimensional 
    (is_algebraic_iff_is_integral.mp (h_alg x)),
  haveI : finite_dimensional K E := hKx_fin,

  set Id1 : K⟮x⟯ →L[K] E := ⟨id1, id1.continuous_of_finite_dimensional⟩ with hId1,
  set Id2 : E →L[K] K⟮x⟯ := ⟨id2, id2.continuous_of_finite_dimensional⟩ with hId2,
 
  have hC1 : ∃ (C1 : ℝ), 0 < C1 ∧ ∀ (y : K⟮x⟯), ∥id1 y∥ ≤ C1 * ∥y∥ := Id1.is_bounded_linear_map.bound,
  have hC2 : ∃ (C2 : ℝ), 0 < C2 ∧ ∀ (y : E), ∥id2 y∥ ≤ C2 * ∥y∥ := Id2.is_bounded_linear_map.bound,

  obtain ⟨C1, hC1_pos, hC1⟩ := hC1,
  obtain ⟨C2, hC2_pos, hC2⟩ := hC2,
  use [⟨C2, le_of_lt hC2_pos⟩, ⟨C1, le_of_lt hC1_pos⟩, hC2_pos, hC1_pos],
  rw forall_and_distrib,
  --simp only at hC1 hC2,
  split,
  { intro y, exact hC2 ⟨y, (intermediate_field.algebra_adjoin_le_adjoin K _) y.2⟩ },
  { intro y, exact hC1 ⟨y, (intermediate_field.algebra_adjoin_le_adjoin K _) y.2⟩ },

end

lemma spectral_norm.unique_field_norm_ext {f : L → nnreal}
  (hf_field_norm : is_mul_norm f) (hf_ext : function_extends (λ x : K, ∥x∥₊) f)
  (hf_na : is_nonarchimedean f) (hna : is_nonarchimedean (λ k : K, ∥k∥₊)) (x : L) :
  f x = spectral_norm h_alg x := 
begin
  have hf_pow : is_pow_mult f := is_mul_norm.to_is_pow_mult hf_field_norm,
  have hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f := 
  { smul := λ k x, by rw [algebra.smul_def, hf_field_norm.mul_eq, hf_ext k],
    ..hf_field_norm},
  rw spectral_norm.unique' h_alg hf_pow hf_alg_norm hf_na hna
end

lemma spectral_norm.is_mul_norm (hna : is_nonarchimedean (λ k : K, ∥k∥₊)) : 
  is_mul_norm (spectral_norm h_alg) :=
{ mul_eq := λ x y, begin
    by_cases hx : 0 = spectral_norm h_alg x,
    { rw [← hx, zero_mul],
      rw [eq_comm, (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.zero_iff] at hx,
      rw [hx, zero_mul, (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.zero] },
    { set f := c_seminorm (spectral_norm.is_norm_le_one_class h_alg) hx
        (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg hna) with hf,
      have hf_pow : is_pow_mult f := c_seminorm_is_pow_mult (spectral_norm.is_norm_le_one_class 
        h_alg) hx (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg hna),
      have hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f := 
      { smul := λ k y,
        begin
          rw [← spectral_norm.extends h_alg, algebra.smul_def, hf],
          have h_mul : ∀ (y : L), spectral_norm h_alg ((algebra_map K L k) * y) = 
            spectral_norm h_alg (algebra_map K L k) * spectral_norm h_alg y,
          { intro y, rw [spectral_norm.extends h_alg, ← algebra.smul_def],
            exact (spectral_norm.is_algebra_norm h_alg hna).smul _ _ },
          rw ← c_seminorm_apply_of_is_mult _ _ _ _ h_mul,
          exact c_seminorm_is_mult_of_is_mult _ _ _ _ h_mul _,
        end,
        ..(c_seminorm_is_norm _ _ _ _ _) },
      have hf_na : is_nonarchimedean f := 
      c_seminorm_is_nonarchimedean _ _ _ _ (spectral_norm.is_nonarchimedean h_alg hna),
      rw [← spectral_norm.unique' h_alg hf_pow hf_alg_norm hf_na hna],
      rw [hf, c_seminorm_c_is_mult (spectral_norm.is_norm_le_one_class h_alg) hx
        (spectral_norm.is_algebra_norm h_alg hna).to_is_norm.to_is_seminorm
        (spectral_norm.is_pow_mult h_alg hna)] }
  end
  ..spectral_norm.is_algebra_norm h_alg hna }

def spectral_norm.normed_field (h : is_nonarchimedean (λ k : K, ∥k∥₊)) : normed_field L := 
{ norm      := λ (x : L), (spectral_norm h_alg x : ℝ),
  dist      := λ (x y : L), (spectral_norm h_alg (x - y) : ℝ),
  dist_self := λ x, by simp only [sub_self, nnreal.coe_eq_zero, spectral_norm.zero],
  dist_comm := λ x y, by rw [nnreal.coe_eq, ← neg_sub, spectral_norm.neg h_alg h],
  dist_triangle := λ x y z, begin
    simp only [dist_eq_norm],
    rw ← sub_add_sub_cancel x y z,
    exact add_le_of_is_nonarchimedean (spectral_norm.zero h_alg)
      (spectral_norm.is_nonarchimedean h_alg h) _ _,
  end,
  eq_of_dist_eq_zero := λ x y hxy,
  begin
    simp only [nnreal.coe_eq_zero] at hxy,
    rw ← sub_eq_zero,
    rw is_norm.zero_iff (spectral_norm.is_mul_norm h_alg h).to_is_norm at hxy,
    exact hxy,
  end,
  dist_eq := λ x y, by refl,
  norm_mul' := λ x y,
  begin
    simp only [← nnreal.coe_mul, nnreal.coe_eq],
    exact (spectral_norm.is_mul_norm h_alg h).mul_eq x y,
  end,
  ..hL }

/- noncomputable! instance us : uniform_space L := infer_instance

instance spectral_norm.complete_space (h_fin : @finite_dimensional K L _ _ _) :
  complete_space L := sorry -/
