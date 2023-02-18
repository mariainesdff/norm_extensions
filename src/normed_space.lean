/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.normed_space.bounded_linear_maps
import ring_seminorm
import seminorm_from_bounded
import smoothing_seminorm

/-!
# 

In this file, we prove [BGR, Lemma 3.2.1./3]: if `K` is a normed field with a nonarchimedean 
power-multiplicative norm and `L/K` is a finite extension, then there exists at least one
power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions
* `basis.norm` : the function sending an element `x : L` to the maximum of the norms of its 
  coefficients with respect to the `K`-basis `B` of `L`.


## Main Results
* `alg_norm_of_auto_is_pow_mul` : `alg_norm_of_auto` is power-multiplicative.
* `alg_norm_of_auto_is_nonarchimedean` : `alg_norm_of_auto` is nonarchimedean.
* `alg_norm_of_auto_extends` : `alg_norm_of_auto` extends the norm on `K`.
* `alg_norm_of_galois_is_pow_mul` : `alg_norm_of_galois` is power-multiplicative.
* `alg_norm_of_galois_is_nonarchimedean` : `alg_norm_of_galois` is nonarchimedean.
* `finite_extension_pow_mul_seminorm` : the proof of [BGR, Lemma 3.2.1./3].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

basis.norm, nonarchimedean
-/

noncomputable theory

open finset

open_locale big_operators

section continuous

/-- A continuous linear map between normed spaces. -/
structure is_continuous_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] (f : E → F)
  extends is_linear_map 𝕜 f : Prop :=
(cont : continuous f . tactic.interactive.continuity')

/-- A linear map between normed spaces is continuous if and only if it is bounded,-/
lemma is_continuous_linear_map_iff_is_bounded_linear_map {K : Type*} [nontrivially_normed_field K]
  {M : Type*} [normed_add_comm_group M] [normed_space K M] {N : Type*} [normed_add_comm_group N] 
  [normed_space K N] (f : M → N) : is_continuous_linear_map K f ↔ is_bounded_linear_map K f :=
begin
  refine ⟨λ h_cont, _, λ h_bdd, ⟨h_bdd.to_is_linear_map, h_bdd.continuous⟩⟩,
  { set F : M →L[K] N :=
    by use [f, is_linear_map.map_add h_cont.1, is_linear_map.map_smul h_cont.1, h_cont.2],
    exact continuous_linear_map.is_bounded_linear_map F, },
end

end continuous

section finsum

/-- Given a function `f : α → M` and a linear equivalence `g : M ≃ₛₗ[σ] N`, we have
  `g ∑ᶠ f i = ∑ᶠ g(f i)`.  -/
theorem linear_equiv.map_finsum {R S : Type*} {α : Sort*} [semiring R] [semiring S] (σ : R →+* S)
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ] (M N : Type*) [add_comm_monoid M]
  [add_comm_monoid N] [module R M] [module S N] (g : M ≃ₛₗ[σ] N) (f : α → M) :
  g (finsum (λ (i : α), f i)) = finsum (λ (i : α), g (f i)) := 
add_equiv.map_finsum g.to_add_equiv f

/-- Given a fintype `α`, a function `f : α → M` and a linear equivalence `g : M ≃ₛₗ[σ] N`, we have
  `g (∑ (i : α), f i) = ∑ (i : α), g (f i)`.  -/
theorem linear_equiv.map_finset_sum {R S : Type*} {α : Sort*} [fintype α] [semiring R] [semiring S] 
  (σ : R →+* S) {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ] (M N : Type*)
  [add_comm_monoid M] [add_comm_monoid N] [module R M] [module S N] (g : M ≃ₛₗ[σ] N)
  (f : α → M) : g (∑ (i : α), f i) = ∑ (i : α), g (f i) := 
by simp only [← finsum_eq_sum_of_fintype, linear_equiv.map_finsum]


theorem finsum_apply {α : Type*} {β : α → Type*} {γ : Type*} [finite γ]
  [Π (a : α), add_comm_monoid (β a)] (a : α) (g : γ → Π (a : α), β a) :
  finsum (λ (c : γ), g c) a = finsum (λ (c : γ), g c a) := 
begin
  casesI nonempty_fintype γ,
  simp only [finsum_eq_sum_of_fintype, sum_apply]
end

/-- If `∑ i, f i • v i = ∑ i, g i • v i`, then for all `i`, `f i = g i`. -/
lemma linear_independent.eq_coords_of_eq {R : Type*} [ring R] {M : Type*} [add_comm_group M] 
  [module R M] {ι : Type*} [fintype ι] {v : ι → M} (hv : linear_independent R v) {f : ι → R} 
  {g : ι → R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := 
begin
  rw [← sub_eq_zero, ← sum_sub_distrib] at heq,
  simp_rw ← sub_smul at heq,
  rw linear_independent_iff' at hv,
  exact sub_eq_zero.mp (hv univ (λ i, (f i - g i)) heq i (mem_univ i)),
end

end finsum

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]

/-- If `B` is a basis of the `K`-vector space `L` such that `B i = 1` for some index `i`, then
each `k:K` gets represented as `k • B i` as an element of `L`. -/
lemma basis_one {ι : Type*} [fintype ι] [decidable_eq ι] {B : basis ι K L} {i : ι}
  (hBi : B i = (1 : L)) (k : K) :
  B.equiv_fun ((algebra_map K L) k) = λ (j : ι), if (j = i) then k else 0 := 
begin
  ext j,
  apply linear_independent.eq_coords_of_eq B.linear_independent,
  rw basis.sum_equiv_fun B (algebra_map K L k),
  have h_sum : ∑ (j : ι), ite (j = i) k 0 • B j = ∑ (j : ι), ite (j = i) (k • B j) 0,
  { apply sum_congr (eq.refl _),
    { rintros h -,
      split_ifs,
      exacts [rfl, zero_smul _ _] }},
  rw [h_sum, algebra.algebra_map_eq_smul_one, sum_ite_eq' univ (i : ι) (λ j : ι, k • B j)],
  simp only [mem_univ, if_true, hBi],
end

namespace basis

/-- The function sending an element `x : L` to the maximum of the norms of its coefficients
  with respect to the `K`-basis `B` of `L`.-/
def norm {ι : Type*} [fintype ι] [nonempty ι] (B : basis ι K L) : L → ℝ := 
λ x, ‖B.equiv_fun x (classical.some (finite.exists_max (λ i : ι, ‖B.equiv_fun x i‖ )))‖

/-- The norm of a coefficient `x_i` is less than or equal to the norm of `x`. -/
lemma le_norm {ι : Type*} [fintype ι] [nonempty ι] (B : basis ι K L) (x : L) (i : ι) :
  ‖B.equiv_fun x i‖ ≤ B.norm x := 
classical.some_spec (finite.exists_max (λ i : ι, ‖B.equiv_fun x i‖)) i

/-- For any `K`-basis of `L`, we have `B.norm 0 = 0`. -/
lemma norm_zero' {ι : Type*} [fintype ι] [nonempty ι] (B : basis ι K L) :  B.norm 0 = 0 :=
by simp only [norm, map_zero, pi.zero_apply, norm_zero]

/-- For any `K`-basis of `L`, and any `x : L`, we have `B.norm (-x) = B.norm x`. -/
lemma norm_neg {ι : Type*} [fintype ι] [nonempty ι] (B : basis ι K L) (x : L) :
  B.norm (-x) = B.norm x :=
begin
  simp only [norm, map_neg],
  convert norm_neg _,
  ext x, simp only [pi.neg_apply, norm_neg]
end

/-- For any `K`-basis of `L`, `B.norm` extends the norm on `K`. -/
lemma norm_extends {ι : Type*} [fintype ι] [nonempty ι] {B : basis ι K L}
  {i : ι} (hBi : B i = (1 : L)) :
  function_extends (λ x : K, ‖x‖) B.norm :=
begin
  classical,
  intro k,
  { by_cases hk : k = 0,
  { simp only [hk, map_zero, norm_zero, norm_zero'] },
  { simp only [norm, basis_one hBi],
    have h_max : (classical.some (finite.exists_max (λ j : ι, 
      ‖(λ (n : ι), if (n = i) then k else 0) j ‖))) = i,
    { by_contradiction h,
      have h_max := classical.some_spec (finite.exists_max (λ j : ι, 
        ‖(λ (n : ι), if (n = i) then k else 0) j ‖)),
      simp only [if_neg h] at h_max,
      specialize h_max i,
      rw [if_pos rfl, norm_zero, norm_le_zero_iff] at h_max,
      exact hk h_max },
    rw if_pos h_max }} 
end

/-- For any `K`-basis of `L`, if the norm on `K` is nonarchimedean, then so is `B.norm`. -/
lemma norm_is_nonarchimedean {ι : Type*} [fintype ι] [nonempty ι] {B : basis ι K L}
  (hna : is_nonarchimedean (has_norm.norm : K → ℝ)) : is_nonarchimedean B.norm  :=
begin
  classical,
  intros x y,
  simp only [basis.norm],
  set ixy := classical.some (finite.exists_max (λ i : ι, ‖B.equiv_fun (x + y) i‖)) with hixy_def,
  have hxy : ‖B.equiv_fun (x + y) ixy‖ ≤ max (‖B.equiv_fun x ixy‖) (‖B.equiv_fun y ixy‖),
  { rw [linear_equiv.map_add, pi.add_apply], exact hna _ _ },
  have hix := classical.some_spec (finite.exists_max (λ i : ι, ‖B.equiv_fun x i‖)),
  have hiy := classical.some_spec (finite.exists_max (λ i : ι, ‖B.equiv_fun y i‖)),
  cases le_max_iff.mp hxy with hx hy,
  { apply le_max_of_le_left (le_trans hx (hix ixy)) },
  { apply le_max_of_le_right (le_trans hy (hiy ixy)) },
end

/-- For any `K`-basis of `L`, `B.norm` is bounded with respect to multiplication. That is, 
  `∃ (c : ℝ), c > 0` such that ` ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y`. -/
lemma norm_is_bdd {ι : Type*} [fintype ι] [nonempty ι] {B : basis ι K L} {i : ι} 
  (hBi : B i = (1 : L)) (hna : is_nonarchimedean (has_norm.norm : K → ℝ)) : 
  ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y :=
begin
  classical,
  -- The bounding constant `c` will be the maximum of the products `B.norm (B i * B j)`.
  set c := classical.some (finite.exists_max (λ (i : ι × ι), B.norm (B i.1 * B i.2))) with hc_def,
  have hc := classical.some_spec (finite.exists_max (λ (i : ι × ι), B.norm (B i.1 * B i.2))),
  use B.norm (B c.1 * B c.2),
  split,
  -- `B c.1 * B c.2` is positive
  {  have h_pos : (0 : ℝ) < B.norm (B i * B i),
    { have h1 : (1 : L) = (algebra_map K L) 1 := by rw map_one,
      rw [hBi, mul_one, h1, basis.norm_extends hBi],
      simp only [norm_one, zero_lt_one] },
    exact lt_of_lt_of_le h_pos (hc (i, i)) },
  -- ∀ (x y : L), B.norm (x * y) ≤ B.norm (⇑B c.fst * ⇑B c.snd) * B.norm x * B.norm y 
  { intros x y,
    -- `ixy` is an index for which `‖B.equiv_fun (x*y) i‖` is maximum.
    set ixy := classical.some (finite.exists_max (λ i : ι, ‖B.equiv_fun (x*y) i‖)) with hixy_def,
    -- We rewrite the LHS using `ixy`.
    conv_lhs{ simp only [basis.norm],
      rw [← hixy_def, ← basis.sum_equiv_fun B x, ← basis.sum_equiv_fun B y] },
    rw [sum_mul, linear_equiv.map_finset_sum, sum_apply],
    simp_rw [smul_mul_assoc, linear_equiv.map_smul, mul_sum,
      linear_equiv.map_finset_sum, mul_smul_comm, linear_equiv.map_smul],
    /- Since the norm is nonarchimidean, the norm of a finite sum is bounded by the maximum of the
      norms of the summands. -/
    have hna' : is_nonarchimedean (normed_field.to_mul_ring_norm K) := hna, 
    have hk : ∃ (k : ι) (hk : univ.nonempty → k ∈ univ),
     ‖∑ (i : ι), 
       (B.equiv_fun x i • ∑ (i_1 : ι), B.equiv_fun y i_1 • B.equiv_fun (B i * B i_1)) ixy‖ ≤ 
     ‖ (B.equiv_fun x k • ∑ (j : ι),  B.equiv_fun y j • B.equiv_fun (B k * B j)) ixy‖ :=
    is_nonarchimedean_finset_image_add hna'
        (λ i, (B.equiv_fun x i • ∑ (i_1 : ι), B.equiv_fun y i_1 • B.equiv_fun (B i * B i_1)) ixy) 
        (univ : finset ι),
    obtain ⟨k, -, hk⟩ := hk,
    apply le_trans hk,
    -- We use the above property again.
    have hk' :  ∃ (k' : ι) (hk' : univ.nonempty → k' ∈ univ), 
      ‖∑ (j : ι), B.equiv_fun y j • B.equiv_fun (B k * B j) ixy‖ ≤ 
      ‖B.equiv_fun y k' • B.equiv_fun (B k * B k') ixy‖ := 
    is_nonarchimedean_finset_image_add hna'
      (λ i, B.equiv_fun y i • B.equiv_fun (B k * B i) ixy) (univ : finset ι),
    obtain ⟨k', -, hk'⟩ := hk',
    rw [pi.smul_apply, norm_smul, sum_apply],
    apply le_trans (mul_le_mul_of_nonneg_left hk' (norm_nonneg _)),
    -- Now an easy computation leads to the desired conclusion.
    rw [norm_smul, mul_assoc, mul_comm (B.norm (B c.fst * B c.snd)), ← mul_assoc],
    exact mul_le_mul (mul_le_mul (B.le_norm _ _) (B.le_norm _ _) (norm_nonneg _) (norm_nonneg _))
      (le_trans (B.le_norm _ _) (hc (k, k'))) (norm_nonneg _) 
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) }
end

/-- For any `k : K`, `y : L`, we have
  `B.equiv_fun ((algebra_map K L k) * y) i = k * (B.equiv_fun y i) `. -/
lemma repr_smul {ι : Type*} [fintype ι] (B : basis ι K L) (i : ι) (k : K) (y : L) : 
  B.equiv_fun ((algebra_map K L k) * y) i = k * (B.equiv_fun y i) :=
by rw [← smul_eq_mul, algebra_map_smul, linear_equiv.map_smul]; refl

/-- For any `k : K`, `y : L`, we have
  `B.norm ((algebra_map K L) k * y) = B.norm ((algebra_map K L) k) * B.norm y`. -/
lemma norm_smul {ι : Type*} [fintype ι] [nonempty ι] {B : basis ι K L}
  {i : ι} (hBi : B i = (1 : L)) (k : K) (y : L) :
  B.norm ((algebra_map K L) k * y) = B.norm ((algebra_map K L) k) * B.norm y :=
begin
  classical,
  by_cases hk : k = 0,
  { rw [hk, map_zero, zero_mul, B.norm_zero', zero_mul],},
  { rw norm_extends hBi,
    simp only [norm],
    set i := classical.some (finite.exists_max (λ i : ι, ‖B.equiv_fun y i‖)) with hi_def,
    have hi := classical.some_spec (finite.exists_max (λ i : ι, ‖B.equiv_fun y i‖)),
    set j := classical.some (finite.exists_max (λ i : ι, ‖B.equiv_fun ((algebra_map K L) k * y) i‖))
      with hj_def,
    have hj := classical.some_spec
      (finite.exists_max (λ i : ι, ‖B.equiv_fun ((algebra_map K L) k * y) i‖)),
    have hij : ‖B.equiv_fun y i‖ = ‖B.equiv_fun y j‖,
    { refine le_antisymm _ (hi j),
      { specialize hj i,
        rw ← hj_def at hj,
        simp only [repr_smul, norm_mul] at hj,
        exact (mul_le_mul_left (lt_of_le_of_ne (norm_nonneg _)
          (ne.symm (norm_ne_zero_iff.mpr hk)))).mp hj }},
    rw [repr_smul, norm_mul, ← hi_def, ← hj_def, hij] },
end

end basis

/-- If `K` is a nonarchimedean normed field `L/K` is a finite extension, then there exists a 
power-multiplicative nonarchimedean `K`-algebra norm on `L` extending the norm on `K`. -/
lemma finite_extension_pow_mul_seminorm (hfd : finite_dimensional K L)
  (hna : is_nonarchimedean (norm : K → ℝ)) :
  ∃ (f : algebra_norm K L), is_pow_mul f ∧ function_extends (norm : K → ℝ) f ∧ 
    is_nonarchimedean f :=
begin
  -- Choose a basis B = {1, e2,..., en} of the K-vector space L
  classical,
  set h1 : linear_independent K (λ (x : ({1} : set L)), (x : L)) := 
  linear_independent_singleton one_ne_zero,
  set ι := {x // x ∈ (h1.extend (set.subset_univ ({1} : set L)))} with hι,
  set B : basis ι K L  := basis.extend h1 with hB,
  letI hfin : fintype ι := finite_dimensional.fintype_basis_index B,
  haveI hem : nonempty ι := B.index_nonempty,
  have h1L : (1 : L) ∈ h1.extend _ := basis.subset_extend _ (set.mem_singleton (1 : L)),
  have hB1 : B ⟨1, h1L⟩ = (1 : L),
  { rw [basis.coe_extend, subtype.coe_mk] },
  -- For every k ∈ K, k = k • 1 + 0 • e2 + ... + 0 • en
  have h_k : ∀ (k : K), B.equiv_fun ((algebra_map K L) k) = λ (i : ι), 
    if (i = ⟨(1 : L), h1L⟩) then k else 0 := basis_one hB1,
  -- Define a function g : L → ℝ by setting g (∑ki • ei) = maxᵢ ‖ ki ‖  
  set g : L → ℝ := B.norm with hg,
  -- g 0 = 0
  have hg0 : g 0 = 0 := B.norm_zero',
  -- g takes nonnegative values
  have hg_nonneg : ∀ (x : L), 0 ≤ g x := λ x, norm_nonneg _,
  -- g extends the norm on K
  have hg_ext : function_extends (norm : K → ℝ) g := basis.norm_extends hB1,
  -- g is nonarchimedean
  have hg_na : is_nonarchimedean g := basis.norm_is_nonarchimedean hna,
  -- g satisfies the triangle inequality
  have hg_add : ∀ (a b : L), g (a + b) ≤ g a + g b,
  { exact add_le_of_is_nonarchimedean hg_nonneg hg_na },
  -- g (-a) = g a
  have hg_neg : ∀ (a : L), g (-a) = g a := B.norm_neg,
  -- g is multiplicatively bounded
  have hg_bdd : ∃ (c : ℝ) (hc : 0 < c), ∀ (x y : L), g (x * y) ≤ c * g x * g y,
  { exact basis.norm_is_bdd hB1 hna },
  -- g is a K-module norm
  have hg_mul : ∀ (k : K) (y : L), g ((algebra_map K L) k * y) = g ((algebra_map K L) k) * g y :=
  λ k y, basis.norm_smul hB1 k y,
  -- Using BGR Prop. 1.2.1/2, we can smooth g to a ring norm f on L that extends the norm on K.
  set f := seminorm_from_bounded hg0 hg_nonneg hg_bdd hg_add hg_neg with hf,
  have hf_na : is_nonarchimedean f := 
  seminorm_from_bounded_is_nonarchimedean hg_nonneg hg_bdd hg_na,
  have hf_1 : f 1 ≤ 1 := seminorm_from_bounded_is_norm_le_one_class hg_nonneg hg_bdd,
  have hf_ext : function_extends (norm : K → ℝ) f,
  { intro k,
    rw ← hg_ext,
    exact seminorm_from_bounded_of_mul_apply hg_nonneg hg_bdd (hg_mul k) },
  -- Using BGR Prop. 1.3.2/1, we obtain from f  a power multiplicative K-algebra norm on L 
  -- extending the norm on K.
  set F' := smoothing_seminorm hf_1 hf_na with hF',
  have hF'_ext : ∀ k : K,  F' ((algebra_map K L) k) = ‖k‖,
  { intro k,
    rw ← hf_ext _,
    exact smoothing_seminorm_apply_of_is_mult hf_1 
      (seminorm_from_bounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k)) hf_na },
  have hF'_1 : F' 1 = 1,
  { have h1 : (1 : L) = (algebra_map K L) 1 := by rw map_one,
    simp only [h1, hF'_ext (1 : K), norm_one], },
  have hF'_0 : F' ≠ 0 := fun_like.ne_iff.mpr ⟨(1 : L), by {rw hF'_1, exact one_ne_zero}⟩,

  set F : algebra_norm K L :=
  { smul' :=  λ k y,
    begin
      simp only [ring_norm.to_fun_eq_coe],
      have hk : ∀ y : L, f ((algebra_map K L k) * y) = f (algebra_map K L k) * f y,
      { exact seminorm_from_bounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k), },
      have hfk : ‖k‖  = (smoothing_seminorm hf_1 hf_na)((algebra_map K L) k),
      { rw [← hf_ext k, eq_comm, smoothing_seminorm_apply_of_is_mult hf_1 hk] },
      simp only [hfk, hF'],
      erw [← smoothing_seminorm_of_mult hf_1 hk hf_na y, algebra.smul_def],
      refl,
    end,
    ..(ring_seminorm.to_ring_norm F' hF'_0) },

    have hF_ext : ∀ k : K,  F ((algebra_map K L) k) = ‖k‖,
    { intro k,
      rw ← hf_ext _,
      exact smoothing_seminorm_apply_of_is_mult hf_1 
        (seminorm_from_bounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k)) hf_na },
    have hF_1 : F 1 = 1,
    { have h1 : (1 : L) = (algebra_map K L) 1 := by rw map_one,
      simp only [h1, hF_ext (1 : K), norm_one], },
    exact ⟨F, smoothing_seminorm_is_pow_mul hf_1, hF_ext, 
      smoothing_seminorm_is_nonarchimedean hf_1 hf_na⟩,
end