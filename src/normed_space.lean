import analysis.normed_space.bounded_linear_maps
import seminormed_rings
import smoothing_procedure

noncomputable theory

open_locale big_operators nnreal


--TODO: check normed_group is normed_add_comm_group, nondiscrete_normed_field is nontrivilly_normed_field
structure is_continuous_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] (f : E → F)
  extends is_linear_map 𝕜 f : Prop :=
(cont : continuous f . tactic.interactive.continuity')

lemma is_continuous_linear_map_iff_is_bounded_linear_map {K : Type*} [nontrivially_normed_field K]
  {M : Type*} [normed_add_comm_group M] [normed_space K M] {N : Type*} [normed_add_comm_group N] 
  [normed_space K N] (f : M → N) : is_continuous_linear_map K f ↔ is_bounded_linear_map K f :=
begin
  refine ⟨λ h_cont, _, λ h_bdd, ⟨h_bdd.to_is_linear_map, h_bdd.continuous⟩⟩,
  { set F : M →L[K] N :=
    by use [f, is_linear_map.map_add h_cont.1, is_linear_map.map_smul h_cont.1, h_cont.2],
    exact continuous_linear_map.is_bounded_linear_map F, },
end

-- Lemma 3.2.1./3

section

variables {K : Type*} [field K] {L : Type*} [field L] [algebra K L] {g : K → ℝ≥0} (hg : is_norm g)
lemma finite_extension_pow_mul_seminorm' (hfd : finite_dimensional K L)
  (hna : ∀ (a b : K), g(a - b) ≤ max (g a) (g b)) :
  ∃ f : L → nnreal, is_algebra_norm hg f ∧ is_pow_mult f ∧ function_extends g f :=
sorry 
end

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]

variables {ι : Type*} [fintype ι] {R : Type*} [ring R] {M : Type*} [add_comm_group M]
  [module R M] 

lemma linear_independent.eq_coords_of_eq {v : ι → M} (hv : linear_independent R v) {f : ι → R}
  {g : ι → R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := 
begin
  rw [← sub_eq_zero, ← finset.sum_sub_distrib] at heq,
  simp_rw ← sub_smul at heq,
  rw linear_independent_iff' at hv,
  exact sub_eq_zero.mp (hv finset.univ (λ i, (f i - g i)) heq i (finset.mem_univ i)),
end

lemma basis_one {ι : Type*} [fintype ι] [decidable_eq ι] {B : basis ι K L} {i : ι}
  (hBi : B i = (1 : L)) (k : K) :
  (B.equiv_fun) ((algebra_map K L) k) = λ (j : ι), if (j = i) then k else 0 := 
begin
  ext j,
  apply linear_independent.eq_coords_of_eq B.linear_independent,
  rw basis.sum_equiv_fun B (algebra_map K L k),
  have h_sum : ∑ (j : ι), ite (j = i) k 0 • B j = ∑ (j : ι), ite (j = i) (k • B j) 0,
  { apply finset.sum_congr (eq.refl _),
    { rintros h -,
      split_ifs,
      exacts [rfl, zero_smul _ _] }},
  rw [h_sum, algebra.algebra_map_eq_smul_one,
    finset.sum_ite_eq' finset.univ (i : ι) (λ j : ι, k • B j)],
  simp only [finset.mem_univ, if_true, hBi],
end

def basis.norm {ι : Type*} [fintype ι] [nonempty ι] (B : basis ι K L) : L → ℝ≥0 := 
λ x, ∥B.equiv_fun x (classical.some (finite.exists_max (λ i : ι, ∥B.equiv_fun x i∥ )))∥₊

lemma basis.norm_zero {ι : Type*} [fintype ι] [nonempty ι] (B : basis ι K L) :  B.norm 0 = 0 :=
by simp only [basis.norm, nnnorm_eq_zero, map_zero, pi.zero_apply, norm_zero]

lemma basis.norm_extends {ι : Type*} [fintype ι] [nonempty ι] [decidable_eq ι] {B : basis ι K L}
  {i : ι} (hBi : B i = (1 : L)) :
  function_extends (λ x : K, ∥x∥₊) B.norm :=
begin
  intro k,
  { by_cases hk : k = 0,
  { simp only [hk, map_zero, B.norm_zero, nnnorm_zero] },
  { simp only [basis.norm,  basis_one hBi],
    have h_max : (classical.some (finite.exists_max (λ j : ι, 
      ∥(λ (n : ι), if (n = i) then k else 0) j ∥))) = i,
    { by_contradiction h,
      have h_max := classical.some_spec (finite.exists_max (λ j : ι, 
        ∥(λ (n : ι), if (n = i) then k else 0) j ∥)),
      simp only [if_neg h] at h_max,
      specialize h_max i,
      rw [if_pos rfl, norm_zero, norm_le_zero_iff] at h_max,
      exact hk h_max },
    rw if_pos h_max, }}
end

lemma basis.norm_is_nonarchimedean {ι : Type*} [fintype ι] [nonempty ι] [decidable_eq ι]
  {B : basis ι K L} {i : ι} (hBi : B i = (1 : L))
  (hna : ∀ (a b : K), ∥a - b∥₊ ≤ max (∥a∥₊) (∥b∥₊)) : is_nonarchimedean B.norm  :=
begin
  intros x y,
  simp only [basis.norm],
  set ixy := classical.some (finite.exists_max (λ i : ι, ∥B.equiv_fun (x - y) i∥)) with hixy_def,
  have hxy : ∥B.equiv_fun (x - y) ixy∥₊ ≤ max (∥B.equiv_fun x ixy∥₊) (∥B.equiv_fun y ixy∥₊),
  { rw [linear_equiv.map_sub, pi.sub_apply], exact hna _ _ , },
  have hix := classical.some_spec (finite.exists_max (λ i : ι, ∥B.equiv_fun x i∥)),
  have hiy := classical.some_spec (finite.exists_max (λ i : ι, ∥B.equiv_fun y i∥)),
  cases le_max_iff.mp hxy with hx hy,
  { apply le_max_of_le_left,
    exact le_trans hx (hix ixy), },
  { apply le_max_of_le_right,
    exact le_trans hy (hiy ixy), },
end

lemma basis.norm_is_bdd {ι : Type*} [fintype ι] [nonempty ι] [decidable_eq ι] {B : basis ι K L}
  {i : ι} (hBi : B i = (1 : L)) : 
  ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y :=
begin
  set M := classical.some (finite.exists_max (λ (i : ι × ι), B.norm (B i.1 * B i.2))) with hM_def,
  have hM := classical.some_spec (finite.exists_max (λ (i : ι × ι), B.norm (B i.1 * B i.2))),
  use B.norm (B M.1 * B M.2),
  split,
  { have h_pos : (0 : nnreal) < B.norm (B i * B i),
    { have h1 : (1 : L) = (algebra_map K L) 1 := by rw map_one,
      rw [hBi, mul_one, h1, basis.norm_extends hBi],
      simp only [nnnorm_one, zero_lt_one] },
    exact lt_of_lt_of_le h_pos (hM (i, i)) },
  { intros x y,
    set ixy := classical.some (finite.exists_max (λ i : ι, ∥B.equiv_fun (x*y) i∥))
      with hixy_def,
    conv_lhs{simp only [basis.norm],
    rw [← hixy_def, ← basis.sum_equiv_fun B x, ← basis.sum_equiv_fun B y] },
    rw finset.sum_mul,
    --rw basis.equiv_fun_apply,
    
    have h_sum : B.equiv_fun (∑ (x_1 : ι), B.equiv_fun x x_1 • B x_1 * 
    ∑ (i : ι), B.equiv_fun y i •  B i) ixy = 
    ∑ (x_1 : ι), B.equiv_fun (B.equiv_fun x x_1 • B x_1 * 
    ∑ (i : ι), B.equiv_fun y i •  B i) ixy,
    { 
      sorry },
/-     have h_sum : B.repr (∑ (x_1 : ι), B.repr x x_1 • B x_1 * 
    ∑ (i : ι), B.equiv_fun y i •  B i) ixy = 
    ∑ (x_1 : ι), B.repr (B.equiv_fun x x_1 • B x_1 * 
    ∑ (i : ι), B.equiv_fun y i •  B i) ixy,
    { 
      sorry }, -/
    simp_rw h_sum,
 --apply @is_nonarchimedean_finset_image_add _ _ (λ (x : K), ∥x∥₊) (nnnorm_zero) _ B.equiv_fun, 
   -- }, 
    /- have hj : ∃ (j : ι) (hj : finset.univ.nonempty → j ∈ finset.univ), ∥∑ (x_1 : ι), 
      B.equiv_fun (B.equiv_fun x x_1 • B x_1 * 
      ∑ (i : ι), B.equiv_fun y i • B i) ixy∥₊ ≤ 
    ∥B.equiv_fun (B.equiv_fun x j • B j * ∑ (i : ι), B.equiv_fun y i • B i) ixy∥₊,
    { have hna : is_nonarchimedean (nnnorm : K → ℝ≥0) := sorry,
      sorry,
      /- have := @is_nonarchimedean_finset_image_add K _ nnnorm (nnnorm_zero) hna B.equiv_fun
        finset.univ,  -/
    },
    obtain ⟨j, hjuniv, hj⟩ := hj,
    apply le_trans hj,
    simp, -/

    /- lemma is_nonarchimedean_finset_image_add {α : Type*} [ring α] {f : α → nnreal} (hf0 : f 0 = 0)
  (hna : is_nonarchimedean f) {β : Type*} [hβ : nonempty β] (g : β → α) (s : finset β) :
  ∃ (b : β) (hb : s.nonempty → b ∈ s), f (s.sum g) ≤ f (g b) := -/
    
    sorry },
end

lemma basis.repr_smul {ι : Type*} [fintype ι] [nonempty ι] [decidable_eq ι] (B : basis ι K L)
  (i : ι) (k : K) (y : L) : B.equiv_fun ((algebra_map K L k) * y) i = k * (B.equiv_fun y i) :=
by rw [← smul_eq_mul, algebra_map_smul, linear_equiv.map_smul]; refl

lemma basis.norm_smul {ι : Type*} [fintype ι] [nonempty ι] [decidable_eq ι] {B : basis ι K L}
  {i : ι} (hBi : B i = (1 : L)) (k : K) (y : L) :
  B.norm ((algebra_map K L) k * y) = B.norm ((algebra_map K L) k) * B.norm y :=
begin
  by_cases hk : k = 0,
  { rw [hk, map_zero, zero_mul, B.norm_zero, zero_mul],},
  { rw basis.norm_extends hBi,
    simp only [basis.norm],
    set i := classical.some (finite.exists_max (λ i : ι, ∥B.equiv_fun y i∥)) with hi_def,
    have hi := classical.some_spec (finite.exists_max (λ i : ι, ∥B.equiv_fun y i∥)),
    set j := classical.some (finite.exists_max (λ i : ι, ∥B.equiv_fun ((algebra_map K L) k * y) i∥))
      with hj_def,
    have hj := classical.some_spec
      (finite.exists_max (λ i : ι, ∥B.equiv_fun ((algebra_map K L) k * y) i∥)),
    have hij : ∥B.equiv_fun y i∥₊ = ∥B.equiv_fun y j∥₊,
    { refine le_antisymm _ (hi j),
      { specialize hj i,
        rw ← hj_def at hj,
        simp only [basis.repr_smul, norm_mul] at hj,
        exact (mul_le_mul_left (lt_of_le_of_ne (norm_nonneg _)
          (ne.symm (norm_ne_zero_iff.mpr hk)))).mp hj }},
    rw [basis.repr_smul, nnnorm_mul, ← hi_def, ← hj_def, hij] },
end

lemma basis.norm_is_module_norm {ι : Type*} [fintype ι] (B : basis ι K L)
  (hB1 : ∃ i : ι, B i = (1 : L)) : Prop := false

lemma finite_extension_pow_mul_seminorm (hfd : finite_dimensional K L)
  (hna : ∀ (a b : K), ∥a - b∥₊ ≤ max (∥a∥₊) (∥b∥₊)) :
  ∃ f : L → nnreal, is_algebra_norm (normed_ring.to_is_norm K) f ∧ is_pow_mult f ∧
    function_extends (λ (k : K), ∥ k ∥₊) f ∧ is_nonarchimedean f :=
begin
  -- Choose a basis B = {1, e2,..., en} of the K-vector space L
  classical,
  set h1 : linear_independent K (λ (x : ({1} : set L)), (x : L)) := 
  linear_independent_singleton one_ne_zero,
  set ι := {x // x ∈ (h1.extend (set.subset_univ ({1} : set L)))} with hι,
  set B : basis ι K L  := basis.extend h1 with hB,
  letI hfin : fintype ι := finite_dimensional.fintype_basis_index B,
  haveI hem : nonempty ι := B.index_nonempty,
  have h1L : (1 : L) ∈ h1.extend _,
  { apply basis.subset_extend,
    exact set.mem_singleton 1 },
  have hB1 : B ⟨1, h1L⟩ = (1 : L),
  { rw [basis.coe_extend, subtype.coe_mk] },
  -- For every k ∈ K, k = k • 1 + 0 • e2 + ... + 0 • en
  have h_k : ∀ (k : K), (B.equiv_fun) ((algebra_map K L) k) = λ (i : ι), 
    if (i = ⟨(1 : L), h1L⟩) then k else 0 := basis_one hB1,
  -- Define a function g : L → ℝ≥0 by setting g (∑ki • ei) = maxᵢ ∥ ki ∥  
  set g : L → nnreal := B.norm with hg,
  -- g 0 = 0
  have hg0 : g 0 = 0 := B.norm_zero,
  -- g extends the norm on K
  have hg_ext : function_extends (λ x : K, ∥x∥₊) g := basis.norm_extends hB1,
  -- g is nonarchimedean
  have hg_na : is_nonarchimedean g := basis.norm_is_nonarchimedean hB1 hna,
  -- g is multiplicatively bounded
  have hg_bdd : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : L), g (x * y) ≤ c * g x * g y,
  { exact basis.norm_is_bdd hB1 },
  -- g is a K-module norm
  have hg_mul : ∀ (k : K) (y : L), g ((algebra_map K L) k * y) = g ((algebra_map K L) k) * g y :=
  λ k y, basis.norm_smul hB1 k y,
  -- Using BGR Prop. 1.2.1/2, we can smooth g to a ring norm f on L that extends the norm on K.
  set f := seminorm_from_bounded g with hf,
  have hf_sn : is_seminorm f := seminorm_from_bounded_is_seminorm hg0 hg_bdd 
    (add_le_of_is_nonarchimedean hg0 hg_na),
  have hf_na : is_nonarchimedean f := seminorm_from_bounded_is_nonarchimedean hg_bdd hg_na,
  have hf_1 : is_norm_le_one_class f := seminorm_from_bounded_is_norm_le_one_class hg_bdd,
  have hf_ext : function_extends (λ x : K, ∥x∥₊) f,
  { intro k,
    rw ← hg_ext,
    exact seminorm_from_bounded_of_mul_apply hg_bdd (hg_mul k) },
  -- Using BGR Prop. 1.3.2/1, we obtain from f  a power multiplicative K-algebra norm on L 
  -- extending the norm on K.
  set F := smoothing_seminorm hf_1 with hF,
  have hF_ext : ∀ k : K,  F ((algebra_map K L) k) = (λ (k : K), ∥k∥₊) k,
  { intro k,
    rw ← hf_ext _,
    exact smoothing_seminorm_apply_of_is_mult hf_sn hf_1 
      (seminorm_from_bounded_of_mul_is_mul hg_bdd (hg_mul k)) },
  have hF_1 : F 1 = 1,
  { have h1 : (1 : L) = (algebra_map K L) 1 := by rw map_one,
    simp only [h1, hF_ext (1 : K), nnnorm_one], },
  use F,
  refine ⟨⟨field.is_norm_of_is_seminorm (smoothing_seminorm_is_seminorm hf_sn hf_1 hf_na)
      ⟨(1 : L), hF_1.symm ▸ zero_ne_one⟩, _⟩, smoothing_seminorm_is_pow_mult hf_sn hf_1, hF_ext, 
      smoothing_seminorm_is_nonarchimedean hf_sn hf_1 hf_na⟩,
  { intros k y,
    have hk : ∀ y : L, f ((algebra_map K L k) * y) = f (algebra_map K L k) * f y,
    { exact seminorm_from_bounded_of_mul_is_mul hg_bdd (hg_mul k), },
    have hfk : f ((algebra_map K L) k) = ∥k∥₊ := hf_ext k,
    rw [hF, ← hfk, ← smoothing_seminorm_apply_of_is_mult hf_sn hf_1 hk, algebra.smul_def],
    exact smoothing_seminorm_of_mult hf_sn hf_1 hk y, },
end