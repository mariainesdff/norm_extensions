import analysis.normed_space.bounded_linear_maps
import seminormed_rings
import smoothing_procedure

noncomputable theory

open_locale big_operators

structure is_continuous_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] (f : E → F)
  extends is_linear_map 𝕜 f : Prop :=
(cont : continuous f . tactic.interactive.continuity')

lemma is_continuous_linear_map_iff_is_bounded_linear_map {K : Type*} [nondiscrete_normed_field K]
  {M : Type*} [normed_group M] [normed_space K M] {N : Type*} [normed_group N] [normed_space K N]
  (f : M → N) : is_continuous_linear_map K f ↔ is_bounded_linear_map K f :=
begin
  refine ⟨λ h_cont, _, λ h_bdd, ⟨h_bdd.to_is_linear_map, h_bdd.continuous⟩⟩,
  { set F : M →L[K] N :=
    by use [f, is_linear_map.map_add h_cont.1, is_linear_map.map_smul h_cont.1, h_cont.2],
    exact continuous_linear_map.is_bounded_linear_map F, },
end

-- Lemma 3.2.1./3

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]  

variables {ι : Type*} [fintype ι] {R : Type*} [ring R] {M : Type*} [add_comm_group M]
  [module R M] 

--set_option pp.all true
lemma linear_independent.eq_coords_of_eq {v : ι → M} (hv : linear_independent R v) {f : ι → R}
  {g : ι → R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := 
begin
  rw [← sub_eq_zero, ← finset.sum_sub_distrib] at heq,
  /- conv at heq begin
    congr,
    congr,
    skip,
    funext,
    rw ← smul_sub,
  end, -/
  have hx: ∀ (x : ι), (f x • v x - g x • v x) = (f x - g x) • v x,
  { intro x,
    rw sub_smul,},
  simp_rw ← sub_smul at heq,
  have h0 : ∑ i, (f i - g i) • v i = 0 := sorry, --smul_sub doesn't work?
  rw linear_independent_iff' at hv,
  exact sub_eq_zero.mp (hv finset.univ (λ i, (f i - g i)) h0 i (finset.mem_univ i)),
end

/- lemma basis.eq_coords_of_eq (B : basis ι R M) {f : ι → R} {g : ι → R}
  (heq : ∑ i, f i • B i = ∑ i, g i • B i) (i : ι) : f i = g i := 
begin
  have hB : linear_independent R B := B.linear_independent,
  rw [← sub_eq_zero, ← finset.sum_sub_distrib] at heq,
  have h0 : ∑ i, (f i - g i) • B i = 0 := sorry, --smul_sub doesn't work?
  rw linear_independent_iff' at hB,
  rw ← sub_eq_zero,
  exact hB finset.univ (λ i, (f i - g i)) h0 i (finset.mem_univ i),
end -/

lemma finite_extension_pow_mul_seminorm (hfd : finite_dimensional K L) :
  ∃ f : L → nnreal, is_algebra_norm K (normed_ring.to_is_norm K) f ∧ is_pow_mult f ∧
    function_extends (λ (k : K), (⟨∥ k ∥, norm_nonneg _ ⟩ : nnreal)) f :=
begin
  classical,
  set h1 : linear_independent K (λ (x : ({1} : set L)), (x : L)) := 
  linear_independent_singleton one_ne_zero,
  set ι := {x // x ∈  (h1.extend (set.subset_univ ({1} : set L)))} with hι,
  set B : basis ι K L  := basis.extend h1 with hB,
  letI hfin : fintype ι := finite_dimensional.fintype_basis_index B,
  haveI hem : nonempty ι := B.index_nonempty,
  set g : L → nnreal := λ x,
    ⟨∥B.equiv_fun x (classical.some (fintype.exists_max (λ i : ι, ∥B.equiv_fun x i∥ )))∥,
      norm_nonneg _⟩ with hg,
  have h1L : (1 : L) ∈ h1.extend _,
  { apply basis.subset_extend,
    exact set.mem_singleton 1 },

  have h_k : ∀ (k : K), (B.equiv_fun) ((algebra_map K L) k) = λ (i : ι), 
    if (i = ⟨(1 : L), h1L⟩) then k else 0,
  { intro k,
    ext i,
    apply linear_independent.eq_coords_of_eq B.linear_independent,
    rw basis.sum_equiv_fun B (algebra_map K L k),

    /- have  hh: ∀ (i : ι), (i ∈ finset.univ) → 
     ite (i = ⟨1, h1L⟩) k 0 • B i =  ite (i = ⟨1, h1L⟩) (k • B i) 0,
    { intros j hj,
      split_ifs,
      exacts [rfl, zero_smul _ _], }, -/

    have : ∑ (i : ι), ite (i = ⟨1, h1L⟩) k 0 • B i = ∑ (i : ι), ite (i = ⟨1, h1L⟩) (k • B i) 0,
    { simp only [basis.coe_extend],
      apply finset.sum_congr (eq.refl _),
      { rintros h -,
        split_ifs,
        exacts [rfl, zero_smul _ _], }},
    rw this,
    
    --delta coe_sort at hι,
     rw algebra.algebra_map_eq_smul_one,
    have h := finset.sum_ite_eq' finset.univ (⟨1, h1L⟩ : ι) (λ i : ι, k • B i), -- TODO: ask
    simp only [basis.coe_extend, finset.mem_univ, subtype.coe_mk, if_true] at h,
    simp_rw hι,
    --have h : ι = {x // x ∈ h1.extend _} := rfl,
    --unfreezingI {subst h},
    --subst h,
    --change k • (1 : L) = ∑ (i : {x // x ∈ h1.extend _}), ite (i = _) (k • B i) 0,
    rw finset.sum_ite_eq' finset.univ (⟨1, h1L⟩ : ι) (λ i : ι, k • B i),
    rw basis.coe_extend,
    rw ← h,
    sorry
    },
    
  have hg0 : g 0 = 0,
  { simp only [nonneg.mk_eq_zero, map_zero, pi.zero_apply, norm_zero],},

  have hg_ext : function_extends (λ x : K, (⟨∥x∥, norm_nonneg _⟩ : nnreal)) g,
  { intro k,
    { by_cases hk : k = 0,
    { rw [hk, map_zero, hg0, eq_comm, ← nnreal.coe_eq_zero, subtype.coe_mk, norm_zero], },
    { simp only [hg, ← nnreal.coe_eq, nnreal.coe_mk],
      rw h_k,
      simp_rw hι,
      have h_max : (classical.some (fintype.exists_max (λ i : ι, 
        ∥(λ (i : ι), if (i = ⟨(1 : L), h1L⟩) then k else 0) i ∥))) = ⟨(1 : L), h1L⟩,
      { by_contradiction h,
        have h_max := classical.some_spec (fintype.exists_max (λ i : ι, 
          ∥(λ (i : ι), if (i = ⟨(1 : L), h1L⟩) then k else 0) i ∥)),
        simp only [if_neg h] at h_max,
        specialize h_max ⟨(1 : L), h1L⟩,
        rw [if_pos rfl, norm_zero, norm_le_zero_iff] at h_max,
        exact hk h_max },
      rw if_pos h_max }}},
  
  have hg_bdd : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : L), g (x * y) ≤ c * g x * g y,
  { set M := classical.some (fintype.exists_max (λ (i : ι × ι), g (B i.1 * B i.2))) with hM_def,
    have hM := classical.some_spec (fintype.exists_max (λ (i : ι × ι), g (B i.1 * B i.2))),
    use g (B M.1 * B M.2),
    split,
    { have h_pos : (0 : nnreal) < g (B ⟨(1 : L), h1L⟩ * B ⟨(1 : L), h1L⟩),
      { have h1 : (1 : L) = (algebra_map K L) 1 := by rw map_one,
        simp only [basis.coe_extend, subtype.coe_mk, mul_one],
        rw [h1, hg_ext],
        simp only [norm_one,
          ← nnreal.coe_pos, subtype.coe_mk, zero_lt_one], },
      exact lt_of_lt_of_le h_pos (hM (⟨(1 : L), h1L⟩, ⟨(1 : L), h1L⟩)) },
    { intros x y,
      sorry }},

  have hg_mul : ∀ (k : K) (y : L), g ((algebra_map K L) k * y) = g ((algebra_map K L) k) * g y,
  { intros k y,
    rw hg_ext,
    simp only [hg],
    sorry },

  set f := seminorm_from_bounded g with hf,
  have hf_sn : is_seminorm f := seminorm_from_bounded_is_seminorm hg0 hg_bdd,
  have hf_1 : is_norm_le_one_class f := seminorm_from_bounded_is_norm_le_one_class hg_bdd,
  have hf_ext : function_extends (λ x : K, (⟨∥x∥, norm_nonneg _⟩ : nnreal)) f,
  { intro k,
    rw ← hg_ext,
    exact seminorm_from_bounded_of_mul_apply hg_bdd (hg_mul k), },
  set F := smoothing_seminorm hf_sn hf_1 with hF,
  have hF_ext : ∀ k : K,  F ((algebra_map K L) k) = (λ (k : K), (⟨∥k∥, norm_nonneg _⟩ : nnreal)) k,
  { intro k,
    rw ← hf_ext _,
    exact smoothing_seminorm_apply_of_is_mult hf_sn hf_1 
      (seminorm_from_bounded_of_mul_is_mul hg_bdd (hg_mul k)) },
  have hF_1 : F 1 = 1,
  { have h1 : (1 : L) = (algebra_map K L) 1 := by rw map_one,
    simp only [h1, hF_ext (1 : K), nonneg.mk_eq_one, norm_one], },
  use F,
  refine ⟨⟨field.is_norm_of_is_seminorm (smoothing_seminorm_is_seminorm hf_sn hf_1)
      ⟨(1 : L), hF_1.symm ▸ zero_ne_one⟩, _⟩, smoothing_seminorm_is_pow_mult hf_sn hf_1, hF_ext⟩,
  { intros k y,
    have hk : ∀ y : L, f ((algebra_map K L k) * y) = f (algebra_map K L k) * f y,
    { exact seminorm_from_bounded_of_mul_is_mul hg_bdd (hg_mul k), },
    have hfk : f ((algebra_map K L) k) = (⟨∥k∥, norm_nonneg _⟩ : nnreal) := hf_ext k,
    rw [hF, ← hfk, ← smoothing_seminorm_apply_of_is_mult hf_sn hf_1 hk],
    exact smoothing_seminorm_of_mult hf_sn hf_1 hk y,},
end