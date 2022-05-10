import analysis.normed_space.bounded_linear_maps
import seminormed_rings
import smoothing_procedure

noncomputable theory

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

lemma finite_extension_pow_mul_seminorm (hfd : finite_dimensional K L) :
  ∃ f : L → nnreal, is_algebra_norm K f ∧ is_pow_mult f ∧ seminorm_extends K f :=
begin
  classical,
  set h1 : linear_independent K (λ (x : ({1} : set L)), (x : L)) := 
  linear_independent_singleton one_ne_zero,
  set ι := ↥(h1.extend (set.subset_univ ({1} : set L))) with hι,
  set B : basis ι K L  := basis.extend h1 with hB,
  haveI hfin : fintype ι := finite_dimensional.fintype_basis_index B,
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
    have h := basis.sum_repr B (algebra_map K L k),
    ext i,
    split_ifs,
    { sorry },
    { sorry }},
    
  have hg0 : g 0 = 0,
  { simp only [nonneg.mk_eq_zero, map_zero, pi.zero_apply, norm_zero],},

  have hg_ext : seminorm_extends K g,
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
  
  have hg_bdd : ∃ (c : nnreal) (hc : 0 < c), ∀ (x y : L), g (x * y) ≤ c * g x * g y := sorry,

  set f := seminorm_from_bounded g with hf_def,
  have hf_sn : is_seminorm f := seminorm_from_bounded_is_seminorm hg0 hg_bdd,
  have hf_ext : seminorm_extends K f := sorry,

  set F := smoothing_seminorm hf_sn with hF,
  have hF1 : F 1 = 1 := sorry,
  use F,
  refine ⟨⟨field.is_norm_of_is_seminorm (smoothing_seminorm_is_seminorm hf_sn)
      ⟨(1 : L), hF1.symm ▸ zero_ne_one⟩, _⟩, smoothing_seminorm_is_pow_mult hf_sn, _⟩,
  { intros k x,

    sorry },
  { intro k,
    sorry }
end