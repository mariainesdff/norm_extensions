import analysis.normed_space.bounded_linear_maps
import seminormed_rings

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

variables {K : Type*} [normed_field K]

-- Lemma 3.2.1./3
lemma finite_extension_pow_mul_seminorm {L : Type*} [field L] [algebra K L] 
  (hfd : finite_dimensional K L) :
  ∃ f : L → nnreal, is_algebra_norm K f ∧ is_pow_mult f ∧ norm_extends K f :=
begin
  have h1 : linear_independent K (λ x, x : ({1} : set L) → L),
  { exact linear_independent_singleton one_ne_zero },
  set ι := ↥(h1.extend (set.subset_univ ({1} : set L))) with hι,
  set B : basis ι K L  := basis.extend h1 with hB,
  haveI hfin : fintype ι := finite_dimensional.fintype_basis_index B,
  haveI hem : nonempty ι := B.index_nonempty,
  set g : L → ℝ := λ x,
   ∥B.equiv_fun x (classical.some (fintype.exists_max (λ i : ι, ∥B.equiv_fun x i∥ )))∥,
  sorry
end