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
  classical,
  have h1 : linear_independent K (λ x, x : ({1} : set L) → L),
  { exact linear_independent_singleton one_ne_zero },
  set ι := ↥((h1).extend (set.subset_univ ({1} : set L))) with hι,
  set B : basis ι K L  := basis.extend h1 with hB,
  haveI hfin : fintype ι := finite_dimensional.fintype_basis_index B,
  haveI hem : nonempty ι := B.index_nonempty,
  set g : L → ℝ := λ x,
   ∥B.equiv_fun x (classical.some (fintype.exists_max (λ i : ι, ∥B.equiv_fun x i∥ )))∥ with hg,

  have h1L : (1 : L) ∈ h1.extend _,
  { apply basis.subset_extend,
    exact set.mem_singleton 1 },
    /- set l : ι →₀ L := finsupp.equiv_fun_on_fintype.inv_fun (λ (i : ι), 
    if (i = ⟨(1 : L), h1L⟩) then k else 0), -/
  have h_k : ∀ (k : K), B.linear_independent.repr 
    (⟨(algebra_map K L k), B.mem_span _⟩ : submodule.span K (set.range B)) = finsupp.equiv_fun_on_fintype.inv_fun (λ (i : ι), 
    if (i = ⟨(1 : L), h1L⟩) then k else 0),
  { intro k,
    have : (B.equiv_fun) ((algebra_map K L) k) =  B.linear_independent.repr 
    (⟨(algebra_map K L k), B.mem_span _⟩ : submodule.span K (set.range B)),
    { simp only [basis.equiv_fun_apply, fun_like.coe_fn_eq], 
      --simp_rw basis.span_eq B,
      --rw basis.mk_repr,
      sorry
      },
    --simp only [basis.equiv_fun_apply],
    /- have := linear_independent.total_repr B.linear_independent ⟨(algebra_map K L k),
      B.mem_span _⟩,  -/
    /- have :  ↑(⟨(algebra_map K L k), B.mem_span _⟩ : submodule.span K (set.range B)) =
      (algebra_map K L k) := by rw [submodule.coe_mk],
    rw ← this, -/
    --have hrepr : B.repr = B.linear_independent.repr _ := rfl,
    apply linear_independent.repr_eq B.linear_independent,
    --rw ← basis.sum_repr B (algebra_map K L k),
    simp only [basis.coe_extend, equiv.inv_fun_as_coe, submodule.coe_mk],
    rw finsupp.total_apply,
    have hh : ((finsupp.equiv_fun_on_fintype.symm) (λ (i : ι), 
      ite (i = ⟨1, h1L⟩) k 0)).sum (λ (i : ι) (a : K), a • (i : L)) = 
      ((finsupp.equiv_fun_on_fintype.symm)
      (λ (i : ι), ite (i = ⟨1, h1L⟩) k 0)).sum (λ (i : ι) (a : K), (ite (i = ⟨1, h1L⟩) (k • (i : L)) 0) ),
    { sorry },
    rw hh,
    rw finsupp.sum_ite_eq,
    sorry
    /- have h_eq : finsupp.total ι L K B (finsupp.equiv_fun_on_fintype.inv_fun (λ (i : ι), 
    if (i = ⟨(1 : L), h1L⟩) then k else 0)) = (algebra_map K L k) := sorry,
    convert linear_independent.repr_eq B.linear_independent h_eq, -/
    /- have h := basis.sum_repr B (algebra_map K L k),
    have h' : finset.univ.sum (λ (i : ι), (if (i = ⟨(1 : L), h1L⟩) then k else 0) • B i) 
    = (algebra_map K L) k,
    { sorry },
    ext i, 
    
    split_ifs,
    { 
       
     sorry },
    { sorry}  -/},

  have h_ext : ∀ (k : K), g (algebra_map K L k) = ∥ k ∥,
  { intro k,
    { by_cases hk : k = 0,
    { sorry },
    { simp only [hg],
    have : (B.equiv_fun) ((algebra_map K L) k) =  B.linear_independent.repr 
    (⟨(algebra_map K L k), B.mem_span _⟩ : submodule.span K (set.range B)) := sorry,
     sorry/-  rw h_k,
      simp_rw hι,
      have : (classical.some (fintype.exists_max (λ i : ι, 
        ∥(λ (i : ι), if (i = ⟨(1 : L), h1L⟩) then k else 0) i ∥))) = ⟨(1 : L), h1L⟩,
      { by_contradiction h,
        have h_max := classical.some_spec (fintype.exists_max (λ i : ι, 
          ∥(λ (i : ι), if (i = ⟨(1 : L), h1L⟩) then k else 0) i ∥)),
        simp only [if_neg h] at h_max,
        specialize h_max ⟨(1 : L), h1L⟩,
        rw [if_pos rfl, norm_zero, norm_le_zero_iff] at h_max,
        exact hk h_max },
    rw if_pos this  -/}}},

  sorry
end