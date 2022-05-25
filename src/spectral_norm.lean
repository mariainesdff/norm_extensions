import rank_one_valuation
import normed_space
import data.list.min_max
import field_theory.minpoly
import field_theory.normal
import topology.algebra.valuation

noncomputable theory

open_locale polynomial nnreal

variables {R : Type*} [normed_ring R]

def polynomial.coeffs (p : R[X])  : list R := list.map p.coeff (list.range p.nat_degree)

lemma list.le_max_of_exists_le {α : Type*} [linear_order α] [order_bot α] {l : list α} {a x : α}
  (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ :=
begin
  induction l with y l IH,
  { exact absurd hx (list.not_mem_nil _), },
  { obtain rfl | hl := hx,
    simp only [list.foldr, list.foldr_cons],
    { exact le_max_of_le_left h, },
    { exact le_max_of_le_right (IH hl) }}
end

def spectral_value_terms {p : R[X]} (hp : p.monic) : ℕ → nnreal := 
λ (n : ℕ), if n < p.nat_degree then 
∥ p.coeff n ∥₊^(1/(p.nat_degree - n : ℝ)) else 0

def spectral_value {p : R[X]} (hp : p.monic) : nnreal := supr (spectral_value_terms hp)

lemma spectral_value_terms_bdd_above {p : R[X]} (hp : p.monic) :
  bdd_above (set.range (spectral_value_terms hp)) := 
begin
  use list.foldr max 0
  (list.map (λ n, ∥ p.coeff n ∥₊^(1/(p.nat_degree - n : ℝ))) (list.range p.nat_degree)),
  { rw mem_upper_bounds,
    intros r hr,
    obtain ⟨n, hn⟩ := set.mem_range.mpr hr,
    simp only [spectral_value_terms] at hn,
    rw ← nnreal.bot_eq_zero,
    split_ifs at hn with hd hd,
    { have h : ∥p.coeff n∥₊ ^ (1 / (p.nat_degree - n : ℝ)) ∈ list.map 
        (λ (n : ℕ), ∥p.coeff n∥₊ ^ (1 / (p.nat_degree - n : ℝ))) (list.range p.nat_degree),
      { simp only [list.mem_map, list.mem_range],
        exact ⟨n, hd, rfl⟩, },  
    exact list.le_max_of_exists_le h (ge_of_eq hn), },
    { rw ← hn, exact zero_le _, }},
end

variable [nontrivial R]

lemma list.max_repeat {α : Type*} {n : ℕ} (a : α) [linear_order α] :
  list.foldr max a (list.repeat a n) = a :=
begin
  induction n with n hn,
  { simp only [list.repeat, list.foldr_nil] },
  { simp only [list.foldr, list.repeat, list.repeat_succ, list.foldr_cons, max_eq_left_iff],
    exact le_of_eq hn, }
end

lemma spectral_value_X_pow (n : ℕ) :
  spectral_value (@polynomial.monic_X_pow R _ n) = 0 := 
begin
  rw spectral_value, rw spectral_value_terms,
  simp_rw [polynomial.coeff_X_pow n, polynomial.nat_degree_X_pow],
  convert csupr_const,
  ext m,
  by_cases hmn : m < n,
  { rw [if_pos hmn, nnreal.coe_eq, nnreal.rpow_eq_zero_iff, if_neg (ne_of_lt hmn), nnnorm_zero,
      one_div, ne.def, inv_eq_zero, ← nat.cast_sub (le_of_lt hmn), nat.cast_eq_zero,
      nat.sub_eq_zero_iff_le],
    exact ⟨eq.refl _, not_le_of_lt hmn⟩, },
  { rw if_neg hmn },
  apply_instance,
end

lemma spectral_value_eq_zero_iff [nontrivial R] {p : R[X]} (hp : p.monic) :
  spectral_value hp = 0 ↔ p = polynomial.X^p.nat_degree := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw spectral_value at h,
    ext,
    rw polynomial.coeff_X_pow,
    by_cases hn : n = p.nat_degree,
    { rw [if_pos hn, hn, polynomial.coeff_nat_degree], exact hp, },
    { rw if_neg hn,
      { by_cases hn' : n < p.nat_degree,
        { have h_le : supr (spectral_value_terms hp) ≤ 0 := le_of_eq h,
          have h_exp : 0 < 1 / ((p.nat_degree : ℝ) - n),
          { rw [one_div_pos, ← nat.cast_sub (le_of_lt hn'), nat.cast_pos],
            exact nat.sub_pos_of_lt hn', },
          have h0 : (0 : nnreal) = 0^(1 / ((p.nat_degree : ℝ) - n)),
          { rw nnreal.zero_rpow (ne_of_gt h_exp), },
          rw [supr, cSup_le_iff (spectral_value_terms_bdd_above hp)
            (set.range_nonempty _)] at h_le,
          specialize h_le (spectral_value_terms hp n) ⟨n, rfl⟩,
          simp only [spectral_value_terms, if_pos hn'] at h_le,
          rw [h0, nnreal.rpow_le_rpow_iff h_exp] at h_le,
          exact norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _)), },
        { exact polynomial.coeff_eq_zero_of_nat_degree_lt 
            (lt_of_le_of_ne (le_of_not_lt hn') (ne_comm.mpr hn)) }}}},
  { convert spectral_value_X_pow p.nat_degree,
    apply_instance }
end

/- In this section we prove Proposition 3.1.2/1 from BGR. -/
section bdd_by_spectral_value
variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L] {f : L → ℝ≥0}
  (hf_pm : is_pow_mult f) (hf_Kn : is_algebra_norm (normed_ring.to_is_norm K) f)

-- Part (1): the norm of any root of p is bounded by the spectral value of p.
lemma root_norm_le_spectral_value {p : K[X]} (hp : p.monic) {x : L}
  (hx : polynomial.aeval x p = 0) : f x ≤ spectral_value hp := 
begin
  sorry
end

lemma polynomial.monic_of_prod (p : K[X]) {n : ℕ} (b : fin n → L) (hp : polynomial.map_alg K L p =
  finprod (λ (k : fin n), polynomial.X - (polynomial.C (b k)))) : p.monic :=
begin
  sorry
end

/-- Part (2): if p splits into linear factors over B, then its spectral value equals the maximum
  of the norms of its roots. -/
lemma max_root_norm_eq_spectral_value (p : K[X]) {n : ℕ} (b : fin n → L)
  (hp : polynomial.map_alg K L p = finprod (λ (k : fin n), polynomial.X - (polynomial.C (b k))))
  (h_isom : ∀ x y : K, f ((algebra_map K L y) - algebra_map K L x) = nndist x y) :
  supr (f ∘ b) = spectral_value (p.monic_of_prod b hp) := 
begin
  sorry
end

end bdd_by_spectral_value

/- In this section we prove Theorem 3.2.1/2 from BGR. -/

section spectral_norm

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

-- The spectral norm |y|_sp is the spectral value of the minimal polynomial of y over K.
def spectral_norm (y : L) : nnreal :=
spectral_value (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg y)))

variable (y : L)

-- We first assume that the extension is finite
section finite

variable (h_fin : finite_dimensional K L)

lemma spectral_value.is_pow_mult_of_fd : is_pow_mult (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_value.is_algebra_norm_of_fd :
  is_algebra_norm (normed_ring.to_is_norm K) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_value.is_nonarchimedean_of_fd : is_nonarchimedean (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_value.extends_norm_of_fd : function_extends (λ x : K, ∥x∥₊) (spectral_norm h_alg) :=
begin
  sorry
end

lemma spectral_value.ge_norm_of_fd {f : L → nnreal} (hf_pm : is_pow_mult f) 
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) (x : L) : 
  f x ≤ spectral_norm h_alg x :=
begin
  sorry
end

lemma spectral_value.aut_isom_of_fd (σ : L ≃ₐ[K] L) (x y : L) : 
  spectral_norm h_alg (y - x) = spectral_norm h_alg (σ (y - x)) :=
begin
  sorry
end

section normal

variable (hn : normal K L)

lemma spectral_value.unique_of_fd_normal {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f)
  (hf_iso : ∀ (σ : L ≃ₐ[K] L) (x y : L), f (y - x) = f (σ (y - x)))
  (x : L) : f x = spectral_norm h_alg x :=
begin
  sorry
end

lemma spectral_value.max_of_fd_normal {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
  (hf_ext : function_extends (λ x : K, ∥x∥₊) f) (x : L) :
  spectral_norm h_alg x = supr (λ (σ : L ≃ₐ[K] L), f (σ x)) :=
begin
  sorry
end

end normal

end finite

-- Now we let L/K be any algebraic extension

-- The spectral norm is a power-multiplicative K-algebra norm on L extending the norm on K.

lemma spectral_norm_pow_mult (y : L) (n : ℕ) (hK : ∀ k : K, ∥ k^n ∥ = ∥ k ∥^n) :
  spectral_norm h_alg (y^n) = spectral_norm h_alg y^n :=
begin
  rw spectral_norm,
  rw spectral_norm,
  rw spectral_value,
  rw spectral_value,
  sorry
end

/- lemma spectral_norm_zero : spectral_norm h_alg (0 : L) = 0 := 
begin
  have h_lr: list.range 1 = [0] := rfl,
  rw [spectral_norm, spectral_value, minpoly.zero, polynomial.nat_degree_X, h_lr],
  simp only [list.map],
  rw [polynomial.coeff_X_zero, norm_zero, nat.cast_one, nat.cast_zero, sub_zero, div_one,
    real.rpow_one, list.foldr_cons, list.foldr_nil, max_eq_right (le_refl _)],
end -/

lemma spectral_norm_zero : spectral_norm h_alg (0 : L) = 0 := 
begin
  have h_lr: list.range 1 = [0] := rfl,
  rw [spectral_norm, spectral_value, spectral_value_terms, minpoly.zero, polynomial.nat_degree_X],
  convert csupr_const,
  ext m,
  by_cases hm : m < 1,
  { rw [if_pos hm, nnreal.coe_eq, nat.lt_one_iff.mp hm, nat.cast_one, nat.cast_zero, sub_zero,
      div_one, nnreal.rpow_one, polynomial.coeff_X_zero, nnnorm_zero] },
  { rw if_neg hm },
  apply_instance,
end

/- lemma spectral_norm_zero_le (y : L) : 0 ≤ spectral_norm h_alg y := 
spectral_value_zero_le _ -/

lemma spectral_norm_zero_lt {y : L} (hy : y ≠ 0) : 0 < spectral_norm h_alg y := 
begin
  rw lt_iff_le_and_ne,
  refine ⟨zero_le _, _⟩,
  rw [spectral_norm, ne.def, eq_comm, spectral_value_eq_zero_iff],
  have h0 : polynomial.coeff (minpoly K y) 0 ≠ 0  :=
  minpoly.coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg y)) hy,
  sorry,

end

lemma spectral_norm_nonarchimedean (x y : L) (h : is_nonarchimedean (λ k : K, ⟨∥k∥, norm_nonneg _⟩)) :
  spectral_norm h_alg (x + y) ≤ max (spectral_norm h_alg x) (spectral_norm h_alg y) :=
begin
  sorry
end

lemma spectral_norm_smul (k : K) (y : L) :
  spectral_norm h_alg (k • y) ≤ ⟨∥ k ∥, norm_nonneg _⟩  * spectral_norm h_alg y :=
begin
  sorry
end

lemma spectral_norm_extends (k : K) : ∥ k ∥ = spectral_norm h_alg (algebra_map K L k) :=
begin

  sorry
end 

end spectral_norm

section spectral_valuation

variables {K : Type*} [hK : field K] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
[val : valued K Γ₀] [hv : is_rank_one val.v] [complete_space K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L) 

--instance valued_field.to_normed_field : normed_field K := sorry

--@[priority 10]
instance valued_field.to_normed_field : normed_field K := 
{ norm               := sorry,
  dist               := sorry,
  dist_self          := sorry,
  dist_comm          := sorry,
  dist_triangle      := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_eq            := sorry,
  norm_mul'          := sorry,
  ..hK }

--instance spectral_valued : valued L (multiplicative (order_dual (with_top  ℝ))) := sorry

lemma spectral_norm.is_mul_norm : is_mul_norm (spectral_norm h_alg) := sorry

lemma spectral_norm.unique {f : L → nnreal} (hf_pow : is_pow_mult f)
  (hf_alg_norm : is_algebra_norm (normed_ring.to_is_norm K) f) 
   (x : L) : f x = spectral_norm h_alg x := sorry

lemma spectral_norm.unique_field_norm_ext {f : L → nnreal} (hf_field_norm : is_mul_norm f)
   (hf_ext : function_extends (λ x : K, ∥x∥₊) f) (x : L) : f x = spectral_norm h_alg x := sorry

-- TODO: ask
-- instance spectral_norm.complete_space (h_fin : finite_dimensional K L) : complete_space L := sorry

end spectral_valuation