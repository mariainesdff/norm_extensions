/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/

import field_theory.normal

/-!
# Minpoly

We prove some auxiliary lemmas about minimal polynomials.

## Main Definitions

* `minpoly.alg_equiv` : the canonical `alg_equiv` between `K⟮x⟯`and `K⟮y⟯`, sending `x` to `y`, where
  `x` and `y` have the same minimal polynomial over `K`, sending `x` to `y`.


## Main Results

* `minpoly.eq_of_conj` : For any `σ : L ≃ₐ[K] L` and `x : L`, the minimal polynomials of `x` and 
  `σ x` are equal.
* `minpoly.conj_of_root` :If `y : L` is a root of `minpoly K x`, then we can find `σ : L ≃ₐ[K] L)` 
   with `σ x = y`. That is, `x` and `y` are Galois conjugates.

## Tags

minpoly, adjoin_root, conj
-/

noncomputable theory

open polynomial intermediate_field alg_equiv

open_locale polynomial

section minpoly

variables {K L : Type*} [field K] [field L] [algebra K L]

namespace adjoin_root

/-- The canonical algebraic equivalence between `adjoin_root p` and `adjoin_root q`, where
  the two polynomial `p q : K[X]` are equal.-/
def id_alg_equiv {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  adjoin_root p ≃ₐ[K] adjoin_root q :=
of_alg_hom (lift_hom p (root q) (by rw [h_eq, aeval_eq, mk_self])) 
  (lift_hom q (root p) (by rw [h_eq, aeval_eq, mk_self]))
  (power_basis.alg_hom_ext (power_basis hq) (by rw [power_basis_gen hq, alg_hom.coe_comp, 
    function.comp_app, lift_hom_root, lift_hom_root, alg_hom.coe_id, id.def]))
  (power_basis.alg_hom_ext (power_basis hp) (by rw [power_basis_gen hp, alg_hom.coe_comp,
    function.comp_app, lift_hom_root, lift_hom_root, alg_hom.coe_id, id.def]))

lemma id_alg_equiv_def {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  (id_alg_equiv hp hq h_eq).to_fun = (lift_hom p (root q) (by rw [h_eq, aeval_eq, mk_self])) :=
rfl

/-- `id_alg_equiv` sends `adjoin_root.root p` to `adjoin_root.root q`. -/
lemma id_alg_equiv_apply_root {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  id_alg_equiv hp hq h_eq (root p) = root q := 
by rw [← to_fun_eq_coe, id_alg_equiv_def, lift_hom_root]

end adjoin_root

namespace minpoly

/-- Given any `σ : L ≃ₐ[K] L` and any `x : L`, the minimal polynomial of `x` vanishes at `σ x`. -/
@[simp] lemma aeval_conj (σ : L ≃ₐ[K] L) (x : L) : (polynomial.aeval (σ x)) (minpoly K x) = 0 :=
by rw [polynomial.aeval_alg_equiv, alg_hom.coe_comp, function.comp_app, aeval, map_zero]

/-- For any `σ : L ≃ₐ[K] L` and `x : L`, the minimal polynomials of `x` and `σ x` are equal. -/
@[simp] lemma eq_of_conj (h_alg : algebra.is_algebraic K L) (σ : L ≃ₐ[K] L) (x : L) :
  minpoly K (σ x) = minpoly K x := 
begin
  have h_dvd : minpoly K x ∣ minpoly K (σ x),
  { apply dvd,
    have hx : σ.symm (σ x) = x := σ.left_inv x,
    nth_rewrite 0 ← hx,
    rw [polynomial.aeval_alg_equiv, alg_hom.coe_comp, function.comp_app, aeval, map_zero] },
  have h_deg : (minpoly K (σ x)).nat_degree ≤ (minpoly K x).nat_degree,
  { apply polynomial.nat_degree_le_nat_degree (degree_le_of_ne_zero K _ (ne_zero 
    (is_algebraic_iff_is_integral.mp (h_alg _))) (aeval_conj σ x)) },
  exact polynomial.eq_of_monic_of_dvd_of_nat_degree_le
    (monic (is_algebraic_iff_is_integral.mp (h_alg _)))
    (monic (is_algebraic_iff_is_integral.mp (h_alg _))) h_dvd h_deg,
end

/-- The canonical `alg_equiv` between `K⟮x⟯`and `K⟮y⟯`, sending `x` to `y`, where `x` and `y` have 
  the same minimal polynomial over `K`. -/
def alg_equiv (h_alg : algebra.is_algebraic K L) {x y : L} (h_mp : minpoly K x = minpoly K y) :
  K⟮x⟯ ≃ₐ[K] K⟮y⟯ := 
trans ((adjoin_root_equiv_adjoin K (is_algebraic_iff_is_integral.mp (h_alg _))).symm)
  (trans (adjoin_root.id_alg_equiv (ne_zero (is_algebraic_iff_is_integral.mp (h_alg _))) 
    (ne_zero (is_algebraic_iff_is_integral.mp (h_alg _))) h_mp)
    (adjoin_root_equiv_adjoin K(is_algebraic_iff_is_integral.mp (h_alg _))))

/-- `minpoly.alg_equiv` sends the generator of `K⟮x⟯` to the generator of `K⟮y⟯`. -/
lemma alg_equiv_apply (h_alg : algebra.is_algebraic K L) {x y : L} 
  (h_mp : minpoly K x = minpoly K y) :
  alg_equiv h_alg h_mp ((adjoin_simple.gen K x)) = (adjoin_simple.gen K y) := 
begin
  simp only [alg_equiv],
  rw [trans_apply, ← adjoin_root_equiv_adjoin_apply_root K
    (is_algebraic_iff_is_integral.mp (h_alg _)), symm_apply_apply,
    trans_apply, adjoin_root.id_alg_equiv_apply_root,
    adjoin_root_equiv_adjoin_apply_root K (is_algebraic_iff_is_integral.mp (h_alg _))],
end

/-- If `y : L` is a root of `minpoly K x`, then `minpoly K y = minpoly K x`. -/
lemma eq_of_root (h_alg : algebra.is_algebraic K L) {x y : L}
 (h_ev : (polynomial.aeval y) (minpoly K x) = 0) : minpoly K y = minpoly K x  := 
polynomial.eq_of_monic_of_associated (monic (is_algebraic_iff_is_integral.mp (h_alg _)))
  (monic (is_algebraic_iff_is_integral.mp (h_alg _)))
  (irreducible.associated_of_dvd (irreducible (is_algebraic_iff_is_integral.mp (h_alg _)))
    (irreducible (is_algebraic_iff_is_integral.mp (h_alg _))) (dvd K y h_ev))

/-- If `y : L` is a root of `minpoly K x`, then we can find `σ : L ≃ₐ[K] L)` with `σ x = y`.
  That is, `x` and `y` are Galois conjugates. -/
lemma conj_of_root (h_alg : algebra.is_algebraic K L) (hn : normal K L) {x y : L}
 (h_ev : (polynomial.aeval x) (minpoly K y) = 0) : ∃ (σ : L ≃ₐ[K] L), σ x = y  := 
begin
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := alg_equiv h_alg (eq_of_root h_alg h_ev),
  use lift_normal f L,
  simp_rw ← adjoin_simple.algebra_map_gen K x,
  rw [lift_normal_commutes f L, alg_equiv_apply, adjoin_simple.algebra_map_gen K y],
end

/-- If `y : L` is a root of `minpoly K x`, then we can find `σ : L ≃ₐ[K] L)` with `σ y = x`.
  That is, `x` and `y` are Galois conjugates. -/
lemma conj_of_root' (h_alg : algebra.is_algebraic K L) (hn : normal K L) {x y : L}
 (h_ev : (polynomial.aeval x) (minpoly K y) = 0) : ∃ (σ : L ≃ₐ[K] L), σ y = x  := 
begin
  obtain ⟨σ, hσ⟩ := conj_of_root h_alg hn h_ev,
  use σ.symm,
  rw [← hσ, symm_apply_apply],
end

end minpoly

end minpoly