/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.normed.ring.seminorm
import field_theory.normal


noncomputable theory

open polynomial

open_locale polynomial

section minpoly

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

def adjoin_root.id_alg_equiv {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  adjoin_root p ≃ₐ[K] adjoin_root q :=
alg_equiv.of_alg_hom (adjoin_root.lift_hom p (adjoin_root.root q) (by 
  rw [h_eq, adjoin_root.aeval_eq, adjoin_root.mk_self])) 
  (adjoin_root.lift_hom q (adjoin_root.root p) (by
  rw [h_eq, adjoin_root.aeval_eq, adjoin_root.mk_self]))
  (power_basis.alg_hom_ext (adjoin_root.power_basis hq) (by
    rw [adjoin_root.power_basis_gen hq, alg_hom.coe_comp, function.comp_app, 
      adjoin_root.lift_hom_root, adjoin_root.lift_hom_root, alg_hom.coe_id, id.def]))
  (power_basis.alg_hom_ext (adjoin_root.power_basis hp) (by
    rw [adjoin_root.power_basis_gen hp, alg_hom.coe_comp, function.comp_app,
      adjoin_root.lift_hom_root, adjoin_root.lift_hom_root, alg_hom.coe_id, id.def]))

lemma adjoin_root.id_alg_equiv_def {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  (adjoin_root.id_alg_equiv hp hq h_eq).to_fun = (adjoin_root.lift_hom p (adjoin_root.root q) 
    (by rw [h_eq, adjoin_root.aeval_eq, adjoin_root.mk_self])) :=
rfl

lemma adjoin_root.id_alg_equiv_apply_root {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) (h_eq : p = q) :
  adjoin_root.id_alg_equiv hp hq h_eq (adjoin_root.root p) = adjoin_root.root q := 
by rw [← alg_equiv.to_fun_eq_coe, adjoin_root.id_alg_equiv_def, adjoin_root.lift_hom_root]
/- by rw [adjoin_root.id_alg_equiv, alg_equiv.of_alg_hom, alg_equiv.coe_mk, adjoin_root.lift_hom_root] -/ 

@[simp] lemma minpoly.aeval_conj (h_alg : algebra.is_algebraic K L) (σ : L ≃ₐ[K] L) (x : L) :
  (polynomial.aeval (σ x)) (minpoly K x) = 0 :=
by rw [polynomial.aeval_alg_equiv, alg_hom.coe_comp, function.comp_app, minpoly.aeval, map_zero]

@[simp] lemma minpoly.eq_of_conj (h_alg : algebra.is_algebraic K L) (σ : L ≃ₐ[K] L) (x : L) :
  minpoly K (σ x) = minpoly K x := 
begin
  have h_dvd : minpoly K x ∣ minpoly K (σ x),
  { apply minpoly.dvd,
    have hx : σ.symm (σ x) = x := σ.left_inv x,
    nth_rewrite 0 ← hx,
    rw [polynomial.aeval_alg_equiv, alg_hom.coe_comp, function.comp_app, minpoly.aeval, map_zero] },
  have h_deg : (minpoly K (σ x)).nat_degree ≤ (minpoly K x).nat_degree,
  { apply polynomial.nat_degree_le_nat_degree (minpoly.degree_le_of_ne_zero K _ (minpoly.ne_zero 
    (is_algebraic_iff_is_integral.mp (h_alg _))) (minpoly.aeval_conj h_alg σ x)) },
  exact polynomial.eq_of_monic_of_dvd_of_nat_degree_le
    (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _)))
    (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _))) h_dvd h_deg,
end


def minpoly.alg_equiv {x y : L} (h_mp : minpoly K x = minpoly K y) : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := 
alg_equiv.trans ((intermediate_field.adjoin_root_equiv_adjoin K 
  (is_algebraic_iff_is_integral.mp (h_alg _))).symm)
  (alg_equiv.trans (adjoin_root.id_alg_equiv
    (minpoly.ne_zero (is_algebraic_iff_is_integral.mp (h_alg _))) 
    (minpoly.ne_zero (is_algebraic_iff_is_integral.mp (h_alg _))) h_mp)
    (intermediate_field.adjoin_root_equiv_adjoin K(is_algebraic_iff_is_integral.mp (h_alg _))))

lemma minpoly.alg_equiv_apply {x y : L} (h_mp : minpoly K x = minpoly K y) :
  minpoly.alg_equiv h_alg h_mp ((intermediate_field.adjoin_simple.gen K x)) =
    (intermediate_field.adjoin_simple.gen K y) := 
begin
  simp only [minpoly.alg_equiv],
  rw [alg_equiv.trans_apply, ← intermediate_field.adjoin_root_equiv_adjoin_apply_root K 
    (is_algebraic_iff_is_integral.mp (h_alg _)), alg_equiv.symm_apply_apply,
    alg_equiv.trans_apply, adjoin_root.id_alg_equiv_apply_root,
    intermediate_field.adjoin_root_equiv_adjoin_apply_root K 
    (is_algebraic_iff_is_integral.mp (h_alg _))],
end

lemma minpoly.eq_of_root (h_alg : algebra.is_algebraic K L) {x y : L}
 (h_ev : (polynomial.aeval y) (minpoly K x) = 0) : minpoly K y = minpoly K x  := 
polynomial.eq_of_monic_of_associated
   (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _)))
   (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg _)))
   (irreducible.associated_of_dvd
    (minpoly.irreducible (is_algebraic_iff_is_integral.mp (h_alg _)))
    (minpoly.irreducible (is_algebraic_iff_is_integral.mp (h_alg _)))
    (minpoly.dvd K y h_ev))

lemma minpoly.conj_of_root (h_alg : algebra.is_algebraic K L) (hn : normal K L) {x y : L}
 (h_ev : (polynomial.aeval x) (minpoly K y) = 0) : ∃ (σ : L ≃ₐ[K] L), σ x = y  := 
begin
  set f : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := minpoly.alg_equiv h_alg (minpoly.eq_of_root h_alg h_ev),
  set h : L ≃ₐ[K] L := alg_equiv.lift_normal f L,
  use alg_equiv.lift_normal f L,
  simp_rw ← intermediate_field.adjoin_simple.algebra_map_gen K x,
  rw [alg_equiv.lift_normal_commutes f L, minpoly.alg_equiv_apply,
    intermediate_field.adjoin_simple.algebra_map_gen K y],
end

lemma minpoly.conj_of_root' (h_alg : algebra.is_algebraic K L) (hn : normal K L) {x y : L}
 (h_ev : (polynomial.aeval x) (minpoly K y) = 0) : ∃ (σ : L ≃ₐ[K] L), σ y = x  := 
begin
  obtain ⟨σ, hσ⟩ := minpoly.conj_of_root  h_alg hn h_ev,
  use σ.symm,
  rw [← hσ, alg_equiv.symm_apply_apply],
end

end minpoly

