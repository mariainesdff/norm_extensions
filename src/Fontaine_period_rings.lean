import linear_algebra.adic_completion
import ring_theory.witt_vector.basic
import Cp_def

noncomputable theory

variables (p : ℕ)  [fact p.prime]

/- Fontaine period rings -/

open mv_polynomial

def Cp_x_y := mv_polynomial (fin 2) ℂ_[p]
instance : comm_ring (Cp_x_y  p) := mv_polynomial.comm_ring

def B_HT := (Cp_x_y  p) ⧸ (ideal.span {(X 0 * X 1 - 1)} : ideal (Cp_x_y  p))


def E := { x : Π (n : ℕ), 𝓞_ℂ_[p] ⧸ (ideal.span{p} : ideal 𝓞_ℂ_[p]) // ∀ n, (x (n + 1))^p = x n }
instance : comm_ring (E p) := sorry

def A_inf := witt_vector p (E p)

instance : comm_ring (A_inf p) := witt_vector.comm_ring _ _

def B_inf_plus := localization.away (p : A_inf p)
instance : comm_ring (B_inf_plus p) := localization.comm_ring

def theta : ring_hom (B_inf_plus p) ℂ_[p] := sorry

lemma theta.surjective : function.surjective (theta p) := sorry

def B_dR_plus := adic_completion (theta p).ker (B_inf_plus p)

noncomputable! instance : comm_ring (B_dR_plus p) := sorry

def B_dR := fraction_ring (B_dR_plus p)





