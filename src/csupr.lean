import order.conditionally_complete_lattice
import algebra.order.with_zero
import data.real.ennreal
import topology.instances.nnreal

noncomputable theory

namespace nnreal

/- variables (α β : Type*) {ι : Sort*}
variables [nonempty ι] [cg : linear_ordered_comm_group_with_zero α]
--[decidable_eq α] -/

/- variables {α : Type*} [linear_ordered_comm_group_with_zero α] [conditionally_complete_lattice α]
[covariant_class α α (*) (≤)]

#exit -/
variables {ι : Sort*} [nonempty ι] 

lemma le_mul_cinfi {a : nnreal} {g : nnreal} {h : ι → nnreal}
  (H : ∀ j, a ≤ g * h j) : a ≤ g * infi h :=
begin
  by_cases hg : g = 0,
  { simp_rw [hg, zero_mul] at H ⊢,
    exact H (nonempty.some _inst_1), },
  { rw [mul_comm, ← mul_inv_le_iff₀ hg],
    apply le_cinfi,
    simp_rw [mul_inv_le_iff₀ hg, mul_comm],
    exact H, }
end

lemma mul_csupr_le {a : nnreal} {g : nnreal} {h : ι → nnreal}
  (H : ∀ j, g * h j ≤ a) : g * supr h ≤ a :=
begin
  by_cases hg : g = 0,
  { simp_rw [hg, zero_mul] at H ⊢,
    exact H (nonempty.some _inst_1), },
  { rw mul_comm,
    rw ← le_div_iff₀ hg,
    apply csupr_le,
    simp_rw [le_div_iff₀ hg, mul_comm],
    exact H, }
end

lemma le_cinfi_mul {a : nnreal} {g : ι → nnreal} {h : nnreal}
  (H : ∀ i, a ≤ g i * h) : a ≤ infi g * h :=
begin
  by_cases hh : h = 0,
  { simp_rw [hh, mul_zero] at H ⊢,
    exact H (nonempty.some _inst_1) },
  { simp_rw ← mul_inv_le_iff₀ hh at H ⊢,
    exact le_cinfi H, }
end

lemma csupr_mul_le {a : nnreal} {g : ι → nnreal} {h : nnreal}
  (H : ∀ i, g i * h ≤ a) : supr g * h ≤ a :=
begin
  by_cases hh : h = 0,
  { simp_rw [hh, mul_zero] at H ⊢,
    exact H (nonempty.some _inst_1) },
  { simp_rw ← le_div_iff₀ hh at H ⊢,
    exact csupr_le H, }
end

lemma le_cinfi_mul_cinfi {a : nnreal} {g h : ι → nnreal} (H : ∀ i j, a ≤ g i * h j) :
  a ≤ infi g * infi h :=
le_cinfi_mul  $ λ i, le_mul_cinfi $ H i


@[to_additive]
lemma csupr_mul_csupr_le {a : nnreal} {g h : ι → nnreal} (H : ∀ i j, g i * h j ≤ a) : 
  supr g * supr h ≤ a :=
csupr_mul_le $ λ i, mul_csupr_le $ H _


variables {f : ι → nnreal}

/- open function set


variables {α β : Type*}  [conditionally_complete_lattice α] 

lemma cinfi_range {g : β → α} {f : ι → β} : (⨅ b ∈ range f, g b) = ⨅ i, g (f i) :=
begin
  rw cinfi_subt

rw [infi_range']
end

#exit
lemma csupr_range {g : β → α} {f : ι → β} : (⨆ b ∈ range f, g b) = ⨆ i, g (f i) :=
@infi_range (order_dual α) _ _ _ _ _

lemma mul_Sup {s : set nnreal} {a : nnreal} : a * Sup s = ⨆i∈s, a * i :=
begin
  sorry
end

lemma mul_csupr' (hf : bdd_above (set.range f)) (a : nnreal) :
  a * (⨆ i, f i) = ⨆ i, a * f i :=
begin
  rw ← Sup_range,
  rw mul_Sup,
  rw csupr_range,
  sorry
end
 -/
lemma mul_csupr (hf : bdd_above (set.range f)) (a : nnreal) :
  a * (⨆ i, f i) = ⨆ i, a * f i :=
begin
  by_cases ha : a = 0,
  { rw [ha, zero_mul], simp_rw zero_mul, rw csupr_const, },
  { apply le_antisymm,
    { rw [mul_comm, ← le_div_iff₀ ha],
      apply csupr_le,
      intro i,
      rw [le_div_iff₀ ha, mul_comm],
      have h_bdd : bdd_above (set.range (λ z, a * f z)),
      { obtain ⟨b, hb⟩ := hf,
        use (a * b),
        rw mem_upper_bounds at hb ⊢,
        rintros r ⟨z, hz⟩,
        simpa [← hz, mul_le_mul_left (lt_of_le_of_ne (zero_le a) (ne.symm ha))]
        using hb (f z) (set.mem_range_self z), },
      exact le_csupr h_bdd _, },
    { apply csupr_le,
      intro z,
      simpa [mul_le_mul_left (lt_of_le_of_ne (zero_le a) (ne.symm ha))] using le_csupr hf _, }},
end

lemma csupr_mul (hf : bdd_above (set.range f)) (a : nnreal) :
  (⨆ i, f i) * a = ⨆ i, f i * a :=
by { rw [mul_comm, mul_csupr hf], simp_rw [mul_comm] }


lemma csupr_div (hf : bdd_above (set.range f)) (a : nnreal) :
  (⨆ i, f i) / a = ⨆ i, f i / a :=
by simp only [div_eq_mul_inv, csupr_mul hf]

end nnreal
