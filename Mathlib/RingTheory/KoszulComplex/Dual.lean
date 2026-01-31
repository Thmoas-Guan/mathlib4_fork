/-
Copyright (c) 2026 Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu
-/
module

public import Mathlib.RingTheory.KoszulComplex.Defs
public import Mathlib.RingTheory.KoszulComplex.Basic

/-!
# The dual of Koszul complex
-/

@[expose] public section

universe u v

open ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

noncomputable def koszulComplexDual_aux (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv {
    toFun x := ∑ i : Fin (n + 1),
      ((-1) ^ i.1 * (φ (x i))) • exteriorPower.ιMulti R n (x ∘ i.succAbove)
    map_update_add' := sorry
    map_update_smul' := sorry
    map_eq_zero_of_eq' := sorry
  }

lemma koszulComplexDual_aux_comp_eq_zero (n : ℕ) :
    koszulComplexDual_aux φ n ∘ₗ koszulComplexDual_aux φ (n + 1) = 0 := sorry

section homology_annihilator

lemma koszulComplex.mem_annihilator_homology (M : Type u) [AddCommGroup M] [Module R M] (x : M)
    (φ : M →ₗ[R] R) (i : ℕ) : φ x ∈ Module.annihilator R ((koszulComplex R x).homology i) := by
  sorry

lemma koszulComplex.mem_annihilator_homology_ofList (l : List R) (i : ℕ) :
    Ideal.ofList l ≤ Module.annihilator R ((koszulComplex.ofList R l).homology i) := by
  intro r hr
  have hr' : r ∈ Ideal.span (Set.range l.get) := by simpa only [Set.range_list_get l]
  rcases (Ideal.mem_span_range_iff_exists_fun (R := R) (x := r) (v := l.get)).1 hr' with ⟨c, hc⟩
  let φ : (Fin l.length → R) →ₗ[R] R := Fintype.linearCombination R c
  have hφ : φ l.get = r := by
    simp only [φ, ← hc, Fintype.linearCombination_apply, mul_comm (c _), smul_eq_mul]
  exact hφ ▸ mem_annihilator_homology (R := R) (M := Fin l.length → R) (x := l.get) φ i

end homology_annihilator
