/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.KoszulComplex.Complex
public import Mathlib.RingTheory.KoszulComplex.Cocomplex

/-!
# Homotopy on Koszul complex
-/

@[expose] public section

universe u v

open ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

section homology_annihilator

lemma koszulComplex.mem_annihilator_homology (M : Type u) [AddCommGroup M] [Module R M] (x : M)
    (φ : M →ₗ[R] R) (i : ℕ) : φ x ∈ Module.annihilator R ((koszulCocomplex R x).homology i) := by
  sorry

lemma koszulComplex.mem_annihilator_homology_ofList (l : List R) (i : ℕ) :
    Ideal.ofList l ≤ Module.annihilator R ((koszulCocomplex.ofList R l).homology i) := by
  intro r hr
  have hr' : r ∈ Ideal.span (Set.range l.get) := by simpa only [Set.range_list_get l]
  rcases (Ideal.mem_span_range_iff_exists_fun (R := R) (x := r) (v := l.get)).1 hr' with ⟨c, hc⟩
  let φ : (Fin l.length → R) →ₗ[R] R := Fintype.linearCombination R c
  have hφ : φ l.get = r := by
    simp only [φ, ← hc, Fintype.linearCombination_apply, mul_comm (c _), smul_eq_mul]
  exact hφ ▸ mem_annihilator_homology (R := R) (M := Fin l.length → R) (x := l.get) φ i

end homology_annihilator
