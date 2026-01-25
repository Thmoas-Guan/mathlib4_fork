/-
Copyright (c) 2026 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.Monoidal

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v

open CategoryTheory Category MonoidalCategory

section GradedAlgebra

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι]
    [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i j k : ι}

def GradedAlgebra.linearGMul (h : k = i + j) : 𝒜 i →ₗ[R] (𝒜 j →ₗ[R] 𝒜 k) := sorry

@[simp]
lemma GradedAlgebra.linearGMul_eq_mul (h : k = i + j) (x : 𝒜 i) (y : 𝒜 j) :
    (GradedAlgebra.linearGMul 𝒜 h) x y = x.1 * y.1 := sorry

end GradedAlgebra

section

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

abbrev ExteriorAlgebra.ι₁ : M →ₗ[R] ⋀[R]^1 M :=
  (ExteriorAlgebra.ι R).codRestrict _ (fun c ↦ by
    rw [exteriorPower, Submodule.pow_one]
    exact ⟨c, rfl⟩)

variable {M} in
def koszulComplex (x : M) : HomologicalComplex (ModuleCat.{max u v} R) (ComplexShape.up ℕ) :=
  CochainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (GradedAlgebra.linearGMul (fun i : ℕ ↦ ⋀[R]^i M) (add_comm n 1)
      (ExteriorAlgebra.ι₁ R M x)))
    (fun n ↦ by
      simp only [← ModuleCat.ofHom_comp]
      congr
      refine LinearMap.ext fun x ↦ Subtype.ext ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, GradedAlgebra.linearGMul_eq_mul,
        LinearMap.codRestrict_apply, ← mul_assoc, CliffordAlgebra.ι_sq_scalar,
        QuadraticMap.zero_apply, map_zero, zero_mul]
      rfl)
