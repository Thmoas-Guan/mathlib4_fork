/-
Copyright (c) 2026 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
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
noncomputable def koszulComplex (x : M) :
    HomologicalComplex (ModuleCat.{max u v} R) (ComplexShape.up ℕ) :=
  CochainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (GradedAlgebra.linearGMul (fun i : ℕ ↦ ⋀[R]^i M) (add_comm n 1)
      ((exteriorPower.oneEquiv R M).symm x)))
    (fun n ↦ by
      simp only [← ModuleCat.ofHom_comp]
      congr
      refine LinearMap.ext fun x ↦ Subtype.ext ?_
      simp only [exteriorPower.oneEquiv_symm_apply, LinearMap.coe_comp, Function.comp_apply,
        GradedAlgebra.linearGMul_eq_mul, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, ← mul_assoc,
        CliffordAlgebra.ι_sq_scalar, QuadraticMap.zero_apply, map_zero, zero_mul]
      rfl)

namespace koszulComplex

variable {M} {N : Type v} [AddCommGroup N] [Module R N]

noncomputable def map (f : M →ₗ[R] N) {x : M} {y : N} (h : f x = y) :
    koszulComplex R x ⟶ koszulComplex R y :=
  CochainComplex.ofHom _ _ _ _ _ _
    (fun i ↦ (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f))
    (fun i ↦ by
      refine ModuleCat.hom_ext <| LinearMap.ext fun z ↦ Subtype.ext ?_
      simp only [ModuleCat.exteriorPower, ModuleCat.exteriorPower.functor_map,
        ModuleCat.exteriorPower.map, ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply, GradedAlgebra.linearGMul_eq_mul, exteriorPower.coe_map,
        exteriorPower.oneEquiv_symm_apply, map_mul, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.map_apply_ιMulti]
      congr
      exact funext fun _ ↦ h.symm)

lemma map_hom (f : M →ₗ[R] N) (x : M) (y : N) (h : f x = y) (i : ℕ) :
    (map R f h).f i = (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f) := rfl

lemma map_id (x y : M) (h : x = y) : koszulComplex.map R (M := M) .id h = eqToHom (by rw [h]) := by
  subst h
  ext i x
  simp only [map_hom, ModuleCat.ofHom_id, ModuleCat.exteriorPower.functor_map,
    ModuleCat.exteriorPower.map, ModuleCat.hom_id, exteriorPower.map_id, eqToHom_refl,
    HomologicalComplex.id_f, LinearMap.id_coe, id_eq]
  rfl

lemma map_comp {P : Type v} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) {x : M} {y : N} {z : P} (hxy : f x = y) (hyz : g y = z) :
    koszulComplex.map R f hxy ≫ koszulComplex.map R g hyz =
    koszulComplex.map R (g ∘ₗ f) (hxy ▸ hyz : g (f x) = z) := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  simp only [HomologicalComplex.comp_f, map_hom, ModuleCat.ofHom_comp, Functor.map_comp]

end koszulComplex
