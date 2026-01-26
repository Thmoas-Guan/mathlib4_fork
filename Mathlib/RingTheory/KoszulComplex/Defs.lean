/-
Copyright (c) 2026 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v w w'

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

section ModuleCat

variable {R : Type u} [CommRing R]

def ModuleCat.tensorFunctor (M : ModuleCat.{v} R) [Small.{w'} M] [UnivLE.{w, w'}] :
    ModuleCat.{w} R ⥤ ModuleCat.{w'} R := sorry

end ModuleCat

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

noncomputable abbrev ofList (l : List R) :=
  koszulComplex R l.get

def topHomologyLinearEquiv (l : List R) :
    (koszulComplex.ofList R l).homology l.length ≃ₗ[R] R ⧸ Ideal.ofList l := sorry

end koszulComplex

section changegenerators

variable [IsNoetherianRing R] [IsLocalRing R]

def koszulComplex.iso_of_minimal_generators {I : Ideal R} {l : List R} (eq : Ideal.ofList l = I)
    (min : l.length = I.spanFinrank) :
    letI : Fintype I.generators :=
      (Submodule.FG.finite_generators I.fg_of_isNoetherianRing).fintype
    koszulComplex.ofList R I.generators.toFinset.toList ≅ koszulComplex.ofList R l :=
  sorry

end changegenerators

section basechange

variable (S : Type u) [CommRing S] (f : R →+* S)

def koszulComplex.baseChange_iso (l : List R) (l' : List S) (eqmap : l.map f = l') :
    koszulComplex.ofList S l' ≅ ((ModuleCat.extendScalars f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulComplex.ofList R l) :=
  sorry

end basechange

section IsRegular

open RingTheory.Sequence

lemma koszulComplex.exactAt_of_lt_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i < rs.length) : (koszulComplex.ofList R rs).ExactAt i := by
  sorry

theorem koszulComplex.exactAt_of_ne_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i ≠ rs.length) : (koszulComplex.ofList R rs).ExactAt i := by
  sorry

lemma koszulComplex.free_of_free (M : Type u) [AddCommGroup M] [Module R M] [Module.Free R M]
    (x : M) (i : ℕ) : Module.Free R ((koszulComplex R x).X i) := by
  sorry

end IsRegular
