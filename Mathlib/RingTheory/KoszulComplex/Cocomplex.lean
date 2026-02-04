/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v w w'

open CategoryTheory Category MonoidalCategory Limits Module

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

variable {M} in
noncomputable def koszulCocomplex (x : M) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
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

namespace koszulCocomplex

variable {M} {N : Type v} [AddCommGroup N] [Module R N]

noncomputable def map (f : M →ₗ[R] N) {x : M} {y : N} (h : f x = y) :
    koszulCocomplex R x ⟶ koszulCocomplex R y :=
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

lemma map_id_refl (x : M) : koszulCocomplex.map R (M := M) .id (Eq.refl x) = 𝟙 _ := by
  ext i x
  simp only [map_hom, ModuleCat.ofHom_id, ModuleCat.exteriorPower.functor_map,
    ModuleCat.exteriorPower.map, ModuleCat.hom_id, exteriorPower.map_id, HomologicalComplex.id_f,
    LinearMap.id_coe, id_eq]
  rfl

lemma map_id (x y : M) (h : x = y) :
    koszulCocomplex.map R (M := M) .id h = eqToHom (by rw [h]) := by
  subst h
  exact map_id_refl R x

lemma map_comp {P : Type v} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) {x : M} {y : N} {z : P} (hxy : f x = y) (hyz : g y = z) :
    koszulCocomplex.map R f hxy ≫ koszulCocomplex.map R g hyz =
    koszulCocomplex.map R (g ∘ₗ f) (hxy ▸ hyz : g (f x) = z) := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  simp only [HomologicalComplex.comp_f, map_hom, ModuleCat.ofHom_comp, Functor.map_comp]

noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) {x : M} {y : N} (h : f x = y) :
    koszulCocomplex R x ≅ koszulCocomplex R y where
  hom := koszulCocomplex.map R f h
  inv := koszulCocomplex.map R f.symm (f.injective (by simpa using h.symm))
  hom_inv_id := by
    simp only [map_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap]
    exact map_id_refl R x
  inv_hom_id := by
    simp only [map_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap]
    exact map_id_refl R y

noncomputable def topXLinearEquivOfBasis {ι : Type*} [Finite ι] [LinearOrder ι] (x : M)
    (b : Basis ι R M) : (koszulCocomplex R x).X (Nat.card ι) ≃ₗ[R] R := by sorry

noncomputable abbrev ofList (l : List R) :=
  koszulCocomplex R l.get

def topHomologyLinearEquiv (l : List R) :
    (koszulCocomplex.ofList R l).homology l.length ≃ₗ[R] R ⧸ Ideal.ofList l := sorry

noncomputable def topXLinearEquivOfBasisOfList (l : List R) :
    (koszulCocomplex.ofList R l).X l.length ≃ₗ[R] R := sorry

instance free [Module.Free R M] (x : M) (i : ℕ) : Module.Free R ((koszulCocomplex R x).X i) :=
  inferInstanceAs <| Module.Free R (⋀[R]^i M)

lemma X_isZero_of_card_generators_le (x : M) {ι : Type*} [Finite ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulCocomplex R x).X i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hcard : Fintype.card ι < i := by simpa [Nat.card_eq_fintype_card] using hi
  have hempty : IsEmpty (Fin i ↪o ι) := by
    refine ⟨fun f ↦ ?_⟩
    absurd f.injective
    contrapose hcard
    simpa using Fintype.card_le_of_injective f ‹_›
  have hbotTop : (⊥ : Submodule R (⋀[R]^i M)) = ⊤ := by
    rw [← exteriorPower.span_ιMulti_orderEmbedding_of_span_eq_top (R := R) (M := M) hg i]
    convert Submodule.span_empty.symm
    exact Set.range_eq_empty_iff.mpr hempty
  have hSubsingleton : Subsingleton (⋀[R]^i M) :=
    (Submodule.subsingleton_iff R).mp <| (subsingleton_iff_bot_eq_top).mp hbotTop
  have hIsZero : IsZero (ModuleCat.of R (⋀[R]^i M)) :=
    ModuleCat.isZero_of_iff_subsingleton.mpr hSubsingleton
  simpa [koszulCocomplex, ModuleCat.exteriorPower] using hIsZero

lemma ofList_X_isZero_of_length_le (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((koszulCocomplex.ofList R l).X i) :=
  X_isZero_of_card_generators_le R l.get
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

end koszulCocomplex
