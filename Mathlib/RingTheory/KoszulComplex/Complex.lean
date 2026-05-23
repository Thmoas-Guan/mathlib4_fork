/-
Copyright (c) 2026 Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu
-/
module

public import Mathlib.RingTheory.KoszulComplex.Preliminaries
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v

open CategoryTheory Category MonoidalCategory Limits Module ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

/-- The alternating map on `(n + 1)`-tuples whose induced linear map is the Koszul differential. -/
noncomputable def koszulComplexAuxAlternating (n : ℕ) :
    M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M :=
  AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))

lemma koszulComplexAuxAlternating_apply (n : ℕ) (x : Fin (n + 1) → M) :
    koszulComplexAuxAlternating φ n x =
      ∑ i : Fin (n + 1),
        ((-1 : R) ^ (i : ℕ) * φ (x i)) • exteriorPower.ιMulti R n (i.removeNth x) := by
  rw [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hremove : x ∘ i.succAbove = i.removeNth x := rfl
  simp [LinearMap.smulRight_apply, AlternatingMap.smul_apply, ← hremove,
    ← Int.cast_smul_eq_zsmul R, smul_smul]

/-- The auxiliary differential used to build the Koszul complex. -/
noncomputable def koszulComplexAux (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (koszulComplexAuxAlternating (R := R) (M := M) φ n)

lemma koszulComplexAux_comp_eq_zero (n : ℕ) :
    koszulComplexAux φ n ∘ₗ koszulComplexAux φ (n + 1) = 0 := by
  let β : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] ⋀[R]^n M :=
    φ.smulRight (φ.smulRight (exteriorPower.ιMulti R n))
  have hβ : ∀ x y, β x y = β y x := by
    intro x y
    ext v
    simp [β, smul_smul, mul_comm]
  -- Unfold the concrete Koszul composite into the twice-uncurried alternating construction.
  have hcomp :
      (koszulComplexAux φ n).compAlternatingMap (koszulComplexAuxAlternating φ (n + 1)) =
        AlternatingMap.alternatizeUncurryFin (AlternatingMap.alternatizeUncurryFinLM ∘ₗ β) := by
    ext v
    simp [koszulComplexAux, koszulComplexAuxAlternating, β,
      AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum, map_sum, smul_smul]
  -- Transport the linear-map composite to the alternating-map side,
  -- where the symmetry theorem applies directly.
  rw [show koszulComplexAux φ (n + 1) =
      exteriorPower.alternatingMapLinearEquiv (koszulComplexAuxAlternating φ (n + 1)) by rfl]
  rw [← exteriorPower.alternatingMapLinearEquiv_comp]
  rw [LinearEquiv.map_eq_zero_iff]
  rw [hcomp]
  exact AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric hβ

set_option backward.isDefEq.respectTransparency false in
noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (koszulComplexAux φ n))
    (fun n ↦ by simp [← ModuleCat.ofHom_comp, koszulComplexAux_comp_eq_zero])

lemma koszulComplex.X_eq_exteriorPower (i : ℕ) :
    (koszulComplex φ).X i = ModuleCat.of R (⋀[R]^i M) := rfl

lemma koszulComplex.d_eq_aux (i : ℕ) :
    (koszulComplex φ).d (i + 1) i = ModuleCat.ofHom (koszulComplexAux φ i) := by
  simp [koszulComplex]

section DifferentialGradedAlgebra

end DifferentialGradedAlgebra

namespace koszulComplex

variable {N : Type v} [AddCommGroup N] [Module R N]

noncomputable def ofList (l : List R) := koszulComplex (Fintype.linearCombination R l.get)

section functoriality

lemma mapAuxAlternating_apply (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ)
    (i : ℕ) (v : Fin (i + 1) → M) :
    ((koszulComplexAuxAlternating φ' i) (f ∘ v) : ⋀[R]^i N) =
      exteriorPower.map i f ((koszulComplexAuxAlternating φ i) v) := by
  calc
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ' (f (v x)) •
          exteriorPower.ιMulti R i (x.removeNth (f ∘ v)) := by
      simp [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ (v x) •
          exteriorPower.ιMulti R i (f ∘ x.removeNth v) := by
      refine Finset.sum_congr rfl (fun x hx ↦ ?_)
      simp only [← h, LinearMap.coe_comp, Function.comp_apply]
      rfl
    _ = exteriorPower.map i f ((koszulComplexAuxAlternating φ i) v) := by
      rw [koszulComplexAuxAlternating, AlternatingMap.alternatizeUncurryFin_apply]
      simp [map_sum, map_smul, exteriorPower.map_apply_ιMulti]

lemma map_aux_comm (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) (i : ℕ) :
    ModuleCat.ofHom (exteriorPower.map (i + 1) f) ≫ ModuleCat.ofHom (koszulComplexAux φ' i) =
      ModuleCat.ofHom (koszulComplexAux φ i) ≫ ModuleCat.ofHom (exteriorPower.map i f) := by
  ext v
  simp [koszulComplexAux, mapAuxAlternating_apply (φ := φ) (f := f) (φ' := φ') h]

noncomputable def map (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ⟶ koszulComplex φ' :=
  ChainComplex.ofHom
    (fun i ↦ ModuleCat.ofHom (exteriorPower.map i f))
    (fun i ↦ by simpa [d_eq_aux] using map_aux_comm φ f φ' h i)

variable {L : Type v} [AddCommGroup L] [Module R L]

variable {φ} in
lemma map_comp_condition {f : M →ₗ[R] N} {φ' : N →ₗ[R] R} {g : N →ₗ[R] L} {φ'' : L →ₗ[R] R}
    (h : φ' ∘ₗ f = φ) (h' : φ'' ∘ₗ g = φ') : φ'' ∘ₗ (g ∘ₗ f) = φ := by
  simp [← h, ← h', LinearMap.comp_assoc]

lemma map_comp (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (g : N →ₗ[R] L) (φ'' : L →ₗ[R] R)
    (h : φ' ∘ₗ f = φ) (h' : φ'' ∘ₗ g = φ') :
    koszulComplex.map φ f φ' h ≫ koszulComplex.map φ' g φ'' h' =
      koszulComplex.map φ (g ∘ₗ f) φ'' (map_comp_condition h h') := by
  ext i x
  simp [map, X_eq_exteriorPower, exteriorPower.map_comp]

noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ≅ koszulComplex φ' where
  hom := koszulComplex.map φ f φ' h
  inv := koszulComplex.map φ' f.symm φ ((f.comp_toLinearMap_symm_eq φ' φ).mpr h.symm)
  hom_inv_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]
  inv_hom_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]

end functoriality

section specialX

noncomputable def XZeroLinearEquivRing : (koszulComplex φ).X 0 ≃ₗ[R] R :=
  exteriorPower.zeroEquiv R M

set_option backward.isDefEq.respectTransparency false in
lemma X_isZero_of_card_generators_le {ι : Type*} [Finite ι] [LinearOrder ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulComplex φ).X i) :=
  ModuleCat.isZero_of_iff_subsingleton.mpr (subsingleton_of_card_generators_le R M g hg i hi)

lemma ofList_X_isZero_of_length_le (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((ofList l).X i) := X_isZero_of_card_generators_le _
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

end specialX

section induction

def X_equiv_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    (koszulComplex.ofList l).X 0 ≃ₗ[R] (koszulComplex.ofList l').X 0 := sorry

def X_equiv_prod {l l' : List R} {a : R} (eq : l = l' ++ [a]) (n : ℕ) :
    (koszulComplex.ofList l).X (n + 1) ≃ₗ[R]
    ((koszulComplex.ofList l').X (n + 1) × (koszulComplex.ofList l').X n) := sorry

lemma d_apply_eq_zero {l l' : List R} {a : R} (eq : l = l' ++ [a])
    (x : (koszulComplex.ofList l).X (0 + 1)) :
    (koszulComplex.ofList l).d (0 + 1) 0 x = (X_equiv_zero eq).symm
      ((koszulComplex.ofList l').d (0 + 1) 0 (X_equiv_prod eq 0 x).1 +
        a • (X_equiv_prod eq 0 x).2) := by
  sorry

lemma d_apply_eq_pos {l l' : List R} {a : R} (eq : l = l' ++ [a]) (n : ℕ)
    (x : (koszulComplex.ofList l).X (n + 1 + 1)) :
    (koszulComplex.ofList l).d (n + 1 + 1) (n + 1) x = (X_equiv_prod eq n).symm
      ⟨(koszulComplex.ofList l').d (n + 1 + 1) (n + 1) (X_equiv_prod eq (n + 1) x).1 +
        ((-1 : R) ^ (n + 1) * a) • (X_equiv_prod eq (n + 1) x).2,
          (koszulComplex.ofList l').d (n + 1) n (X_equiv_prod eq (n + 1) x).2⟩ := by
  sorry

noncomputable def from_ofList_hom_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    (ofList l').X 0 ⟶ (ofList l).X 0 :=
  ModuleCat.ofHom (X_equiv_zero eq).symm.toLinearMap

noncomputable def from_ofList_hom_pos {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    (ofList l').X (i + 1) ⟶ (ofList l).X (i + 1) :=
  ModuleCat.ofHom ((X_equiv_prod eq i).symm.toLinearMap.comp (LinearMap.inl R _ _))

lemma from_ofList_hom_comm_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    from_ofList_hom_pos eq 0 ≫ (ofList l).d (0 + 1) 0 =
    (ofList l').d (0 + 1) 0 ≫ from_ofList_hom_zero eq := by
  ext x
  change (ofList l).d (0 + 1) 0 ((X_equiv_prod eq 0).symm (LinearMap.inl R _ _ x)) =
    (X_equiv_zero eq).symm ((ofList l').d (0 + 1) 0 x)
  rw [d_apply_eq_zero eq]
  simp

lemma from_ofList_hom_comm_pos {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    from_ofList_hom_pos eq (i + 1) ≫ (ofList l).d (i + 1 + 1) (i + 1) =
      (ofList l').d (i + 1 + 1) (i + 1) ≫ from_ofList_hom_pos eq i := by
  ext x
  change (ofList l).d (i + 1 + 1) (i + 1) ((X_equiv_prod eq (i + 1)).symm (LinearMap.inl R _ _ x)) =
    (X_equiv_prod eq i).symm (LinearMap.inl R _ _ ((ofList l').d (i + 1 + 1) (i + 1) x))
  rw [d_apply_eq_pos eq]
  simp

noncomputable def from_ofList {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    koszulComplex.ofList l' ⟶ koszulComplex.ofList l :=
  ChainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => from_ofList_hom_zero eq
      | i + 1 => from_ofList_hom_pos eq i)
    (fun i ↦
      match i with
      | 0 => from_ofList_hom_comm_zero eq
      | i + 1 => from_ofList_hom_comm_pos eq i)

noncomputable abbrev ofList_up_one (l : List R) : ChainComplex (ModuleCat R) ℕ :=
  (ofList l).augment (X := ModuleCat.of R PUnit) 0 (by simp)

/--
The canonical isomorphism of homology for augumenting with zero object.
May need to construct by cases whether `i = 0`.
-/
noncomputable abbrev ofList_up_one_homology_iso (l : List R) (i : ℕ) :
    (ofList_up_one l).homology (i + 1) ≅ (ofList l).homology i := sorry

noncomputable def to_up_one_hom {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    (ofList l).X (i + 1) ⟶ (ofList_up_one l').X (i + 1) :=
  ModuleCat.ofHom ((LinearMap.snd R _ _).comp (X_equiv_prod eq i).toLinearMap)

lemma to_self_hom_comm {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    to_up_one_hom eq (i + 1) ≫ (ofList l').d (i + 1) i =
      (ofList l).d (i + 1 + 1) (i + 1) ≫ to_up_one_hom eq i := by
  ext x
  change (ofList l').d (i + 1) i (X_equiv_prod eq (i + 1) x).2 =
    ((X_equiv_prod eq i) ((ofList l).d (i + 1 + 1) (i + 1) x)).2
  rw [d_apply_eq_pos eq]
  simp

noncomputable def to_ofList_up_one {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    koszulComplex.ofList l ⟶ koszulComplex.ofList_up_one l' :=
  ChainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => 0
      | i + 1 => to_up_one_hom eq i)
    (fun i ↦
      match i with
      | 0 => by
        simp only [Nat.reduceAdd, ChainComplex.augment_X_zero, ChainComplex.augment_X_succ,
          ChainComplex.augment_d_one_zero, comp_zero]
        exact comp_zero.symm
      | i + 1 => to_self_hom_comm eq i)

lemma from_ofList_comp_to_ofList_up_one_eq_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    from_ofList eq ≫ to_ofList_up_one eq = 0 := by
  sorry

noncomputable def shortComplex_of_eq {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) where
  f := from_ofList eq
  g := to_ofList_up_one eq
  zero := from_ofList_comp_to_ofList_up_one_eq_zero eq

noncomputable def shortComplex_of_eq_shortExact {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    (shortComplex_of_eq eq).ShortExact where
  exact := sorry
  mono_f := sorry
  epi_g := sorry

lemma shortComplex_of_eq_δ_apply {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    (shortComplex_of_eq_shortExact eq).δ (i + 1) i rfl =
      ((-1 : R) ^ i * a) • (ofList_up_one_homology_iso l' i).hom := by
  sorry

end induction

section H0

/-
Proof route: using the inductivity above, construct the isomorphism using long exact sequence of
homology by induction on length.
It would be better to have a separate isomorphism for the induction step `l = l' ++ [a]`
`(ofList l).homology 0 ≃ ((ofList l').homology 0) ⧸ a • (⊤ : Submodule R ((ofList l').homology 0))`
-/

noncomputable def zeroHomologyLinearEquiv (l : List R) :
    (ofList l).homology 0 ≃ₗ[R] R ⧸ Ideal.ofList l := sorry

end H0

section regular

open RingTheory.Sequence

/-
Proof route: proof exactness using vanishing of homology, using the inductivity above,
obtain homology `IsZero` from long exact sequence of homology and sequence being regular.
-/

lemma exactAt_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i ≠ 0) : (ofList rs).ExactAt i := by
  sorry

end regular

/-
section basechange

variable (S : Type (max u v)) [CommRing S] (f : R →+* S)

instance (T : Type v) [CommRing T] (g : R →+* T) :
    (ModuleCat.extendScalars.{u, v, u} g).Additive where
  map_add {X Y a b} := by
    simp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
      ModuleCat.hom_add, LinearMap.baseChange_add]
    rfl

open TensorProduct in
noncomputable def baseChange_iso (l : List R) (l' : List S) (eqmap : l.map f = l') :
    ofList l' ≅ ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (ofList l) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ LinearEquiv.toModuleIso ?_) (fun i j ↦ ?_)
  · sorry
  · sorry

end basechange
-/

end koszulComplex
