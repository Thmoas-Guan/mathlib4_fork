/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Definition of Koszul cocomplex
-/

@[expose] public section

universe u v w w'

open CategoryTheory Category MonoidalCategory Limits Module

section GradedAlgebra

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι]
    [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i j k : ι}

def GradedAlgebra.linearGMul (h : k = i + j) : 𝒜 i →ₗ[R] (𝒜 j →ₗ[R] 𝒜 k) :=
  h ▸ DirectSum.gMulLHom (R := R) (A := fun n ↦ 𝒜 n)

@[simp]
lemma GradedAlgebra.linearGMul_eq_mul (h : k = i + j) (x : 𝒜 i) (y : 𝒜 j) :
    (GradedAlgebra.linearGMul 𝒜 h) x y = x.1 * y.1 := by
  subst h
  rfl

end GradedAlgebra

section

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

noncomputable abbrev koszulCocomplexAux (x : M) (n : ℕ) :
    ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M :=
  GradedAlgebra.linearGMul (fun i : ℕ ↦ ⋀[R]^i M) (add_comm n 1)
    ((exteriorPower.oneEquiv R M).symm x)

set_option backward.isDefEq.respectTransparency false in
variable {M} in
noncomputable def koszulCocomplex (x : M) : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (koszulCocomplexAux R M x n))
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

/-- The differential of `koszulCocomplex R x` is exterior multiplication by `x` in each degree. -/
theorem d_eq_aux (x : M) (i : ℕ) :
    (koszulCocomplex R x).d i (i + 1) = ModuleCat.ofHom (koszulCocomplexAux R M x i) := by
  simp [koszulCocomplex]

noncomputable abbrev ofList (l : List R) :=
  koszulCocomplex R l.get

instance free [Module.Free R M] (x : M) (i : ℕ) : Module.Free R ((koszulCocomplex R x).X i) :=
  inferInstanceAs <| Module.Free R (⋀[R]^i M)

variable {M} {N : Type v} [AddCommGroup N] [Module R N]

section functoriality

set_option backward.isDefEq.respectTransparency false in
noncomputable def map (f : M →ₗ[R] N) {x : M} {y : N} (h : f x = y) :
    koszulCocomplex R x ⟶ koszulCocomplex R y :=
  CochainComplex.ofHom
    (fun i ↦ (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f))
    (fun i ↦ ModuleCat.hom_ext <| LinearMap.ext fun z ↦ Subtype.ext
      (by simp [koszulCocomplex, ModuleCat.exteriorPower, ModuleCat.exteriorPower.map,
        koszulCocomplexAux, exteriorPower.oneEquiv_symm_apply, h]))

lemma map_hom (f : M →ₗ[R] N) (x : M) (y : N) (h : f x = y) (i : ℕ) :
    (map R f h).f i = (ModuleCat.exteriorPower.functor R i).map (ModuleCat.ofHom f) := rfl

lemma map_id_refl (x : M) : koszulCocomplex.map R (M := M) .id (Eq.refl x) = 𝟙 _ := by
  ext i x
  simp only [map_hom, ModuleCat.ofHom_id, ModuleCat.exteriorPower.functor_map,
    ModuleCat.exteriorPower.map, ModuleCat.hom_id, exteriorPower.map_id, HomologicalComplex.id_f,
    LinearMap.id_coe, id_eq]
  rfl

lemma map_id (x y : M) (h : x = y) : koszulCocomplex.map R (M := M) .id h =
  eqToHom (congrArg _ h) := by
  subst h
  exact map_id_refl R x

set_option backward.isDefEq.respectTransparency false in
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

end functoriality

section specialX

noncomputable def XZeroLinearEquivRing (x : M) : (koszulCocomplex R x).X 0 ≃ₗ[R] R :=
  exteriorPower.zeroEquiv R M

/-- The top-cardinality subset type consists only of the full finite set. -/
@[reducible]
noncomputable instance nonempty_unique_top_powersetCard {ι : Type*} [Finite ι] :
    (Unique (Set.powersetCard ι (Nat.card ι))) where
  default :=
    letI : Fintype ι := Fintype.ofFinite ι
    Set.powersetCard.ofCard (s := Finset.univ) (by simp [Nat.card_eq_fintype_card])
  uniq s := by
    let : Fintype ι := Fintype.ofFinite ι
    apply Subtype.ext
    simp [← Finset.card_eq_iff_eq_univ]

noncomputable def topXLinearEquivOfBasis {ι : Type*} [Finite ι] [LinearOrder ι] (x : M)
    (b : Basis ι R M) : (koszulCocomplex R x).X (Nat.card ι) ≃ₗ[R] R :=
  (b.exteriorPower (Nat.card ι)).equivFun.trans (LinearEquiv.funUnique _ R R)

noncomputable def topXLinearEquivOfBasisOfList (l : List R) :
    (ofList R l).X l.length ≃ₗ[R] R := by
  have : l.length = Nat.card (Fin l.length) := by simp
  rw [this]
  exact topXLinearEquivOfBasis R l.get (Pi.basisFun R (Fin l.length))

lemma X_isZero_of_card_generators_le (x : M) {ι : Type*} [Finite ι] [LinearOrder ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulCocomplex R x).X i) :=
  ModuleCat.isZero_of_iff_subsingleton.mpr (subsingleton_of_card_generators_le R M g hg i hi)

lemma ofList_X_isZero_of_length_le (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((koszulCocomplex.ofList R l).X i) :=
  X_isZero_of_card_generators_le R l.get
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

end specialX

section induction

variable {R}

def X_equiv_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    (koszulCocomplex.ofList R l).X 0 ≃ₗ[R] (koszulCocomplex.ofList R l').X 0 := sorry

def X_equiv_prod {l l' : List R} {a : R} (eq : l = l' ++ [a]) (n : ℕ) :
    (koszulCocomplex.ofList R l).X (n + 1) ≃ₗ[R]
    ((koszulCocomplex.ofList R l').X (n + 1) × (koszulCocomplex.ofList R l').X n) := sorry

lemma d_apply_eq_zero {l l' : List R} {a : R} (eq : l = l' ++ [a])
    (x : (koszulCocomplex.ofList R l).X 0) :
    (koszulCocomplex.ofList R l).d 0 (0 + 1) x = (X_equiv_prod eq 0).symm
      ⟨(koszulCocomplex.ofList R l').d 0 (0 + 1) (X_equiv_zero eq x), a • (X_equiv_zero eq x)⟩ := by
  sorry

lemma d_apply_eq_pos {l l' : List R} {a : R} (eq : l = l' ++ [a]) (n : ℕ)
    (x : (koszulCocomplex.ofList R l).X (n + 1)) :
    (koszulCocomplex.ofList R l).d (n + 1) (n + 1 + 1) x = (X_equiv_prod eq (n + 1)).symm
      ⟨(koszulCocomplex.ofList R l').d (n + 1) (n + 1 + 1) (X_equiv_prod eq n x).1,
        (koszulCocomplex.ofList R l').d n (n + 1) (X_equiv_prod eq n x).2 +
          ((-1 : R) ^ (n + 1) * a) • (X_equiv_prod eq n x).1⟩ := by
  sorry

variable (R) in
noncomputable abbrev ofList_up_one (l : List R) : CochainComplex (ModuleCat R) ℕ :=
  (ofList R l).augment (X := ModuleCat.of R PUnit) 0 (by simp)

/--
The canonical isomorphism of homology for augumenting with zero object.
May need to construct by cases whether `i = 0`.
-/
noncomputable abbrev ofList_up_one_homology_iso (l : List R) (i : ℕ) :
    (ofList_up_one R l).homology (i + 1) ≅ (ofList R l).homology i := sorry

noncomputable def from_ofList_up_one_hom {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    (ofList_up_one R l').X (i + 1) ⟶ (ofList R l).X (i + 1) :=
  ModuleCat.ofHom ((X_equiv_prod eq i).symm.toLinearMap.comp (LinearMap.inr R _ _))

lemma from_ofList_up_one_hom_comm {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    from_ofList_up_one_hom eq i ≫ (ofList R l).d (i + 1) (i + 1 + 1) =
      (ofList R l').d i (i + 1) ≫ from_ofList_up_one_hom eq (i + 1) := by
  ext x
  change (ofList R l).d (i + 1) (i + 1 + 1) ((X_equiv_prod eq i).symm ((LinearMap.inr R _ _) x)) =
    (X_equiv_prod eq (i + 1)).symm ((LinearMap.inr R _ _) ((ofList R l').d i (i + 1) x))
  rw [d_apply_eq_pos eq i]
  simp

noncomputable def from_ofList_up_one {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    koszulCocomplex.ofList_up_one R l' ⟶ koszulCocomplex.ofList R l :=
  CochainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => 0
      | i + 1 => from_ofList_up_one_hom eq i)
    (fun i ↦
      match i with
      | 0 => by
        simp only [CochainComplex.augment_X_zero, Nat.reduceAdd, CochainComplex.augment_X_succ,
          CochainComplex.augment_d_zero_one, zero_comp]
        exact zero_comp
      | i + 1 => by simpa using from_ofList_up_one_hom_comm eq i)

noncomputable def to_self_hom_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    (ofList R l).X 0 ⟶ (ofList R l').X 0 :=
  ModuleCat.ofHom (X_equiv_zero eq).toLinearMap

noncomputable def to_self_hom_pos {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    (ofList R l).X (i + 1) ⟶ (ofList R l').X (i + 1) :=
  ModuleCat.ofHom ((LinearMap.fst R _ _).comp (X_equiv_prod eq i).toLinearMap)

lemma to_self_hom_comm_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    to_self_hom_zero eq ≫ (ofList R l').d 0 (0 + 1) =
      (ofList R l).d 0 (0 + 1) ≫ to_self_hom_pos eq 0 := by
  ext x
  change ((ofList R l').d 0 (0 + 1) (X_equiv_zero eq x)) =
    (X_equiv_prod eq 0 ((ofList R l).d 0 (0 + 1) x)).1
  rw [d_apply_eq_zero eq]
  simp

lemma to_self_hom_comm_pos {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    to_self_hom_pos eq i ≫ (ofList R l').d (i + 1) (i + 1 + 1) =
      (ofList R l).d (i + 1) (i + 1 + 1) ≫ to_self_hom_pos eq (i + 1) := by
  ext x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  change ((ofList R l').d (i + 1) (i + 1 + 1)) (X_equiv_prod eq i x).1 =
    (X_equiv_prod eq (i + 1) ((ofList R l).d (i + 1) (i + 1 + 1) x)).1
  rw [d_apply_eq_pos eq]
  simp

noncomputable def to_ofList {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    koszulCocomplex.ofList R l ⟶ koszulCocomplex.ofList R l' :=
  CochainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => to_self_hom_zero eq
      | i + 1 => to_self_hom_pos eq i)
    (fun i ↦
      match i with
      | 0 => to_self_hom_comm_zero eq
      | i + 1 => to_self_hom_comm_pos eq i)

lemma from_ofList_up_one_comp_to_ofList_eq_zero {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    from_ofList_up_one eq ≫ to_ofList eq = 0 := by
  sorry

noncomputable def shortComplex_of_eq {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    ShortComplex (CochainComplex (ModuleCat R) ℕ) where
  f := from_ofList_up_one eq
  g := to_ofList eq
  zero := from_ofList_up_one_comp_to_ofList_eq_zero eq

lemma shortComplex_of_eq_shortExact {l l' : List R} {a : R} (eq : l = l' ++ [a]) :
    (shortComplex_of_eq eq).ShortExact where
  exact := sorry
  mono_f := sorry
  epi_g := sorry

lemma shortComplex_of_eq_δ_apply {l l' : List R} {a : R} (eq : l = l' ++ [a]) (i : ℕ) :
    (shortComplex_of_eq_shortExact eq).δ i (i + 1) rfl =
      ((-1 : R) ^ i * a) • (ofList_up_one_homology_iso l' i).inv := by
  sorry

end induction

section Htop

theorem exactAt_of_gt_length_of_isRegular (rs : List R) (i : ℕ) (lt : i > rs.length) :
    (koszulCocomplex.ofList R rs).ExactAt i := by
  sorry

/-
Proof route: using the inductivity above, construct the isomorphism using long exact sequence of
homology by induction on length.
It would be better to have a separate isomorphism for the induction step `l = l' ++ [a]`
i.e. isomorphism between `(ofList l).homology l.length` and
`((ofList l').homology l'.length) ⧸ a • (⊤ : Submodule R ((ofList l').homology l'.length))`
-/

noncomputable def topHomologyLinearEquiv (l : List R) :
    (ofList R l).homology l.length ≃ₗ[R] R ⧸ Ideal.ofList l := sorry

end Htop

section regular

open RingTheory.Sequence

/-
Proof route: proof exactness using vanishing of homology, using the inductivity above,
obtain homology `IsZero` from long exact sequence of homology and sequence being regular.
-/

lemma exactAt_of_lt_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i < rs.length) : (koszulCocomplex.ofList R rs).ExactAt i := by
  sorry

theorem exactAt_of_ne_length_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i ≠ rs.length) : (koszulCocomplex.ofList R rs).ExactAt i := by
  sorry

end regular

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
    ofList S l' ≅ ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (ofList R l) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ LinearEquiv.toModuleIso ?_) (fun i j ↦ ?_)
  · sorry
  · sorry

end basechange

end koszulCocomplex
