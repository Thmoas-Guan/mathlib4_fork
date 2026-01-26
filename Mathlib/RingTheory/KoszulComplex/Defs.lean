/-
Copyright (c) 2026 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
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
public import Mathlib.Data.Fin.Tuple.Sort

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

namespace exteriorPower

variable {ι : Type*} [LinearOrder ι]

/-- Given a linearly ordered basis `b : Module.Basis ι R M`, the `n`th exterior power `⋀[R]^n M`
has a basis indexed by order embeddings `Fin n ↪o ι`. -/
noncomputable def basis (b : Module.Basis ι R M) (n : ℕ) :
    Module.Basis (Fin n ↪o ι) R (⋀[R]^n M) := by
  let e : (Fin n ↪o ι) → ⋀[R]^n M := fun a ↦ ιMulti R n (fun i ↦ b (a i))
  let S : Submodule R (⋀[R]^n M) := Submodule.span R (Set.range e)
  have h₁ : ∀ i : ι, b.coord i (b i) = (1 : R) := by
    intro i
    simp [Module.Basis.coord]
  have h₀ : ∀ ⦃i j : ι⦄, i ≠ j → b.coord i (b j) = (0 : R) := by
    intro i j hij
    simp [Module.Basis.coord, hij]
  have mem_S_of_injective (v : Fin n → ι) (hv : Function.Injective v) :
      ιMulti R n (fun i ↦ b (v i)) ∈ S := by
    let σ : Equiv.Perm (Fin n) := Tuple.sort v
    have hmono : Monotone (v ∘ σ) := Tuple.monotone_sort v
    have hinj : Function.Injective (v ∘ σ) := hv.comp σ.injective
    let a : Fin n ↪o ι := OrderEmbedding.ofStrictMono (v ∘ σ) (hmono.strictMono_of_injective hinj)
    have hperm :
        ιMulti R n (fun i ↦ b (v i)) = Equiv.Perm.sign σ • ιMulti R n (fun i ↦ b (a i)) := by
      have hperm' :
          ιMulti R n (fun i ↦ b (a ((Equiv.symm σ) i))) =
            Equiv.Perm.sign σ • ιMulti R n (fun i ↦ b (a i)) := by
        simpa using
          (AlternatingMap.map_perm (g := ιMulti R n) (v := fun i ↦ b (a i))
            (σ := (σ⁻¹ : Equiv.Perm (Fin n))))
      have hcomp : (fun i ↦ b (a ((Equiv.symm σ) i))) = fun i ↦ b (v i) := by
        ext i
        simp [a, Function.comp]
      simpa [hcomp] using hperm'
    rw [hperm]
    refine S.smul_mem _ (Submodule.subset_span ?_)
    exact ⟨a, rfl⟩
  have hli : LinearIndependent R e := by
    refine (linearIndependent_iff).2 ?_
    intro l hl
    ext a0
    let φ : ⋀[R]^n M →ₗ[R] R := pairingDual R M n (ιMulti R n (fun i ↦ b.coord (a0 i)))
    have hx : φ ((Finsupp.linearCombination R e) l) = 0 := by
      simpa using congrArg (fun x ↦ φ x) hl
    have hx' : φ ((Finsupp.linearCombination R e) l) = l a0 := by
      simp only [Finsupp.linearCombination_apply]
      simp_rw [map_finsuppSum, map_smul]
      refine (Finsupp.sum_eq_single a0 ?_ ?_).trans ?_
      · intro a ha hne
        have : φ (e a) = (0 : R) := by
          dsimp [φ, e]
          exact
            pairingDual_apply_apply_eq_one_zero (R := R) (M := M) (ι := ι) (x := b)
              (f := fun i ↦ b.coord i) (n := n) (h₀ := by
                intro i j hij; exact h₀ hij) a0 a hne.symm
        simp [this]
      · intro ha0
        simp
      · have : φ (e a0) = 1 := by
          dsimp [φ, e]
          exact
            pairingDual_apply_apply_eq_one (R := R) (M := M) (ι := ι) (x := b)
              (f := fun i ↦ b.coord i) h₁ (by
                intro i j hij; exact h₀ hij) n a0
        simp [this, smul_eq_mul]
    exact by simpa [hx', Finsupp.zero_apply] using hx
  have hsp : (⊤ : Submodule R (⋀[R]^n M)) ≤ S := by
    let π : ⋀[R]^n M →ₗ[R] (⋀[R]^n M ⧸ S) := S.mkQ
    let ψ : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M ⧸ S) := π.compAlternatingMap (ιMulti R n)
    have hψ : ψ = 0 := by
      refine (Module.Basis.ext_alternating (ι := Fin n) (e := b) (f := ψ) (g := 0) ?_)
      intro v hv
      have hvmem : ιMulti R n (fun i ↦ b (v i)) ∈ S :=
        mem_S_of_injective v hv
      have : π (ιMulti R n (fun i ↦ b (v i))) = 0 := by
        simpa [π, Submodule.mkQ_apply] using (Submodule.Quotient.mk_eq_zero S).2 hvmem
      simpa [ψ, Function.comp] using this
    have hrange : Set.range (ιMulti R n (M := M)) ⊆ S := by
      rintro _ ⟨m, rfl⟩
      have : ψ m = 0 := by
        simp [hψ]
      have : π (ιMulti R n m) = 0 := by
        simpa [ψ] using this
      have : Submodule.Quotient.mk (p := S) (ιMulti R n m) = 0 := by
        simpa [π, Submodule.mkQ_apply] using this
      exact (Submodule.Quotient.mk_eq_zero S).1 this
    have hspanle : Submodule.span R (Set.range (ιMulti R n (M := M))) ≤ S :=
      Submodule.span_le.2 hrange
    simpa [S, ιMulti_span (R := R) (n := n) (M := M)] using hspanle
  exact Module.Basis.mk hli (by simpa [S] using hsp)

end exteriorPower

instance Module.Free.exteriorPower (n : ℕ) [Module.Free R M] : Module.Free R (⋀[R]^n M) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R M
  letI : LinearOrder ι := linearOrderOfSTO (WellOrderingRel (α := ι))
  exact
    Module.Free.of_basis
      (exteriorPower.basis (R := R) (M := M) (ι := ι) (Module.Free.chooseBasis R M) n)

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

section homologyannihilator

lemma koszulComplex.mem_annihilator_homology (M : Type u) [AddCommGroup M] [Module R M] (x : M)
    (φ : M →ₗ[R] R) (i : ℕ) : φ x ∈ Module.annihilator R ((koszulComplex R x).homology i) := by
  sorry

end homologyannihilator

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
    (x : M) (i : ℕ) : Module.Free R ((koszulComplex R x).X i) :=
  inferInstanceAs <| Module.Free R (⋀[R]^i M)

end IsRegular
