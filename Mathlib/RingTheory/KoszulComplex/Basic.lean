/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.RingTheory.KoszulComplex.Defs

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

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

section change_generators

variable [IsNoetherianRing R] [IsLocalRing R]

noncomputable def koszulComplex.isoOfMinimalGenerators {I : Ideal R} {l : List R}
    (eq : Ideal.ofList l = I) (min : l.length = I.spanFinrank) :
    koszulComplex.ofList R I.finite_generators_of_isNoetherian.toFinset.toList ≅
    koszulComplex.ofList R l := by
  refine isoOfEquiv R ?_ ?_
  all_goals sorry

end change_generators

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

end IsRegular
