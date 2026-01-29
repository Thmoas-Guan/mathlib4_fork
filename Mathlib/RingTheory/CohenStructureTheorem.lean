/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Basic

/-!

# Cohen Structure Theorem

-/

@[expose] public section

open IsLocalRing

universe u

variable (R : Type u) [CommRing R]

variable [IsNoetherianRing R] [IsLocalRing R]

lemma exist_isRegularLocalRing_surjective_of_isAdicComplete [IsAdicComplete (maximalIdeal R) R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (f : S →+* R),
    Function.Surjective f := by
  sorry

lemma spanFinrank_eq_of_surjective_of_ker_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (f : R →+* R') (surj : Function.Surjective f) (le : RingHom.ker f ≤ (maximalIdeal R) ^ 2) :
    (maximalIdeal R').spanFinrank = (maximalIdeal R).spanFinrank := by
  classical
  apply le_antisymm (spanFinrank_le_of_surjective f surj)
  let fin := Submodule.FG.finite_generators (maximalIdeal R').fg_of_isNoetherianRing
  let _ := fin.fintype
  rcases surj.list_map (maximalIdeal R').generators.toFinset.toList with ⟨l, hl⟩
  apply le_of_le_of_eq _ (Submodule.FG.generators_ncard (maximalIdeal R').fg_of_isNoetherianRing)
  have leneq : l.length = (maximalIdeal R').generators.ncard := by
    rw [← List.length_map (as := l) f, hl, Set.ncard_eq_toFinset_card', Finset.length_toList]
  rw [← leneq]
  have := ((local_hom_TFAE f).out 0 4).mp (surj.isLocalHom f)
  have mapeq : (maximalIdeal R).map f = maximalIdeal R' := by
    simpa [this] using Ideal.map_comap_of_surjective f surj (maximalIdeal R')
  have hspan : Ideal.span (maximalIdeal R').generators = _ := (maximalIdeal R').span_generators
  have supeq : Ideal.ofList l ⊔ RingHom.ker f = maximalIdeal R := by
    simp [← Ideal.comap_map_of_surjective' f surj, Ideal.map_ofList, hl, Ideal.ofList, hspan, this]
  have : Ideal.ofList l = maximalIdeal R :=
    le_antisymm (by simp [← supeq]) (Submodule.le_of_le_smul_of_le_jacobson_bot
      (maximalIdeal R).fg_of_isNoetherianRing (maximalIdeal_le_jacobson ⊥)
      (le_of_eq_of_le supeq.symm (sup_le_sup_left (by simpa [← pow_two]) _)))
  have spaneq : Submodule.span R (l.toFinset : Set R) = maximalIdeal R := by simp [← this]
  rw [← spaneq]
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _))
  exact le_of_eq_of_le (Set.ncard_coe_finset _) (List.toFinset_card_le l)

lemma exist_isRegularLocalRing_surjective_ker_le_of_isAdicComplete
    [IsAdicComplete (maximalIdeal R) R] : ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* R), Function.Surjective f ∧ RingHom.ker f ≤ (maximalIdeal S) ^ 2 := by
  rcases exist_isRegularLocalRing_surjective_of_isAdicComplete R with ⟨S, _, regS, f, surj⟩
  obtain ⟨n, hn⟩ : ∃ n, (maximalIdeal R).spanFinrank + n = (maximalIdeal S).spanFinrank :=
    Nat.le.dest (spanFinrank_le_of_surjective f surj)
  induction n generalizing S f with
  | zero =>
    use S, inferInstance, inferInstance, f, surj
    intro x hx
    by_contra nmem
    have le : RingHom.ker f ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
    obtain ⟨reg, dim⟩ := quotient_span_singleton S (le hx) nmem
    have : ∀ y ∈ Ideal.span {x}, f y = 0 := by
      intro y hy
      rcases Ideal.mem_span_singleton.mp hy with ⟨z, hz⟩
      simp [hz, RingHom.mem_ker.mp hx]
    have surj' := Ideal.Quotient.lift_surjective_of_surjective _ this surj
    rw [← (isRegularLocalRing_def _).mp reg, ← (isRegularLocalRing_def _).mp regS,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj] at dim
    absurd spanFinrank_le_of_surjective _ surj'
    omega
  | succ n ih =>
    obtain ⟨x, hx, nmem⟩ : ∃ x ∈ RingHom.ker f, x ∉ (maximalIdeal S) ^ 2 := by
      by_contra! mem
      simp [spanFinrank_eq_of_surjective_of_ker_le f surj mem] at hn
    have le : RingHom.ker f ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
    obtain ⟨reg, dim⟩ := quotient_span_singleton S (le hx) nmem
    have : ∀ y ∈ Ideal.span {x}, f y = 0 := by
      intro y hy
      rcases Ideal.mem_span_singleton.mp hy with ⟨z, hz⟩
      simp [hz, RingHom.mem_ker.mp hx]
    have surj' := Ideal.Quotient.lift_surjective_of_surjective _ this surj
    rw [← (isRegularLocalRing_def _).mp reg, ← (isRegularLocalRing_def _).mp regS,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj] at dim
    simp only [← add_assoc, ← dim, Nat.add_right_cancel_iff] at hn
    exact ih (S ⧸ Ideal.span {x}) inferInstance reg _ surj' hn

lemma exist_isRegularLocalRing_surjective_adicCompletion :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* (AdicCompletion (maximalIdeal R) R)), Function.Surjective f :=
  exist_isRegularLocalRing_surjective_of_isAdicComplete _

lemma exist_isRegularLocalRing_surjective_adicCompletion_ker_le :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
    (f : S →+* (AdicCompletion (maximalIdeal R) R)),
    Function.Surjective f ∧ RingHom.ker f ≤ (maximalIdeal S) ^ 2 :=
  exist_isRegularLocalRing_surjective_ker_le_of_isAdicComplete _
