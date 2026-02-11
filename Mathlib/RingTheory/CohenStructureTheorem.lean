/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!

# Cohen Structure Theorem

-/

@[expose] public section

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R]

section

lemma exists_isLocalHom_flat [IsLocalRing R] (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
    (_ : IsLocalHom (algebraMap R R')), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[ResidueField R] (ResidueField R')) := by
  sorry

end

section IsCohenRing

class IsCohenRing [IsDomain R] extends IsDiscreteValuationRing R where
  complete : IsAdicComplete (maximalIdeal R) R
  span : maximalIdeal R = Ideal.span {(ringChar (ResidueField R) : R)}

lemma exists_isCohenRing_of_not_charZero (k : Type u) [Field k] (charpos : ¬ CharZero k) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsCohenRing R),
      Nonempty (ResidueField R ≃+* k) := by
  have char := CharP.exists' k
  simp only [charpos, false_or] at char
  rcases char with ⟨p, _, char⟩
  let _ := ZMod.algebra k p
  let _ : Algebra (ResidueField (PadicInt p)) k := sorry
  rcases exists_isLocalHom_flat (PadicInt p) k with ⟨R, _, _, _, _, flat, maxeq, ⟨iso⟩⟩
  use AdicCompletion (maximalIdeal R) R, inferInstance

  sorry

def RingHom.mapQuotientNat {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    R ⧸ Ideal.span {(n : R)} →+* S ⧸ Ideal.span {(n : S)} :=
  Ideal.Quotient.lift (Ideal.span {(n : R)})
    ((Ideal.Quotient.mk (Ideal.span {(n : S)})).comp f) (fun x mem ↦ by
      rcases  Ideal.mem_span_singleton.mp mem with ⟨y, hy⟩
      simpa [Ideal.Quotient.eq_zero_iff_dvd] using ⟨f y, by simp [hy]⟩)

lemma quotient_power_char_formallySmooth [IsDomain R] [IsCohenRing R] (p : ℕ) (prime : Nat.Prime p)
    (char : CharP (ResidueField R) p) (n : ℕ) (ne0 : n ≠ 0) :
    (RingHom.mapQuotientNat (Int.castRingHom R) (p ^ n)).FormallySmooth := by
  induction n with
  | zero => simp at ne0
  | succ n ih =>
    by_cases eq0 : n = 0
    · rw [eq0, zero_add, pow_one]
      sorry
    · have ih' := ih eq0

      sorry

end IsCohenRing

section

variable {R} [IsLocalRing R]

class IsCoefficientRing {S : Type*} [CommRing S] (f : S →+* R) extends
    IsLocalRing S, IsLocalHom f where
  inj : Function.Injective f
  complete : IsAdicComplete (maximalIdeal S) S
  residue_iso : Function.Bijective (IsLocalRing.ResidueField.map f)
  span : maximalIdeal S = Ideal.span {(ringChar (ResidueField S) : S)}

lemma exists_section_of_charZero [IsAdicComplete (maximalIdeal R) R]
    (char : CharZero (ResidueField R)) :
    ∃ (f : ResidueField R →+* R), (IsLocalRing.residue R).comp f = RingHom.id _ := by
  let _ : Algebra ℚ (ResidueField R) := DivisionRing.toRatAlgebra
  let _ : Algebra.FormallySmooth ℚ (ResidueField R) := sorry
  have exists_lift (n : ℕ) (f : ResidueField R →+* (R ⧸ (maximalIdeal R) ^ n)) :
    ∃ g : ResidueField R →+* (R ⧸ (maximalIdeal R) ^ (n + 1)),
      (Ideal.Quotient.factorPowSucc _ n).comp g = f := by
    sorry
  let f_series (n : ℕ) : (ResidueField R →+* (R ⧸ (maximalIdeal R) ^ n)) := by
    induction n with
    | zero =>
      exact Ideal.Quotient.factor (by simp)
    | succ n ih =>
      induction n with
      | zero =>
        exact Ideal.Quotient.factor (by simp)
      | succ n ih =>
        exact Classical.choose (exists_lift (n + 1) ih)
  have f_series1 : f_series 1 = Ideal.Quotient.factor (le_of_eq (pow_one _).symm) := rfl
  have f_series_spec {n m : ℕ} (h : m = n + 1) : (Ideal.Quotient.factorPow _
    (Nat.le.intro h.symm)).comp (f_series m) = f_series n := by
    subst h
    match n with
    | 0 => exact Ideal.Quotient.factor_comp _ _
    | n + 1 => exact Classical.choose_spec (exists_lift (n + 1) _)
  have f_series_spec'' {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (f_series n) = f_series m := by
    obtain ⟨l, hl⟩ := Nat.le.dest hle
    subst hl
    induction l with
    | zero => simp
    | succ l ih =>
      have : m + (l + 1) = (m + l) + 1 := add_assoc m l 1
      rw [← ih (Nat.le_add_right m l), ← f_series_spec this, ← RingHom.comp_assoc,
        Ideal.Quotient.factor_comp]
  let f' := AdicCompletion.liftRingHom (maximalIdeal R) f_series f_series_spec''
  use (AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm.toRingHom.comp f'
  have (x : R) : (residue R) x = (Ideal.Quotient.factor (by simp))
    ((Ideal.Quotient.mk ((maximalIdeal R) ^ 1)) x) := rfl
  ext x
  rw [RingHom.comp_apply, this, RingHom.comp_apply]
  change (Ideal.Quotient.factor (le_of_eq (pow_one _))) ((Ideal.Quotient.mk (maximalIdeal R ^ 1))
    ((AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm (f' x))) = _
  --wierd coercion problem
  rw [AdicCompletion.mk_ofAlgEquiv_symm, AdicCompletion.evalₐ_liftRingHom, f_series1,
    ← RingHom.comp_apply, Ideal.Quotient.factor_comp, Ideal.Quotient.factor_eq]
  rfl

lemma isCoefficientRing_of_residueField (char : CharZero (ResidueField R))
    (f : ResidueField R →+* R) (h : (IsLocalRing.residue R).comp f = RingHom.id _) :
    IsCoefficientRing f where
  inj := f.injective
  complete := by
    rw [maximalIdeal_eq_bot]
    exact IsAdicComplete.bot (ResidueField R)
  residue_iso := ⟨RingHom.injective _, fun x ↦ ⟨IsLocalRing.residue _ x, by
    simpa [IsLocalRing.ResidueField.map_residue] using RingHom.congr_fun h x⟩⟩
  span := by
    have : ringChar (ResidueField (ResidueField R)) = 0 := by
      rw [← Algebra.ringChar_eq (ResidueField R)]
      exact (CharP.ringChar_zero_iff_CharZero (ResidueField R)).mpr char
    simpa [this] using maximalIdeal_eq_bot

lemma exists_isCoeffientRing_isCohenRing [IsAdicComplete (maximalIdeal R) R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsCohenRing S) (f : S →+* R),
    IsCoefficientRing f := by
  sorry

lemma exists_mvPowerSeries_surjective_of_isCoeffientRing [IsAdicComplete (maximalIdeal R) R]
    (fg : (maximalIdeal R).FG) (S : Type u) [CommRing S] (f : S →+* R) [IsCoefficientRing f] :
    ∃ (n : ℕ) (g : MvPowerSeries (Fin n) S →+* R),
    Function.Surjective g ∧ g.comp MvPowerSeries.C = f := by
  sorry

end

section corollary

variable [IsLocalRing R] [IsNoetherianRing R]

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

end corollary
