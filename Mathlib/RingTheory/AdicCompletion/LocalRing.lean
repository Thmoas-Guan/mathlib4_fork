/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Basic Properties of Complete Local Ring

In this file we prove that a ring that is adic complete with respect to a maximal ideal
ia a local ring (complete local ring).

-/

public section

variable {R : Type*} [CommRing R] (m : Ideal R) [hmax : m.IsMaximal]

open Ideal Quotient

lemma isUnit_iff_notMem_of_isAdicComplete_maximal [IsAdicComplete m R] (r : R) :
    IsUnit r ↔ r ∉ m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra mem
    rcases IsUnit.exists_left_inv h with ⟨s, hs⟩
    absurd m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax)
    simp [← hs, Ideal.mul_mem_left m s mem]
  · have mapu {n : ℕ} (npos : 0 < n) : IsUnit (Ideal.Quotient.mk (m ^ n) r) := by
      induction n with
      | zero =>
        absurd npos
        exact Nat.not_lt_zero 0
      | succ n ih =>
        by_cases neq0 : n = 0
        · let max' : (m ^ (n + 1)).IsMaximal := by simpa only [neq0, zero_add, pow_one] using hmax
          let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
          simpa [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem.not, neq0] using h
        · apply factorPowSucc.isUnit_of_isUnit_image (Nat.zero_lt_of_ne_zero neq0)
          simpa using (ih (Nat.zero_lt_of_ne_zero neq0))
    choose invSeries' invSeries_spec' using fun (n : {n : ℕ // 0 < n}) ↦
      (IsUnit.exists_left_inv (mapu n.2))
    let invSeries : ℕ → R := fun n ↦ if h : n = 0 then 0 else Classical.choose <|
      Ideal.Quotient.mk_surjective <| invSeries' ⟨n, (Nat.zero_lt_of_ne_zero h)⟩
    have invSeries_spec {n : ℕ} (npos : 0 < n) : (Ideal.Quotient.mk (m ^ n)) (invSeries n) =
      invSeries' ⟨n, npos⟩ := by
      simpa only [Nat.ne_zero_of_lt npos, invSeries]
      using Classical.choose_spec (Ideal.Quotient.mk_surjective (invSeries' ⟨n, npos⟩))
    have mod {a b : ℕ} (le : a ≤ b) :
      invSeries a ≡ invSeries b [SMOD m ^ a • (⊤ : Submodule R R)] := by
      by_cases apos : 0 < a
      · simp only [smul_eq_mul, Ideal.mul_top]
        rw [SModEq.sub_mem, ← eq_zero_iff_mem, map_sub, ← (mapu apos).mul_right_inj,
          mul_zero, mul_sub]
        nth_rw 3 [← factor_mk (pow_le_pow_right le), ← factor_mk (pow_le_pow_right le)]
        simp only [invSeries_spec apos, invSeries_spec (Nat.lt_of_lt_of_le apos le)]
        rw [← map_mul, mul_comm, invSeries_spec', mul_comm, invSeries_spec',
          map_one, sub_self]
      · simp [Nat.eq_zero_of_not_pos apos]
    rcases IsAdicComplete.toIsPrecomplete.prec mod with ⟨inv, hinv⟩
    have eq (n : ℕ) : inv * r - 1 ≡ 0 [SMOD m ^ n • (⊤ : Submodule R R)] := by
      by_cases npos : 0 < n
      · apply SModEq.sub_mem.mpr
        simp only [smul_eq_mul, Ideal.mul_top, sub_zero, ← eq_zero_iff_mem]
        rw [map_sub, map_one, map_mul, ← sub_add_cancel inv (invSeries n), map_add]
        have := SModEq.sub_mem.mp (hinv n).symm
        simp only [smul_eq_mul, Ideal.mul_top] at this
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr this, invSeries_spec npos, invSeries_spec']
      · simp [Nat.eq_zero_of_not_pos npos]
    apply isUnit_iff_exists_inv'.mpr
    use inv
    exact sub_eq_zero.mp <| IsHausdorff.haus IsAdicComplete.toIsHausdorff (inv * r - 1) eq

theorem isLocalRing_of_isAdicComplete_maximal [IsAdicComplete m R] : IsLocalRing R where
  exists_pair_ne := ⟨0, 1, ne_of_mem_of_not_mem m.zero_mem
    (m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax))⟩
  isUnit_or_isUnit_of_add_one {a b} hab := by
    simp only [isUnit_iff_notMem_of_isAdicComplete_maximal m]
    by_contra! h
    absurd m.add_mem h.1 h.2
    simpa [hab] using m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax)

open IsLocalRing

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

lemma AdicCompletion.ker_eval_eq_range (n : ℕ) : (AdicCompletion.eval I M n).ker =
    (AdicCompletion.map I ((I ^ n) • (⊤ : Submodule R M)).subtype).range.restrictScalars R := by
  let InM := (I ^ n) • (⊤ : Submodule R M)
  have comap_eq (m : ℕ) : (I ^ (m + n) • (⊤ : Submodule R M)).comap InM.subtype =
    (I ^ m) • (⊤ : Submodule R InM) := by
    ext x
    simp [Submodule.mem_smul_top_iff, InM, smul_smul, pow_add]
  let shift (m : ℕ) : InM ⧸ ((I ^ m) • (⊤ : Submodule R InM)) →ₗ[R]
    M ⧸ ((I ^ (m + n) • (⊤ : Submodule R M))) :=
    Submodule.mapQ _ _ InM.subtype (le_of_eq (comap_eq m).symm)
  have shift_inj (m : ℕ) : Function.Injective (shift m) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on
    simp only [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
      shift, ← Submodule.mem_comap, comap_eq] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have shift_comm {m l : ℕ} (hle : m ≤ l) :
    (transitionMap I M (add_le_add_left hle n)).comp (shift l) =
    (shift m).comp (transitionMap I InM hle) := by
    ext x
    simp [shift]
  have shift_range (m : ℕ) : (shift m).range = (transitionMap I M (Nat.le_add_left n m)).ker := by
    ext x
    refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun h ↦ ?_⟩
    · rcases Submodule.Quotient.mk_surjective _ y with ⟨z, hz⟩
      simp [← hy, ← hz, LinearMap.mem_ker, shift]
    · rcases Submodule.Quotient.mk_surjective _ x with ⟨y, hy⟩
      simp only [← hy, LinearMap.mem_ker, Submodule.mapQ_apply, LinearMap.id_coe, id_eq,
        Submodule.Quotient.mk_eq_zero] at h
      use Submodule.Quotient.mk ⟨y, h⟩
      simp [shift, hy]
  change _ = ((AdicCompletion.map I InM.subtype).restrictScalars R).range
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have mem (m : ℕ) : x.1 (m + n) ∈ (shift m).range := by
      simpa [shift_range] using hx
    let y_aux (m : ℕ) : InM ⧸ (I ^ m • (⊤ : Submodule R InM)) := Classical.choose (mem m)
    have y_aux_spec (m : ℕ) : (shift m) (y_aux m) = x.1 (m + n) :=
      Classical.choose_spec (mem m)
    refine ⟨⟨y_aux, fun {m n} hle ↦ ?_⟩, ?_⟩
    · apply shift_inj m
      rw [← LinearMap.comp_apply, ← shift_comm hle]
      simp [y_aux_spec]
    · ext m
      simp only [LinearMap.coe_restrictScalars, map_val_apply]
      rw [← x.2 (Nat.le_add_right m n), ← y_aux_spec m]
      rcases Submodule.Quotient.mk_surjective _ (y_aux m) with ⟨z, hz⟩
      simp [← hz, shift]
  · rcases hx with ⟨y, hy⟩
    rcases Submodule.Quotient.mk_surjective _ (y.1 n) with ⟨z, hz⟩
    simp [← hy, ← hz]

lemma LinearMap.lsum_smul_id_range {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → R) (I : Ideal R)
    (eq : Ideal.span (Set.range f) = I) :
    ((LinearMap.lsum R _ R) (fun (i : ι) ↦ (f i) • LinearMap.id)).range =
    I • (⊤ : Submodule R M) := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hx with ⟨y, hy⟩
    simp only [← hy, lsum_apply, coe_sum, coe_comp, coe_proj, Finset.sum_apply, Function.comp_apply,
      Function.eval, smul_apply, id_coe, id_eq]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    simpa [← eq] using mem_span_range_self
  · refine Submodule.smul_induction_on hx (fun r memr m _ ↦ ?_) (fun x y hx hy ↦ add_mem hx hy)
    rw [← eq] at memr
    refine Submodule.span_induction (fun r hr ↦ ?_) (by simp)
      (fun x y memx memy hx hy ↦ by simpa [add_smul] using add_mem hx hy)
      (fun r s mems mem ↦ by simpa [← smul_smul] using Submodule.smul_mem _ r mem) memr
    rcases hr with ⟨i, hi⟩
    use Pi.single i m
    simp [Pi.single_apply, hi]

lemma AdicCompletion.le_ker_eval (n : ℕ) :
    (I ^ n) • (⊤ : Submodule R _) ≤ (AdicCompletion.eval I M n).ker := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r memr m _ ↦ ?_) (fun x y hx hy ↦ add_mem hx hy)
  simpa using Module.isTorsionBySet_quotient_ideal_smul M (I ^ n) (a := ⟨r, memr⟩)

lemma AdicCompletion.ker_eval (fg : I.FG) (n : ℕ) :
    (AdicCompletion.eval I M n).ker = (I ^ n) • (⊤ : Submodule R _) := by
  have fg' : (I ^ n).FG := fg.pow
  classical
  let _ : Fintype (I ^ n).generators := (Submodule.FG.finite_generators fg').fintype
  let g : ((I ^ n).generators → M) →ₗ[R] M :=
    (LinearMap.lsum R _ R) (fun (r : (I ^ n).generators) ↦ r.1 • LinearMap.id)
  have rg : g.range = (I ^ n) • (⊤ : Submodule R M) := by
    apply LinearMap.lsum_smul_id_range
    simpa using (I ^ n).span_generators
  let gr := g.codRestrict ((I ^ n) • (⊤ : Submodule R M)) (by simp [← rg])
  have surjgr : Function.Surjective gr := by
    intro x
    rcases (Submodule.ext_iff.mp rg x.1).mpr x.2 with ⟨y, hy⟩
    exact ⟨y, SetCoe.ext hy⟩
  have req : (AdicCompletion.map I ((I ^ n) • (⊤ : Submodule R M)).subtype).range =
    ((AdicCompletion.map I g).comp (piEquivOfFintype I _).symm.toLinearMap).range := by
    have : ((I ^ n) • (⊤ : Submodule R M)).subtype.comp gr = g := g.subtype_comp_codRestrict _ _
    rw [LinearEquiv.range_comp, ← this, ← map_comp, LinearMap.range_comp, LinearMap.range_eq_map,
      LinearMap.range_eq_top_of_surjective _ (AdicCompletion.map_surjective I surjgr)]
  have compeq : ((AdicCompletion.map I g).comp
    (piEquivOfFintype I _).symm.toLinearMap).restrictScalars R =
    (LinearMap.lsum R _ R) (fun (r : (I ^ n).generators) ↦ r.1 • LinearMap.id) := by
    ext r x n
    have : (r.1 • (mk I M) x).1 n = r.1 • ((mk I M) x).1 n:= rfl
    simp [piEquivOfFintype, Pi.single_apply, g, this]
  rw [AdicCompletion.ker_eval_eq_range, req, ← LinearMap.range_restrictScalars, compeq]
  apply LinearMap.lsum_smul_id_range
  simpa using (I ^ n).span_generators

lemma AdicCompletion.isAdicComplete (fg : I.FG) : IsAdicComplete I (AdicCompletion I M) where
  haus' x hx := by
    ext n
    simpa using (AdicCompletion.le_ker_eval I M n) ((Submodule.Quotient.mk_eq_zero _).mp (hx n))
  prec' f hf := by
    refine ⟨⟨fun n ↦ (f n).1 n, fun {m l} hle ↦ ?_⟩, fun n ↦ ?_⟩
    · have := (AdicCompletion.le_ker_eval I M m) (SModEq.sub_mem.mp (hf hle))
      simp only [LinearMap.mem_ker, coe_eval, val_sub, Pi.sub_apply, sub_eq_zero] at this
      simp [this]
    · simp [SModEq.sub_mem, ← AdicCompletion.ker_eval I M fg]

lemma AdicCompletion.isAdicComplete_self (fg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) := by
  sorry

lemma AdicCompletion.isMaximal_map [IsNoetherianRing R] [IsLocalRing R] (ne : I ≠ ⊤) :
    ((maximalIdeal R).map (algebraMap R (AdicCompletion I R))).IsMaximal := by
  sorry

instance [IsNoetherianRing R] [IsLocalRing R] :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) := by
  sorry

lemma AdicCompletion.maximalIdeal_eq_map [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  sorry

instance [IsNoetherianRing R] [IsLocalRing R] : IsAdicComplete
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) (AdicCompletion (maximalIdeal R) R) := by
  sorry

lemma AdicCompletion.spanFinrank_maximalIdeal_eq [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  -- use cotangent space iso
  sorry
