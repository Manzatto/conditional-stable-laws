import ConditionedStableLaws.ClusterEncoding
import ConditionedStableLaws.FactorialMoments
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm

/-!
# Sorting injective factorial-moment configurations

An injective time selection determines its increasing time tuple and the
permutation of observation labels. The injection yields the factorial
multiplicity bound, and close pairs imply a short adjacent gap after sorting.
-/

open Finset Classical
open scoped BigOperators
noncomputable section

namespace ConditionedStableLaws.SortedConfigurations

/-- Increasing time tuples in the observation window. -/
def Ordered (n k : ℕ) := {t : Fin k → Fin n // StrictMono t}

instance (n k : ℕ) : Fintype (Ordered n k) :=
  inferInstanceAs (Fintype {_t : Fin k → Fin n // _})

/-- The finite set of selected observation times. -/
def timeSet {n k : ℕ} (e : Fin k ↪ Fin n) : Finset (Fin n) := univ.map e

@[simp] theorem card_timeSet {n k : ℕ} (e : Fin k ↪ Fin n) : (timeSet e).card = k := by
  simp [timeSet]

/-- The strictly increasing enumeration of the selected times. -/
def sorted {n k : ℕ} (e : Fin k ↪ Fin n) : Ordered n k :=
  ⟨(timeSet e).orderEmbOfFin (card_timeSet e),
    ((timeSet e).orderEmbOfFin (card_timeSet e)).strictMono⟩

private def rangeEquiv {n k : ℕ} (e : Fin k ↪ Fin n) : Fin k ≃ timeSet e :=
  Equiv.ofBijective (fun i => ⟨e i, mem_map.mpr ⟨i, mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => e.injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨i, _, hi⟩ := mem_map.mp hx
      exact ⟨i, Subtype.ext hi⟩⟩

/-- The rank permutation takes an original label to its sorted position. -/
def rank {n k : ℕ} (e : Fin k ↪ Fin n) : Equiv.Perm (Fin k) :=
  (rangeEquiv e).trans ((timeSet e).orderIsoOfFin (card_timeSet e)).symm.toEquiv

/-- Reconstruction preserves the times and their original labels. -/
theorem sorted_rank {n k : ℕ} (e : Fin k ↪ Fin n) (i : Fin k) :
    (sorted e).val (rank e i) = e i := by
  change (((timeSet e).orderIsoOfFin (card_timeSet e))
    (((timeSet e).orderIsoOfFin (card_timeSet e)).symm (rangeEquiv e i))).val = e i
  simp only [OrderIso.apply_symm_apply]
  rfl

/-- Sorting and label permutation encode an injective tuple without loss. -/
def encoding {n k : ℕ} : (Fin k ↪ Fin n) ↪ (Ordered n k × Equiv.Perm (Fin k)) where
  toFun e := (sorted e, rank e)
  inj' := by
    intro e f h
    have ht := congrArg Prod.fst h
    have hr := congrArg Prod.snd h
    ext i
    rw [← sorted_rank e i, ← sorted_rank f i]
    rw [show sorted e = sorted f from ht, show rank e = rank f from hr]

/-- A close pair in an increasing tuple forces a short adjacent gap. -/
theorem exists_short_adjacent {n q r : ℕ} (t : Ordered n (r + 1))
    (h : ∃ i j, i ≠ j ∧ CloseTimes i j q t.val) :
    ∃ i : Fin r, (t.val i.succ).val ≤ (t.val i.castSucc).val + q := by
  obtain ⟨a, b, hab, hclose⟩ := h
  have hpair : ∃ a b : Fin (r + 1), a < b ∧ CloseTimes a b q t.val := by
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact ⟨a, b, hlt, hclose⟩
    · exact ⟨b, a, hlt, hclose.symm⟩
  obtain ⟨i, j, hij, hclose⟩ := hpair
  let a : Fin r := ⟨i.val, by have := j.isLt; exact Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
  have hcast : a.castSucc = i := Fin.ext rfl
  have hsucc : a.succ ≤ j := by change i.val + 1 ≤ j.val; omega
  have hmono : (t.val a.succ).val ≤ (t.val j).val := t.property.monotone hsucc
  exact ⟨a, hmono.trans (by simpa [hcast] using hclose.2)⟩

/-- Injective configurations with a close pair. -/
def Bad (n q r : ℕ) :=
  {e : Fin (r + 1) ↪ Fin n // ∃ i j, i ≠ j ∧ CloseTimes i j q e}

instance (n q r : ℕ) : Fintype (Bad n q r) :=
  inferInstanceAs (Fintype {_e : Fin (r + 1) ↪ Fin n // _})

/-- The sorted version of every close injective configuration is an ordered close configuration. -/
def sortedBad {n q r : ℕ} (e : Bad n q r) : ClusterEncoding.BadConfiguration n q r :=
  ⟨(sorted e.val).val, (sorted e.val).property,
    exists_short_adjacent (sorted e.val) (by
      obtain ⟨i, j, hij, hc⟩ := e.property
      refine ⟨rank e.val i, rank e.val j, (rank e.val).injective.ne hij, ?_⟩
      simpa only [CloseTimes, sorted_rank] using hc)⟩

/-- The finite permutation is the only additional coordinate after sorting. -/
def badEncoding {n q r : ℕ} : Bad n q r ↪
    (ClusterEncoding.BadConfiguration n q r × Equiv.Perm (Fin (r + 1))) where
  toFun e := (sortedBad e, rank e.val)
  inj' := by
    intro e f h
    apply Subtype.ext
    apply encoding.injective
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : ClusterEncoding.BadConfiguration n q r ×
        Equiv.Perm (Fin (r + 1)) => z.1.val) h
    · change rank e.val = rank f.val
      exact congrArg Prod.snd h

/-- The factorial multiplicity bound for arbitrary nonnegative sorted weights. -/
theorem sum_bad_le_factorial_mul (n q r : ℕ)
    (W : ClusterEncoding.BadConfiguration n q r → ℝ) (hW : ∀ t, 0 ≤ W t)
    (w : Bad n q r → ℝ) (hw : ∀ e, w e ≤ W (sortedBad e)) :
    (∑ e, w e) ≤ ((r + 1).factorial : ℝ) * ∑ t, W t := by
  classical
  let f : (ClusterEncoding.BadConfiguration n q r × Equiv.Perm (Fin (r + 1))) → ℝ :=
    fun z => W z.1
  calc
    (∑ e, w e) ≤ ∑ e, f (badEncoding e) := sum_le_sum (fun e _ => hw e)
    _ = ∑ z ∈ univ.image badEncoding, f z :=
      (sum_image (fun _ _ _ _ h => badEncoding.injective h)).symm
    _ ≤ ∑ z, f z := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun z _ _ => hW z.1)
    _ = ((r + 1).factorial : ℝ) * ∑ t, W t := by
      simp [f, Fintype.sum_prod_type, Fintype.card_perm, ← mul_sum]

/-- The exact connection with the function-indexed bad-configuration sum
used in factorial moments: repeated times have weight zero. -/
theorem sum_finset_bad_eq (n q r : ℕ) (w : (Fin (r + 1) → Fin n) → ℝ)
    (hzero : ∀ t, ¬Function.Injective t → w t = 0) :
    (∑ t ∈ badConfigurations n (r + 1) q, w t) = ∑ e : Bad n q r, w e.val := by
  classical
  calc
    (∑ t ∈ badConfigurations n (r + 1) q, w t) =
        ∑ t, if t ∈ badConfigurations n (r + 1) q then w t else 0 := by
      rw [← sum_filter]
      simp
    _ = ∑ t, if Function.Injective t then
        (if t ∈ badConfigurations n (r + 1) q then w t else 0) else 0 := by
      apply sum_congr rfl
      intro t ht
      by_cases hi : Function.Injective t
      · simp [hi]
      · simp [hi, hzero t hi]
    _ = ∑ e : Fin (r + 1) ↪ Fin n,
        if (e : Fin (r + 1) → Fin n) ∈ badConfigurations n (r + 1) q then w e else 0 := by
      rw [← sum_filter, sum_subtype (p := Function.Injective) _ (by simp)]
      exact (Equiv.subtypeInjectiveEquivEmbedding (Fin (r + 1)) (Fin n)).sum_comp
        (fun e : Fin (r + 1) ↪ Fin n =>
          if (e : Fin (r + 1) → Fin n) ∈ badConfigurations n (r + 1) q then w e else 0)
    _ = ∑ e : Bad n q r, w e.val := by
      simp only [badConfigurations, mem_filter, mem_univ, true_and]
      rw [← sum_filter, sum_subtype
        (p := fun e : Fin (r + 1) ↪ Fin n => ∃ i j, i ≠ j ∧ CloseTimes i j q e) _ (by simp)]
      rfl

/-- The sorting bound applies to the factorial weights. -/
theorem sum_finset_bad_le_factorial_mul (n q r : ℕ)
    (W : ClusterEncoding.BadConfiguration n q r → ℝ) (hW : ∀ t, 0 ≤ W t)
    (w : (Fin (r + 1) → Fin n) → ℝ)
    (hzero : ∀ t, ¬Function.Injective t → w t = 0)
    (hw : ∀ e : Bad n q r, w e.val ≤ W (sortedBad e)) :
    (∑ t ∈ badConfigurations n (r + 1) q, w t) ≤
      ((r + 1).factorial : ℝ) * ∑ t, W t := by
  rw [sum_finset_bad_eq n q r w hzero]
  exact sum_bad_le_factorial_mul n q r W hW (fun e => w e.val) hw

/-- A uniform additive mixing error costs at most the number of all time
configurations. This keeps that error separate from the rare-target factors. -/
theorem sum_finset_bad_le_factorial_mul_add (n q r : ℕ)
    (W : ClusterEncoding.BadConfiguration n q r → ℝ) (hW : ∀ t, 0 ≤ W t)
    (w : (Fin (r + 1) → Fin n) → ℝ)
    (hzero : ∀ t, ¬Function.Injective t → w t = 0)
    (err : ℝ) (herr : 0 ≤ err)
    (hw : ∀ e : Bad n q r, w e.val ≤ W (sortedBad e) + err) :
    (∑ t ∈ badConfigurations n (r + 1) q, w t) ≤
      ((r + 1).factorial : ℝ) * ∑ t, W t + (n : ℝ) ^ (r + 1) * err := by
  classical
  have hc : Fintype.card (Bad n q r) ≤ n ^ (r + 1) := by
    have hi : Function.Injective (fun e : Bad n q r => (e.val : Fin (r + 1) → Fin n)) := by
      intro e f h
      apply Subtype.ext
      exact Function.Embedding.ext (fun i => congrFun h i)
    simpa using Fintype.card_le_of_injective _ hi
  rw [sum_finset_bad_eq n q r w hzero]
  calc
    (∑ e : Bad n q r, w e.val) ≤ ∑ e : Bad n q r, (W (sortedBad e) + err) :=
      sum_le_sum (fun e _ => hw e)
    _ = (∑ e : Bad n q r, W (sortedBad e)) + (Fintype.card (Bad n q r) : ℝ) * err := by
      simp [sum_add_distrib]
    _ ≤ ((r + 1).factorial : ℝ) * ∑ t, W t + (n : ℝ) ^ (r + 1) * err := by
      apply add_le_add
      · exact sum_bad_le_factorial_mul n q r W hW _ (fun _ => le_rfl)
      · apply mul_le_mul_of_nonneg_right _ herr
        exact_mod_cast hc

end ConditionedStableLaws.SortedConfigurations
