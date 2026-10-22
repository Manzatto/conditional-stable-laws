import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Counting configurations in factorial moments

These are deterministic counting identities used in the point-process proof. Falling factorials
count injective time selections; disjoint target sets make the selections for different labels
jointly injective.
-/

open Function Finset Classical
open scoped BigOperators

namespace ConditionedStableLaws

noncomputable section

variable {T J : Type*} [Fintype T] [Fintype J]

omit [Fintype T] in
private theorem card_finset_as_set (s : Finset T) :
    Fintype.card (s : Set T) = s.card := Fintype.card_coe s

/-- A falling factorial counts ordered distinct visits to a target. -/
theorem descFactorial_card_eq_sum_injective (s : Finset T) (r : ℕ) :
    s.card.descFactorial r =
      ∑ e : Fin r ↪ T, ∏ i : Fin r, (if e i ∈ s then 1 else 0 : ℕ) := by
  have hc := Fintype.card_congr (Equiv.codRestrict (Fin r) (s : Set T))
  simp only [Fintype.card_embedding_eq, card_finset_as_set, Fintype.card_fin] at hc
  rw [← hc, Fintype.card_subtype]
  simp only [Finset.prod_boole, Finset.mem_univ, forall_const]
  exact (Finset.sum_boole _ _).symm

/-- For pairwise disjoint targets, individual injective selections assemble
into a single injective selection indexed by target label and visit number. -/
def disjointSelectionsEquiv (s : J → Finset T)
    (hs : Pairwise fun i j => Disjoint (s i) (s j)) (r : J → ℕ) :
    (∀ j, Fin (r j) ↪ (s j : Set T)) ≃
      {e : (Σ j, Fin (r j)) ↪ T // ∀ a, e a ∈ s a.1} where
  toFun f := ⟨⟨fun a => (f a.1 a.2).val, by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    by_cases hij : i = j
    · subst j
      have he : a = b := (f i).injective (Subtype.ext hab)
      subst b
      rfl
    · change (f i a).val = (f j b).val at hab
      exact False.elim ((Finset.disjoint_left.mp (hs hij))
        (f i a).property (by rw [hab]; exact (f j b).property))⟩,
      fun a => (f a.1 a.2).property⟩
  invFun e j := ⟨fun a => ⟨e.val ⟨j, a⟩, e.property ⟨j, a⟩⟩, by
    intro a b hab
    have he := e.val.injective (congrArg Subtype.val hab)
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2⟩
  left_inv f := by
    funext j
    ext a
    rfl
  right_inv e := by
    apply Subtype.ext
    ext a
    rfl

/-- The multivariate falling-factorial identity, with every time distinct
across all labels. This is a pointwise identity, prior to expectation. -/
theorem prod_descFactorial_eq_sum_injective (s : J → Finset T)
    (hs : Pairwise fun i j => Disjoint (s i) (s j)) (r : J → ℕ) :
    (∏ j, (s j).card.descFactorial (r j)) =
      ∑ e : (Σ j, Fin (r j)) ↪ T,
        ∏ a : Σ j, Fin (r j), (if e a ∈ s a.1 then 1 else 0 : ℕ) := by
  have hc := Fintype.card_congr (disjointSelectionsEquiv s hs r)
  simp only [Fintype.card_pi, Fintype.card_embedding_eq, card_finset_as_set,
    Fintype.card_fin] at hc
  rw [hc, Fintype.card_subtype]
  simp only [Finset.prod_boole, Finset.mem_univ, forall_const]
  exact (Finset.sum_boole _ _).symm

/-- The finite set of times at which an observation lies in a target. -/
def visitTimes {A : Type*} (x : T → A) (U : Set A) : Finset T :=
  Finset.univ.filter (fun t => x t ∈ U)

omit [Fintype J] in
/-- Disjoint targets induce disjoint sets of visit times. -/
theorem pairwise_disjoint_visitTimes {A : Type*} (x : T → A) (U : J → Set A)
    (hU : Pairwise fun i j => Disjoint (U i) (U j)) :
    Pairwise fun i j => Disjoint (visitTimes x (U i)) (visitTimes x (U j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro t hi hj
  exact Set.disjoint_left.mp (hU hij)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Joint factorials of visit counts equal a sum of products of target indicators over globally
injective time selections. -/
theorem prod_visit_descFactorial_eq {A : Type*} (x : T → A) (U : J → Set A)
    (hU : Pairwise fun i j => Disjoint (U i) (U j)) (r : J → ℕ) :
    (∏ j, (visitTimes x (U j)).card.descFactorial (r j)) =
      ∑ e : (Σ j, Fin (r j)) ↪ T,
        ∏ a : Σ j, Fin (r j), (if x (e a) ∈ U a.1 then 1 else 0 : ℕ) := by
  simpa only [visitTimes, Finset.mem_filter, Finset.mem_univ, true_and] using
    prod_descFactorial_eq_sum_injective
      (fun j => visitTimes x (U j)) (pairwise_disjoint_visitTimes x U hU) r

/-- The real-valued form ready for integration in factorial-moment arguments. -/
theorem prod_visit_descFactorial_eq_real {A : Type*} (x : T → A) (U : J → Set A)
    (hU : Pairwise fun i j => Disjoint (U i) (U j)) (r : J → ℕ) :
    (∏ j, ((visitTimes x (U j)).card.descFactorial (r j) : ℝ)) =
      ∑ e : (Σ j, Fin (r j)) ↪ T,
        ∏ a : Σ j, Fin (r j), (if x (e a) ∈ U a.1 then 1 else 0 : ℝ) := by
  exact_mod_cast prod_visit_descFactorial_eq x U hU r

/-- Two specified coordinates are at most `L` time units apart. -/
def CloseTimes {n r : ℕ} (i j : Fin r) (L : ℕ) (t : Fin r → Fin n) : Prop :=
  (t i).val ≤ (t j).val + L ∧ (t j).val ≤ (t i).val + L

private def closeTimesEncoding {n r : ℕ} (i j : Fin r) (hij : i ≠ j) (L : ℕ) :
    {t : Fin r → Fin n // CloseTimes i j L t} ↪
      Fin (2 * L + 1) × ({k : Fin r // k ≠ j} → Fin n) where
  toFun t := (⟨(t.val j).val + L - (t.val i).val, by
      have h := t.property
      dsimp [CloseTimes] at h
      omega⟩, fun k => t.val k)
  inj' := by
    intro t u h
    apply Subtype.ext
    funext k
    by_cases hkj : k = j
    · subst k
      apply Fin.ext
      have hc := congrArg (fun p => p.1.val) h
      have hi := congrArg (fun p => (p.2 ⟨i, hij⟩).val) h
      have ht := t.property
      have hu := u.property
      dsimp [CloseTimes] at hc hi ht hu
      omega
    · exact congrArg (fun p => p.2 ⟨k, hkj⟩) h

/-- A fixed close pair removes one free time coordinate, costing at most
`2 L + 1` choices. All other coordinates are completely unrestricted. -/
theorem card_closeTimes_le {n r : ℕ} (i j : Fin r) (hij : i ≠ j) (L : ℕ) :
    (Finset.univ.filter (CloseTimes (n := n) i j L)).card ≤
      (2 * L + 1) * n ^ (r - 1) := by
  have h := Fintype.card_le_of_embedding (closeTimesEncoding (n := n) i j hij L)
  have hcard : Fintype.card {k : Fin r // k ≠ j} = r - 1 := by
    simp
  simpa only [Fintype.card_subtype, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fun, hcard] using h

/-- Time configurations with at least one pair separated by at most `L`. -/
def badConfigurations (n r L : ℕ) : Finset (Fin r → Fin n) :=
  Finset.univ.filter (fun t => ∃ i j, i ≠ j ∧ CloseTimes i j L t)

/-- Union bound over pairs of coordinates: the number of configurations
containing a close pair is at most `r² (2 L + 1) n^(r-1)`. -/
theorem card_badConfigurations_le (n r L : ℕ) :
    (badConfigurations n r L).card ≤ r ^ 2 * (2 * L + 1) * n ^ (r - 1) := by
  let psets : (Fin r × Fin r) → Finset (Fin r → Fin n) := fun p =>
    if p.1 = p.2 then ∅ else Finset.univ.filter (CloseTimes p.1 p.2 L)
  have hs : badConfigurations n r L ⊆ Finset.univ.biUnion psets := by
    intro t ht
    obtain ⟨i, j, hij, ht⟩ := (Finset.mem_filter.mp ht).2
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, by simp [psets, hij, ht]⟩
  calc
    (badConfigurations n r L).card ≤ (Finset.univ.biUnion psets).card :=
      Finset.card_le_card hs
    _ ≤ ∑ p, (psets p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin r × Fin r, (2 * L + 1) * n ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.1 = p.2
      · simp [psets, hp]
      · simpa [psets, hp] using card_closeTimes_le (n := n) p.1 p.2 hp L
    _ = r ^ 2 * (2 * L + 1) * n ^ (r - 1) := by
      simp [pow_two, Nat.mul_assoc]

/-- A convenient linear-in-`L` version of the close-pair bound. -/
theorem card_badConfigurations_le_linear (n r L : ℕ) (hL : 0 < L) :
    (badConfigurations n r L).card ≤ 3 * r ^ 2 * L * n ^ (r - 1) := by
  calc
    _ ≤ r ^ 2 * (2 * L + 1) * n ^ (r - 1) := card_badConfigurations_le n r L
    _ ≤ r ^ 2 * (3 * L) * n ^ (r - 1) := by gcongr; omega
    _ = 3 * r ^ 2 * L * n ^ (r - 1) := by ring

/-- Configurations with all distinct coordinates farther than `L` apart. -/
def separatedConfigurations (n r L : ℕ) : Finset (Fin r → Fin n) :=
  Finset.univ \ badConfigurations n r L

/-- The set subtraction definition expresses the usual pairwise separation. -/
theorem mem_separatedConfigurations_iff {n r L : ℕ} (t : Fin r → Fin n) :
    t ∈ separatedConfigurations n r L ↔
      ∀ i j, i ≠ j → ¬ CloseTimes i j L t := by
  simp [separatedConfigurations, badConfigurations]

/-- Every separated time selection is injective, including the case `L = 0`. -/
theorem injective_of_mem_separatedConfigurations {n r L : ℕ} {t : Fin r → Fin n}
    (ht : t ∈ separatedConfigurations n r L) : Function.Injective t := by
  intro i j hij
  by_contra hne
  have hc := (mem_separatedConfigurations_iff t).mp ht i j hne
  apply hc
  simp [CloseTimes, hij]

/-- Separated configurations exhaust all `n^r` configurations up to the
explicit close-pair error. -/
theorem pow_le_card_separated_add_error (n r L : ℕ) :
    n ^ r ≤ (separatedConfigurations n r L).card +
      r ^ 2 * (2 * L + 1) * n ^ (r - 1) := by
  have hc := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (badConfigurations n r L))
  change (separatedConfigurations n r L).card + (badConfigurations n r L).card =
    (Finset.univ : Finset (Fin r → Fin n)).card at hc
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hc
  rw [← hc]
  exact Nat.add_le_add_left (card_badConfigurations_le n r L) _

private def coordinateRestrictionEncoding {n r : ℕ} (i : Fin r) (s : Finset (Fin n)) :
    {t : Fin r → Fin n // t i ∈ s} ↪ s × ({k : Fin r // k ≠ i} → Fin n) where
  toFun t := (⟨t.val i, t.property⟩, fun k => t.val k)
  inj' := by
    intro t u h
    apply Subtype.ext
    funext k
    by_cases hk : k = i
    · subst k
      exact congrArg (fun p => p.1.val) h
    · exact congrArg (fun p => p.2 ⟨k, hk⟩) h

/-- Restricting one time coordinate to `s` removes one free time choice. -/
theorem card_coordinate_mem_le {n r : ℕ} (i : Fin r) (s : Finset (Fin n)) :
    (Finset.univ.filter (fun t : Fin r → Fin n => t i ∈ s)).card ≤ s.card * n ^ (r - 1) := by
  have h := Fintype.card_le_of_embedding (coordinateRestrictionEncoding i s)
  have hc : Fintype.card {k : Fin r // k ≠ i} = r - 1 := by simp
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, hc] at h
  simpa only [Fintype.card_subtype, Fintype.card_fin] using h

/-- The initial and terminal strips removed before applying spectral mixing. -/
def boundaryTimes (n L : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => t.val < L ∨ n < t.val + L)

theorem card_boundaryTimes_le (n L : ℕ) : (boundaryTimes n L).card ≤ 2 * L := by
  have hl : (Finset.univ.filter (fun t : Fin n => t.val < L)).card ≤ L := by
    have h := Fintype.card_le_of_injective
      (fun t : {t : Fin n // t.val < L} => (⟨t.val.val, t.property⟩ : Fin L))
      (by
        intro t u h
        apply Subtype.ext
        apply Fin.ext
        exact congrArg (fun v : Fin L => v.val) h)
    simpa only [Fintype.card_subtype, Fintype.card_fin] using h
  have hr : (Finset.univ.filter (fun t : Fin n => n < t.val + L)).card ≤ L := by
    have h := Fintype.card_le_of_injective
      (fun t : {t : Fin n // n < t.val + L} =>
        (⟨n - 1 - t.val.val, by have h := t.property; have h' := t.val.isLt; omega⟩ : Fin L))
      (by
        intro t u h
        apply Subtype.ext
        apply Fin.ext
        have hh := congrArg Fin.val h
        have ht := t.val.isLt
        have hu := u.val.isLt
        dsimp at hh
        omega)
    simpa only [Fintype.card_subtype, Fintype.card_fin] using h
  rw [boundaryTimes, Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- Configurations that enter either boundary strip in at least one coordinate. -/
def boundaryConfigurations (n r L : ℕ) : Finset (Fin r → Fin n) :=
  Finset.univ.filter (fun t => ∃ i, t i ∈ boundaryTimes n L)

theorem card_boundaryConfigurations_le (n r L : ℕ) :
    (boundaryConfigurations n r L).card ≤ 2 * r * L * n ^ (r - 1) := by
  have hs : boundaryConfigurations n r L ⊆
      Finset.univ.biUnion (fun i : Fin r =>
        Finset.univ.filter (fun t : Fin r → Fin n => t i ∈ boundaryTimes n L)) := by
    intro t ht
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp ht).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ ∑ i : Fin r, (Finset.univ.filter
        (fun t : Fin r → Fin n => t i ∈ boundaryTimes n L)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin r, (2 * L) * n ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (card_coordinate_mem_le i (boundaryTimes n L)).trans
        (Nat.mul_le_mul_right _ (card_boundaryTimes_le n L))
    _ = 2 * r * L * n ^ (r - 1) := by simp; ring

/-- Every configuration excluded from the interior mixing argument: close
pairs together with visits near the initial or terminal time. -/
def excludedConfigurations (n r L : ℕ) : Finset (Fin r → Fin n) :=
  badConfigurations n r L ∪ boundaryConfigurations n r L

/-- Configurations with all gaps and both endpoint gaps at least the cutoff. -/
def interiorSeparatedConfigurations (n r L : ℕ) : Finset (Fin r → Fin n) :=
  Finset.univ \ excludedConfigurations n r L

theorem mem_interiorSeparatedConfigurations_iff {n r L : ℕ} (t : Fin r → Fin n) :
    t ∈ interiorSeparatedConfigurations n r L ↔
      (∀ i j, i ≠ j → ¬ CloseTimes i j L t) ∧
        ∀ i, L ≤ (t i).val ∧ (t i).val + L ≤ n := by
  simp [interiorSeparatedConfigurations, excludedConfigurations, badConfigurations,
    boundaryConfigurations, boundaryTimes, not_or]

/-- An explicit `O(L n^(r-1))` bound including both boundary strips. -/
theorem card_excludedConfigurations_le (n r L : ℕ) :
    (excludedConfigurations n r L).card ≤ (r + 1) ^ 2 * (2 * L + 1) * n ^ (r - 1) := by
  calc
    _ ≤ (badConfigurations n r L).card + (boundaryConfigurations n r L).card :=
      Finset.card_union_le _ _
    _ ≤ r ^ 2 * (2 * L + 1) * n ^ (r - 1) + 2 * r * L * n ^ (r - 1) :=
      Nat.add_le_add (card_badConfigurations_le n r L) (card_boundaryConfigurations_le n r L)
    _ ≤ (r + 1) ^ 2 * (2 * L + 1) * n ^ (r - 1) := by
      rw [← Nat.add_mul]
      apply Nat.mul_le_mul_right
      nlinarith [Nat.zero_le (r * L)]

end

end ConditionedStableLaws
