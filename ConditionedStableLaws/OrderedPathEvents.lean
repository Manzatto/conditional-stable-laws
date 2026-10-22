import ConditionedStableLaws.PositiveConditioning
import ConditionedStableLaws.SortedConfigurations

/-!
# Ordered tuples as path events

Absolute observation times are converted to consecutive gaps. The resulting path event is proved
equal to simultaneous membership at the original times; its elapsed time is the last observation
time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace ConditionedStableLaws.OrderedPathEvents
open PathMixing

/-- Convert absolute times to gaps from a specified preceding time. -/
def gapWord {A : Type*} : ℕ → List (ℕ × A) → List (ℕ × A)
  | _, [] => []
  | prev, (n, a) :: w => (n - prev, a) :: gapWord n w

/-- The explicit adjacent-gap form for a nonempty finite tuple. -/
theorem gapWord_ofFn {A : Type*} (r prev : ℕ) (t : Fin (r + 1) → ℕ) (a : Fin (r + 1) → A) :
    gapWord prev (List.ofFn (fun i => (t i, a i))) =
      (t 0 - prev, a 0) :: List.ofFn (fun i : Fin r => (t i.succ - t i.castSucc, a i.succ)) := by
  induction r generalizing prev with
  | zero => simp [List.ofFn_succ, gapWord]
  | succ r ih =>
      rw [List.ofFn_succ, gapWord, ih]
      congr 1
      rw [List.ofFn_succ]
      rfl

variable {M : Type*}

/-- The gap event is exactly membership at the corresponding absolute times,
relative to the initial offset. -/
theorem mem_pathEvent_gapWord_iff (prev : ℕ) (w : List (ℕ × Set M))
    (horder : w.Pairwise (fun p q => p.1 ≤ q.1)) (hprev : ∀ p ∈ w, prev ≤ p.1)
    (ω : ℕ → Option M) :
    ω ∈ pathEvent (gapWord prev w) ↔ ∀ p ∈ w, ω (p.1 - prev) ∈ Option.some '' p.2 := by
  induction w generalizing prev ω with
  | nil => simp [gapWord, pathEvent]
  | cons p w ih =>
      rcases p with ⟨n, A⟩
      have hnt := (List.pairwise_cons.mp horder).1
      have hwt := (List.pairwise_cons.mp horder).2
      have hn := hprev (n, A) (by simp)
      change (ω (n-prev) ∈ Option.some '' A ∧
        (fun k => ω ((n-prev)+k)) ∈ pathEvent (gapWord n w)) ↔ _
      rw [ih n hwt hnt]
      simp only [List.forall_mem_cons]
      apply and_congr_right
      intro _
      apply forall_congr'
      intro p
      apply forall_congr'
      intro hp
      have hnp := hnt p hp
      have he : n - prev + (p.1 - n) = p.1 - prev := by omega
      rw [he]

/-- Consecutive-gap observation word for an ordered finite tuple. -/
def timeWord {r : ℕ} (t : Fin (r+1) → ℕ) (A : Fin (r+1) → Set M) : List (ℕ × Set M) :=
  gapWord 0 (List.ofFn (fun i => (t i, A i)))

theorem timeWord_eq {r : ℕ} (t : Fin (r+1) → ℕ) (A : Fin (r+1) → Set M) :
    timeWord t A = (t 0, A 0) ::
      List.ofFn (fun i : Fin r => (t i.succ - t i.castSucc, A i.succ)) := by
  simpa [timeWord] using gapWord_ofFn r 0 t A

/-- No Markov property is needed for the deterministic event identity. -/
theorem pathEvent_timeWord {r : ℕ} (t : Fin (r+1) → ℕ) (ht : Monotone t)
    (A : Fin (r+1) → Set M) :
    pathEvent (timeWord t A) = {ω : ℕ → Option M | ∀ i, ω (t i) ∈ Option.some '' A i} := by
  ext ω
  have ho : (List.ofFn (fun i => (t i, A i))).Pairwise (fun p q => p.1 ≤ q.1) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact ht hij.le
  rw [timeWord, mem_pathEvent_gapWord_iff 0 _ ho (fun _ _ => Nat.zero_le _)]
  simp only [List.forall_mem_ofFn_iff, Nat.sub_zero, Set.mem_ofPred_eq]

theorem timeWord_ne_nil {r : ℕ} (t : Fin (r+1) → ℕ) (A : Fin (r+1) → Set M) :
    timeWord t A ≠ [] := by rw [timeWord_eq]; simp

/-- Every target label in the gap word comes from the original tuple. -/
theorem forall_timeWord_targets {r : ℕ} (t : Fin (r+1) → ℕ) (A : Fin (r+1) → Set M)
    (P : Set M → Prop) (hP : ∀ i, P (A i)) : ∀ p ∈ timeWord t A, P p.2 := by
  rw [timeWord_eq]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hP 0
  · rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
    exact hP i.succ


/-- Adjacent positive gaps telescope to the elapsed absolute time. -/
theorem first_add_sum_gaps (r : ℕ) (t : Fin (r+1) → ℕ) (ht : Monotone t) :
    t 0 + ∑ i : Fin r, (t i.succ - t i.castSucc) = t (Fin.last r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hi := ih (fun i => t i.succ) (fun i j hij => ht (Fin.succ_le_succ_iff.mpr hij))
      change t (0 : Fin (r+1)).succ +
        (∑ i : Fin r, (t i.succ.succ - t i.castSucc.succ)) = t (Fin.last (r+1)) at hi
      have hfirst : t 0 ≤ t (0 : Fin (r+1)).succ := ht (Fin.zero_le _)
      rw [Fin.sum_univ_succ]
      have he : (∑ i : Fin r, (t i.succ.succ - t i.succ.castSucc)) =
          ∑ i : Fin r, (t i.succ.succ - t i.castSucc.succ) := rfl
      rw [he]
      simp only [Fin.castSucc_zero] at *
      omega

/-- The word consumes exactly the last observation time, so the remaining survival interval is the
horizon minus that time. -/
theorem totalTime_timeWord {r : ℕ} (t : Fin (r+1) → ℕ) (ht : Monotone t)
    (A : Fin (r+1) → Set M) :
    totalTime (indicatorObservations (timeWord t A)) = t (Fin.last r) := by
  rw [timeWord_eq]
  simpa [totalTime, indicatorObservations, List.map_ofFn, List.sum_ofFn] using first_add_sum_gaps r t ht

end ConditionedStableLaws.OrderedPathEvents
