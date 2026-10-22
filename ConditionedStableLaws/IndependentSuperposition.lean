import ConditionedStableLaws.CountablePoissonSums

/-! Independence of countable superpositions over disjoint sets. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ConditionedStableLaws
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

/-- Independence is preserved by a measurable change of probability space
with the prescribed law. -/
theorem independent_pullback
    {J Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : Ω → Ω') (hZ : Measurable Z) (hLaw : HasLaw Z Q P)
    (X : J → Ω' → E) (hm : ∀ j, Measurable (X j)) (hi : iIndepFun X Q) :
    iIndepFun (fun j ω => X j (Z ω)) P := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (X := fun j ω => X j (Z ω)) (fun j => (hm j).comp hZ)).mpr
  have hj : P.map (fun ω j => X j (Z ω)) = Q.map (fun ω j => X j ω) := by
    rw [← hLaw.map_eq, Measure.map_map (Measurable.of_eval hm) hZ]
    rfl
  have hk (j : J) : P.map (fun ω => X j (Z ω)) = Q.map (X j) := by
    rw [← hLaw.map_eq, Measure.map_map (hm j) hZ]
    rfl
  rw [hj, hi.map_fun_eq_infinitePi_map hm]
  simp_rw [hk]

/-- Regrouping a jointly independent array into rows preserves independence. -/
theorem independent_rows_of_independent_array
    {ι κ Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → κ → Ω → E) (hm : ∀ i j, Measurable (X i j))
    (hi : iIndepFun (fun p : ι × κ => X p.1 p.2) P) :
    iIndepFun (fun i ω j => X i j ω) P := by
  let (i : ι) (j : κ) : IsProbabilityMeasure (P.map (X i j)) :=
    (Measure.isProbabilityMeasure_map_iff (hm i j).aemeasurable).mpr inferInstance
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have hrow (i : ι) : P.map (fun ω j => X i j ω) =
      Measure.infinitePi (fun j => P.map (X i j)) := by
    apply iIndepFun.map_fun_eq_infinitePi_map (hm i)
    exact hi.precomp (g := fun j : κ => (i, j)) (fun _ _ h => (Prod.mk.inj h).2)
  simp_rw [hrow]
  have hmap := hi.map_fun_eq_infinitePi_map (fun p : ι × κ => hm p.1 p.2)
  have hcomp : (MeasurableEquiv.curry ι κ E) ∘ (fun ω p => X p.1 p.2 ω) =
      (fun ω i j => X i j ω) := rfl
  rw [← hcomp, ← Measure.map_map (MeasurableEquiv.curry ι κ E).measurable (by fun_prop),
    hmap]
  exact Measure.infinitePi_map_curry (fun i j => P.map (X i j))

/-- Independent rows of independently scattered counts can be superposed
columnwise, including when a column has an infinite sum. -/
theorem independent_countable_sums
    {J Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → J → Ω → ℝ≥0∞) (hm : ∀ n j, Measurable (X n j))
    (hrows : iIndepFun (fun n ω j => X n j ω) P)
    (hwithin : ∀ n, iIndepFun (X n) P) :
    iIndepFun (fun j ω => ∑' n, X n j ω) P := by
  have ha := iIndepFun_uncurry' hm hrows hwithin
  have hb : iIndepFun (fun p : J × ℕ => X p.2 p.1) P :=
    ha.precomp Prod.swap_injective
  have hc := independent_rows_of_independent_array P (fun j n => X n j)
    (fun j n => hm n j) hb
  exact hc.comp (fun _ x => ∑' n, x n) (fun _ => Measurable.tsum (fun _ => measurable_pi_apply _))

end
end ConditionedStableLaws
