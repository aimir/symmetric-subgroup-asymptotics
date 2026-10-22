import SymmetricSubgroupAsymptotics.CFSGSymplecticHyperbolicPairCardinality

/-! At rank one, an ordered hyperbolic pair is exactly the two columns
of a determinant-one matrix. This supplies the elementary base order
without a separate published special-linear order formula. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable (K : Type) [Field K]

 def pairColumns (p : HyperbolicPairs K 1) : Mat K 1 :=
  fun i => Sum.elim (fun _ => p.val.1 i) (fun _ => p.val.2 i)

 theorem pairColumns_det (p : HyperbolicPairs K 1) : (pairColumns K p).det = 1 := by
  let e : Index 1 ≃ Fin 2 := finSumFinEquiv
  rw [← Matrix.det_reindex_self e, Matrix.det_fin_two]
  change p.val.1 (Sum.inl 0) * p.val.2 (Sum.inr 0) -
    p.val.2 (Sum.inl 0) * p.val.1 (Sum.inr 0) = 1
  simpa only [pairing, Fin.sum_univ_one, mul_comm] using p.property

 def rankOnePairsEquiv : elementaryRootGroup K 1 ≃ HyperbolicPairs K 1 where
  toFun g := g • standardHyperbolicPair K 0
  invFun p := ⟨Matrix.SpecialLinearGroup.toGL ⟨pairColumns K p, pairColumns_det K p⟩,
    rankOne_SL_toGL_mem K _⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    change pairColumns K (g • standardHyperbolicPair K 0) i j = (g.val : Mat K 1) i j
    cases j with
    | inl j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change ((g.val : Mat K 1) *ᵥ Pi.single (Sum.inl 0) 1) i = _
      simp only [Matrix.mulVec_single_one, Matrix.col_apply]
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change ((g.val : Mat K 1) *ᵥ Pi.single (Sum.inr 0) 1) i = _
      simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change (pairColumns K p *ᵥ Pi.single (Sum.inl 0) 1) i = p.val.1 i
      simp only [Matrix.mulVec_single_one, Matrix.col_apply]
      rfl
    · funext i
      change (pairColumns K p *ᵥ Pi.single (Sum.inr 0) 1) i = p.val.2 i
      simp only [Matrix.mulVec_single_one, Matrix.col_apply]
      rfl

 theorem elementary_rankOne_card [Finite K] :
    Nat.card (elementaryRootGroup K 1) = (Nat.card K ^ 2 - 1) * Nat.card K := by
  rw [Nat.card_congr (rankOnePairsEquiv K), hyperbolicPairs_card]
  norm_num

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
