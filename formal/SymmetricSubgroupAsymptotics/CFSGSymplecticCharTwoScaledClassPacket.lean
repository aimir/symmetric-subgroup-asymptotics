import SymmetricSubgroupAsymptotics.SiegelPointIndexComparison
import SymmetricSubgroupAsymptotics.RankThreePointRadicalScaledClassEnvelope
import SymmetricSubgroupAsymptotics.OrthogonalPointRadicalScaledClassEnvelope
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryHigherSiegelIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds

/-! A single literal elementary symplectic backend pays every
characteristic-two rank at least three except the binary rank-three
head. Higher Siegel and binary point stabilizers give the SAME point
quantity. The checked binary rank-four class code fills its head.
No original-C simplicity is needed when this is applied to actual B. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticCharTwoScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction CFSGSymplecticSerreMatrices
open OrthogonalPointRadicalOrderCubeNumerics

private theorem center_eq_bot {S : Type} [Group S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S) : Subgroup.center S=⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim

private theorem scaled_of_point_index {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (r q : ℕ) (hr : 3 ≤ r) (hq : 2 ≤ q) (hwindow : 3 ≤ q ∨ 5 ≤ r)
    (hn : ¬IsMulCommutative S)
    (horder : Nat.card S ≤ q^(2*r^2+r)) (houter : Nat.card (Outer S) ≤ q^3)
    (hi : ∀ K : Subgroup S, K ≠ ⊤ → (q^(r-1)-1)*q^(r-1) ≤ K.index)
    (K : Subgroup S) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 3^K.index := by
  by_cases hr4 : 4 ≤ r
  · have hb : 0 < minusIndex q r := lt_of_lt_of_le (by decide : 0 < 32)
      (minusIndex_ge_thirtyTwo q r (by omega) hr4 hwindow)
    have hindex : ∀ J : Subgroup S, J ≠ ⊤ → minusIndex q r ≤ J.index := by
      intro J hJ
      have hp : q^(r-2)-1 ≤ q^(r-1)-1 := Nat.sub_le_sub_right
        (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : r-2 ≤ r-1)) 1
      exact (Nat.mul_le_mul_right _ hp).trans (hi J hJ)
    have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
      (minusIndex q r) hb (center_eq_bot hn) hindex).trans
      (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
    have ho : Nat.card (Outer S) ≤ q^6 := houter.trans
      (Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 3 ≤ 6))
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
      (OrthogonalPointRadicalScaledClassEnvelope.scaled_class_equation_budget
        q r (by omega) hr4 hwindow)).trans
        (Nat.pow_le_pow_right (by decide) (hindex K hK))
  · have hr3 : r=3 := by omega
    subst r
    have hq3 : 3 ≤ q := by rcases hwindow with h | h; exact h; omega
    have hindex : ∀ J : Subgroup S, J ≠ ⊤ → (q^2-1)*q^2 ≤ J.index := hi
    have hq2 : 9 ≤ q^2 := (by decide : 9 ≤ (3:ℕ)^2).trans
      (Nat.pow_le_pow_left hq3 2)
    have hb : 0 < (q^2-1)*q^2 := Nat.mul_pos (by omega) (by omega)
    have horder21 : Nat.card S ≤ q^21 := horder
    have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
      ((q^2-1)*q^2) hb (center_eq_bot hn) hindex).trans
      (Nat.add_le_add_right (Nat.div_le_div_right horder21) 1)
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc houter) 3)).trans
      (RankThreePointRadicalScaledClassEnvelope.scaled_class_equation_budget q hq3)).trans
        (Nat.pow_le_pow_right (by decide) (hindex K hK))

theorem elementary_scaled_class_cube_le_proper_index
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hp : q.prime=2)
    [IsSimpleGroup (elementaryProjective q.Field r)] [Finite (elementaryProjective q.Field r)]
    (hn : ¬IsMulCommutative (elementaryProjective q.Field r))
    (hhead : ¬(r=3 ∧ q.order=2))
    (J : Subgroup (elementaryProjective q.Field r)) (hJ : J ≠ ⊤) :
    25*(Nat.card (ConjClasses (elementaryProjective q.Field r))*
      Nat.card (Outer (elementaryProjective q.Field r)))^3 ≤ 3^J.index := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
  letI : CharP q.Field 2 := by rw [←hp]; infer_instance
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hquot : Nat.card (elementaryProjective q.Field (s+3)) ≤
      Nat.card (elementaryRootGroup q.Field (s+3)) :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center _))
      (QuotientGroup.mk'_surjective _)
  have horder : Nat.card (elementaryProjective q.Field (s+3)) ≤
      q.order^(2*(s+3)^2+(s+3)) := hquot.trans (by
    simpa only [q.card_field] using
      CFSGSymplecticSharpOrderUpper.elementary_card_le_quadratic_power q.Field (s+3))
  have hout : Nat.card (Outer (elementaryProjective q.Field (s+3))) ≤ 3*q.exponent := by
    simpa only [Nat.add_assoc,Nat.reduceAdd,
      CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      CFSGSymplecticPointRootLabels.binary_outer_card_le
        (K := q.Field) (s+2) (by omega)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hthree : 3 ≤ q.order^2 := (by decide : 3 ≤ (2:ℕ)^2).trans
    (Nat.pow_le_pow_left hq 2)
  have houter : Nat.card (Outer (elementaryProjective q.Field (s+3))) ≤ q.order^3 :=
    hout.trans ((Nat.mul_le_mul hthree hf).trans_eq (pow_succ q.order 2).symm)
  have hindex : ∀ K : Subgroup (elementaryProjective q.Field (s+3)), K ≠ ⊤ →
      (q.order^((s+3)-1)-1)*q.order^((s+3)-1) ≤ K.index := by
    intro K hK
    by_cases hq3 : 3 ≤ q.order
    · apply SiegelPointIndexComparison.point_index_le_of_siegel_numerator
        q.order (s+3) K.index hq3 (by omega)
      have hb := CFSGSymplecticBinaryHigherSiegelIndex.projective_two_frame_le_two_mul_proper_index
        q.Field (s+2) (by omega) K hK
      simpa only [q.card_field,show s+3-2=s+1 by omega,show s+2-1=s+1 by omega,
        Nat.add_assoc,Nat.reduceAdd] using hb
    · have hq2 : q.order=2 := by omega
      have hb := CFSGSymplecticBinaryPointIndex.binary_point_radical_proper_index
        q.Field (q.card_field.trans hq2) (s+3) (by omega) K hK
      have he : (q.order^((s+3)-1)-1)*q.order^((s+3)-1)=
          2^((s+3)-1)*(2^((s+3)-1)-1) := by rw [hq2]; ring
      exact he.le.trans hb
  by_cases hwindow : 3 ≤ q.order ∨ 5 ≤ s+3
  · exact scaled_of_point_index (s+3) q.order (by omega) hq hwindow hn
      horder houter hindex J hJ
  · have hq2 : q.order=2 := by omega
    have hs : s=1 := by omega
    subst s
    have he : q.exponent=1 :=
      (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two q.exponent_pos.ne'
        (by decide : (1:ℕ) ≠ 0) (show q.prime^q.exponent=2^1 from hq2)).2
    have hclasses : Nat.card (ConjClasses (elementaryProjective q.Field 4)) ≤ 448 :=
      (Nat.card_le_card_of_surjective
        (ConjClasses.map (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup q.Field 4))))
        (ConjClasses.map_surjective (QuotientGroup.mk'_surjective _))).trans
        (CFSGSymplecticSmallClassBounds.binary_rankFour q.Field (q.card_field.trans hq2))
    have ho : Nat.card (Outer (elementaryProjective q.Field 4)) ≤ 3 := by
      simpa only [he,mul_one] using hout
    have hi : 56 ≤ J.index := by
      have hh := hindex J hJ
      norm_num [hq2] at hh
      exact hh
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hclasses ho) 3)).trans
      (by decide +kernel : 25*((448:ℕ)*3)^3 ≤ 3^56)).trans
        (Nat.pow_le_pow_right (by decide) hi)

end SymmetricSubgroupAsymptotics.CFSGSymplecticCharTwoScaledClassPacket
