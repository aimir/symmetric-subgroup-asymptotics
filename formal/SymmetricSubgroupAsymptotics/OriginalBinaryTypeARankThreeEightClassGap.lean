import SymmetricSubgroupAsymptotics.PrimitivePermutationHalfOrderRecognition
import SymmetricSubgroupAsymptotics.OriginalBinaryNaturalEightClassGap
import SymmetricSubgroupAsymptotics.CFSGTypeARankThreeCardTwo

/-! The actual eight-point top with one original PSL4(2) socle factor
has at least half the symmetric-group order, hence is literally A(X)
or Sym(X). The proved natural binary action bound then pays the SAME
original subnormal subgroup. No PSL4(2) to A8 recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalBinaryTypeARankThreeEightClassGap
open OriginalBlockClassBound PrimitiveSocleRawStructure

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]

theorem subnormal_class_cube_gap_of_single_factor_degree_eight
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (x₀ : X) (htwo : Nat.card (originalBlockFibre b x₀)=2)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.A 3 q)
    (hk : D.factorCount=1) (hdegree : Nat.card X=8)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI := Fintype.ofFinite X
  letI := Classical.decEq X
  have hs : Nat.card D.Simple=20160 :=
    (Nat.card_congr e.toEquiv).trans (CFSGTypeARankThreeCardTwo.order_eq_20160 q hq)
  have hnatural := PrimitivePermutationHalfOrderRecognition.alternating_or_top_of_single_factor_half_order
    (Top (A := A) (X := X)) D hk (by omega) (by rw [hdegree,hs]; decide)
  have htop : (Top (A := A) (X := X)).IsSubnormal := by
    rcases hnatural with h | h
    · rw [h]
      exact Subgroup.Normal.isSubnormal inferInstance
    · rw [h]
      exact Subgroup.IsSubnormal.top
  exact OriginalBinaryNaturalEightClassGap.subnormal_class_cube_gap_at_original_degree
    b hb x₀ htwo (by omega) htop H hH

end SymmetricSubgroupAsymptotics.OriginalBinaryTypeARankThreeEightClassGap
