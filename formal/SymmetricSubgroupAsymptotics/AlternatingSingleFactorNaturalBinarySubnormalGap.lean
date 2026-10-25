import SymmetricSubgroupAsymptotics.PrimitiveAlternatingNaturalDegreeRecognition
import SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap

/-! A natural-degree alternating descriptor is recognized in its
ACTUAL top permutation subgroup before applying binary wreath fusion.
The subnormal source subgroup is not assumed transitive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingSingleFactorNaturalBinarySubnormalGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

theorem subnormal_class_cube_gap
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (x₀ : X) (htwo : Nat.card (originalBlockFibre b x₀)=2)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 10 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount=1) (hdegree : Nat.card X=m)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI := Fintype.ofFinite X
  letI := Classical.decEq X
  have hnatural := PrimitiveAlternatingNaturalDegreeRecognition.alternating_or_top_of_single_factor_natural_degree
    (Top (A := A) (X := X)) D m (by omega) e hk hdegree
  have htop : (Top (A := A) (X := X)).IsSubnormal := by
    rcases hnatural with h | h
    · rw [h]
      exact Subgroup.Normal.isSubnormal inferInstance
    · rw [h]
      exact Subgroup.IsSubnormal.top
  exact OriginalBinaryBlockSubnormalClassGap.subnormal_class_cube_gap_at_original_degree
    b hb x₀ htwo (by omega) htop H hH

end SymmetricSubgroupAsymptotics.AlternatingSingleFactorNaturalBinarySubnormalGap
