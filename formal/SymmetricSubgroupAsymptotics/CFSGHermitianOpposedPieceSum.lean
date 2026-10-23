import SymmetricSubgroupAsymptotics.CFSGHermitianOpposedSum

/-! Remove the actual nonzero cross multiplier between two local
linear pieces by rescaling only the second piece. The rescaling changes
no projective ray and yields an exact isometry on the original sum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters CFSGHermitianOpposedSum
variable {K I : Type*} [Field K] [Finite K] [Fintype I]

theorem exists_normalized_opposed_sum (sigma : K ≃+* K) (H : Matrix I I K)
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (P Z : IsotropicSpace sigma H) (d : ℕ)
    (hP : Module.finrank K P.val = d+2) (hZ : Module.finrank K Z.val = d+2)
    (hND : ∀ x : P.val, (∀ y : Z.val, hermitianPair sigma H x.val y.val = 0) → x = 0)
    (F : SemilinearPiece sigma H f P (RingEquiv.refl K))
    (G : SemilinearPiece sigma H f Z (RingEquiv.refl K))
    (delta : K)
    (hflip : ∀ x y, hermitianPair sigma H y x = delta * sigma (hermitianPair sigma H x y)) :
    ∃ c : K, c ≠ 0 ∧ ∀ v w : P.val × Z.val,
      hermitianPair sigma H
        (imageSum P.val Z.val F.map (c⁻¹ • G.map) v)
        (imageSum P.val Z.val F.map (c⁻¹ • G.map) w) =
      hermitianPair sigma H (sourceSum P.val Z.val v) (sourceSum P.val Z.val w) := by
  obtain ⟨c,hc,hcross⟩ := linearPiece_opposed_pair_multiplier sigma H f hf P Z d hP hZ hND F G
  have hF (x y : P.val) : hermitianPair sigma H (F.map x) (F.map y) = 0 :=
    (semilinearPiece_cross_zero_iff sigma H f hf P P (RingEquiv.refl K)
      (RingEquiv.refl K) F F x y).mpr (P.property _ x.property _ y.property)
  have hG (x y : Z.val) : hermitianPair sigma H (G.map x) (G.map y) = 0 :=
    (semilinearPiece_cross_zero_iff sigma H f hf Z Z (RingEquiv.refl K)
      (RingEquiv.refl K) G G x y).mpr (Z.property _ x.property _ y.property)
  have hb (x y : Z.val) : hermitianPair sigma H
      ((c⁻¹ • G.map) x) ((c⁻¹ • G.map) y) = 0 := by
    change hermitianPair sigma H (c⁻¹ • G.map x) (c⁻¹ • G.map y) = 0
    rw [hermitianPair_smul,hG,mul_zero]
  have hpair (x : P.val) (y : Z.val) : hermitianPair sigma H
      (F.map x) ((c⁻¹ • G.map) y) = hermitianPair sigma H x.val y.val := by
    change hermitianPair sigma H (F.map x) (c⁻¹ • G.map y) = _
    have hh := hermitianPair_smul sigma H 1 c⁻¹ (F.map x) (G.map y)
    rw [one_smul,map_one,one_mul,hcross,← mul_assoc,inv_mul_cancel₀ hc,one_mul] at hh
    exact hh
  exact ⟨c,hc,sum_pair sigma H P.val Z.val F.map (c⁻¹ • G.map)
    P.property Z.property hF hb hpair delta hflip⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
