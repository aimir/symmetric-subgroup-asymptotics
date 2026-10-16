import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFourPointFullBinary
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.QuotientSocleRelativeHead

/-! The original zero-core four-by-four source: every actual quotient
has two ambient socle generators, and every original binary normal
relative head has dimension at most two. The only published input is the
already explicit McIver--Neumann bound for nonbinary top-carried types. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourZeroCoreFourPointSocleSource_localFact1 : Fact P.p.Prime := ⟨P.p_prime⟩


theorem degreeFourZeroCore_fourPoint_top_not_isPGroup
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P = ⊥) : ¬ IsPGroup 2 block.Top := by
  intro hTop
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let i : block.Points := (Finite.equivFinOfCardEq hs).symm 0
  let e := degreeFourZeroCoreTopEquiv block P hr hD
  have hQ : IsPGroup 2 (DegreeFourComplementQuotient block P) :=
    hTop.of_injective e.toMonoidHom e.injective
  have hH := hQ.to_subgroup (fullFrameInducedStabilizer block P i)
  have hL : IsPGroup 2 (LocalQuotient block P) :=
    hH.of_surjective (binaryAffineStabilizerComponent block P i)
      (binaryAffineStabilizerComponent_surjective block P i)
  have hthree : 3 ∣ Nat.card (LocalQuotient block P) := by
    rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with h3 | h6
    · simpa only [h3] using (dvd_refl 3)
    · rw [h6]; decide
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hL
  rw [hn] at hthree
  have hbad := (by decide : Nat.Prime 3).dvd_of_dvd_pow hthree
  norm_num at hbad

theorem degreeFourZeroCore_fourPoint_quotientSocle_le_two
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    SocleNormalGeneratorBound (DegreeFourRetainedQuotient N) 2 := by
  have hTop := degreeFourZeroCore_fourPoint_top_not_isPGroup block P hr hs hD
  let Q := DegreeFourRetainedQuotient N
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hprimary : DegreeFourFullBinarySocle block P N =
      minimalNormalSoclePart Q (fun M => IsPGroup 2 M) := by
    change minimalNormalSoclePart Q (fun M => True ∧ IsPGroup P.p M) = _
    apply minimalNormalSoclePart_congr Q _ _
    intro M _
    simp only [true_and, degreeFour_profilePrime_eq_two block P hr]
  apply (socleNormalGeneratorBound_iff_normalGen_le Q 2).2
  apply (normalGen_finiteGroupSocle_le_max_primePrimaryParts 2 Q).trans
  apply max_le
  · rw [← hprimary]
    exact degreeFourZeroCore_fourPoint_fullBinary_normalGen_le_two block P hr hs hD hTop N
  · simpa [hs, degreeFourSocleSlots] using
      degreeFourZeroCore_nonbinary_normalGen_le_slots block P hMN hr hD (by omega) N

theorem degreeFourZeroCore_fourPoint_binary_relative_head_le_two
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre = 4) (hs : Nat.card block.Points = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 := by
  exact primeRelativeHead_le_of_all_quotient_socles 2 2
    (fun K => degreeFourZeroCore_fourPoint_quotientSocle_le_two block P hMN hr hs hD K) N

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
