import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147Centralizer0
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147Centralizer1
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147Centralizer2
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147Centralizer3
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147Centralizer4

/-!
# Selected six-pair action 147: complete class cover

This is a resource-bounded split of the selected action-147 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

noncomputable def centralizer : ∀ i : Fin 5,
    FinitePairCentralizerCoordinateCertificate
      (Subgroup.centralizer ({representative i} : Set Source)) 6 :=
  (Fin.cases C0.centralizer (Fin.cases C1.centralizer (Fin.cases C2.centralizer (Fin.cases C3.centralizer (Fin.cases C4.centralizer (fun i => Fin.elim0 i))))))

private def claimedCardRows (i : Fin 5) : ℕ :=
  (if i.val < 2 then (if i.val < 1 then 60 else 5) else (if i.val < 3 then 5 else (if i.val < 4 then 4 else 3)))

private theorem centralizer_claimedCard : ∀ i : Fin 5,
    (centralizer i).claimedCard = claimedCardRows i :=
  (Fin.cases (by rfl) (Fin.cases (by rfl) (Fin.cases (by rfl) (Fin.cases (by rfl) (Fin.cases (by rfl) (fun i => Fin.elim0 i))))))

private theorem claimed_class_sum :
    (∑ i : Fin 5, Nat.card Source / (centralizer i).claimedCard) =
      Nat.card Source := by
  rw [source_card]
  simp_rw [centralizer_claimedCard]
  norm_num [claimedCardRows, Fin.sum_univ_succ]

/-- Kernel-checked complete conjugacy-class chunk for the selected action. -/
noncomputable def conjugacyChunk :
    FiniteConjugacyCentralizerCoordinateChunk representative 6 :=
  finiteConjugacyCentralizerCoordinateChunk_ofInvariant
    ambient representative ambient_full classInvariant centralizer
      claimed_class_sum

/-- Complete class cover derived from the checked invariant and coordinate
charts, without a producer coverage assertion. -/
noncomputable def conjugacyCover :
    FiniteConjugacyCardinalCover representative :=
  conjugacyChunk.toCardinalCover
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassPilot

end
