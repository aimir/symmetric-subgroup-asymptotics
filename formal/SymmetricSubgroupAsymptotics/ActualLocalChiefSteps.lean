import SymmetricSubgroupAsymptotics.LocalChiefNonabelianStep
import SymmetricSubgroupAsymptotics.LocalChiefCoprimeOrderStep
import SymmetricSubgroupAsymptotics.LocalChiefIntersectionStep
import SymmetricSubgroupAsymptotics.ChiefTernaryWeights
import SymmetricSubgroupAsymptotics.AbelianMinimalNormal

/-! Every actual local chief factor installs its correct original
intersection step. The three alternatives are proved from the actual
factor: ternary elementary, coprime order, and nonabelian. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A R : Type} [Group A] [Finite A] [Group R] [Finite R]
variable (N H : Subgroup A) [N.Normal] (θ : N→*R) (β : H→*R)
variable (hθ : ∀ (h:H) (n:N),θ (MulAut.conjNormal (h:A) n)=β h*θ n*(β h)⁻¹)
variable (hβ : Function.Surjective β)
variable (B L : Subgroup R) [B.Normal] [L.Normal] (hBL:B≤L)
variable (hc:∀K:Subgroup R,K.Normal → B≤K → K≤L → K=B ∨ K=L)
include hθ hβ hBL hc

theorem actualLocalChiefStep :
    TernaryChiefStep (localChiefIntersection N θ B) (localChiefIntersection N θ L) H
      (chiefTernaryWeight (normalChainQuotient B L)) := by
  classical
  have hmin := normalChiefFactor_minimal B L hBL hc
  by_cases hab : IsMulCommutative (normalChainQuotient B L)
  · letI := hab
    rcases abelian_minimal_normal_elementary_or_coprime (normalChainQuotient B L) 3 hmin
      with he|hp
    · obtain ⟨V,hV,hM,hD,⟨e⟩⟩ := he
      letI := hV
      letI := hM
      letI := hD
      rw [chiefTernaryWeight_elementary e]
      exact actualTernaryChiefIntersectionStep N H θ β hθ B L hBL e
    · rw [chiefTernaryWeight_coprime _ hp]
      apply actualCoprimeOrderChiefIntersectionStep N H θ B L hBL
      rw [ne_eq,ZMod.natCast_eq_zero_iff]
      exact Nat.prime_three.coprime_iff_not_dvd.mp hp.symm
  · rw [chiefTernaryWeight_nonabelian _ hab]
    exact actualNonabelianChiefIntersectionStep N H θ β hθ hβ B L hmin hab hBL

end SymmetricSubgroupAsymptotics
