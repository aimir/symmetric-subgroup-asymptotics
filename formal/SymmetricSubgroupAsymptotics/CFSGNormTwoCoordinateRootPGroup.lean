import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootOrbitTransitive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters

/-! Every lattice-labelled actual root subgroup is a defining-prime
group, by a literal word conjugating an original positive simple root.
No representation-faithfulness or projective-intersection premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPGroup
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootOrbitTransitive CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinatePositivePGroup CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoGeckWeylWordDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem rootSubgroup_isPGroup (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (k : Roots A) : IsPGroup p (rootSubgroup A hd hs hp ho K k) := by
  let j : Fin r := (rootWitness A hd hs hp ho k).val.2
  have hj : ∀i,0≤(s₀ j : Roots A).val i := by
    intro i
    change 0≤(Pi.single j (1:ℤ) : Fin r→ℤ) i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hL := positive_root_subgroup_le A hd hs hp ho K (s₀ j) hj
  have hLp : IsPGroup p (rootSubgroup A hd hs hp ho K (s₀ j)) :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p false).of_injective
      (Subgroup.inclusion hL) (Subgroup.inclusion_injective hL)
  obtain ⟨w,hw⟩ := rootSubgroup_conjugate_by_word A hd hs hp ho K (s₀ j) k
  have hm := hLp.map (MulAut.conj (wordUnit A hs hp b₀ s₀ K w)).toMonoidHom
  rwa [hw] at hm

theorem rootSubgroupInElementary_isPGroup (K : Type) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (k : Roots A) :
    IsPGroup p ((rootSubgroup A hd hs hp ho K k).subgroupOf (ElementaryGroup A hd hs hp ho K)) :=
  (rootSubgroup_isPGroup A hd hs hp ho K p k).of_injective
    (Subgroup.subgroupOfEquivOfLe (rootSubgroup_le_elementary A hd hs hp ho K k)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (rootSubgroup_le_elementary A hd hs hp ho K k)).injective

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPGroup
