import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop2NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop3NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop4NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop5NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop6NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop7NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop8NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop9NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop10NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop11NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop12NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop13NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop14NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop15NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop16NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop17NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop19NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop21NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop22NormalizerHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairCanonicalSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTopRelativeHeads

/-!
The complete eight-point family, with the original stabilizer and local
representation retained. Twenty literal head bounds use small Sylow
point-word certificates; the other four entries are excluded by the actual
local epimorphism. The same family applies to an original eight-point top
and to the actual eight-pair quotient of a sixteen-point top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeFourEightTopHeads

theorem literal_head_le_two (j : Fin 24)
    (hj : ¬ DegreeFourEightTopEligibility.Excluded j)
    {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : MulAction.stabilizer (DegreeTwoPairedEightSharedTops.interface j).top
      (0 : Fin 8) →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod 2) L V)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind
      (MulAction.stabilizer (DegreeTwoPairedEightSharedTops.interface j).top
        (0 : Fin 8)).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2)
          (DegreeTwoPairedEightSharedTops.interface j).top (ZMod 2))) ≤ 2 := by
  fin_cases j
  · exact PrimitiveAffineEightTop1NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop2NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop3NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop4NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop5NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop6NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop7NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop8NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop9NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop10NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop11NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop12NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop13NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop14NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop15NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop16NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop17NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact False.elim (hj (Or.inl rfl))
  · exact PrimitiveAffineEightTop19NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact False.elim (hj (Or.inr (Or.inl rfl)))
  · exact PrimitiveAffineEightTop21NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact PrimitiveAffineEightTop22NormalizerHead.literal_head_le_two f hf hL rho hdim hrho B
  · exact False.elim (hj (Or.inr (Or.inr (Or.inl rfl))))
  · exact False.elim (hj (Or.inr (Or.inr (Or.inr rfl))))

theorem literal_head_le_two_at {p : ℕ} [Fact p.Prime] (hp : p = 2)
    (j : Fin 24) (hj : ¬ DegreeFourEightTopEligibility.Excluded j)
    {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (f : MulAction.stabilizer (DegreeTwoPairedEightSharedTops.interface j).top
      (0 : Fin 8) →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod p) L V)
    (hdim : Module.finrank (ZMod p) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind
      (MulAction.stabilizer (DegreeTwoPairedEightSharedTops.interface j).top
        (0 : Fin 8)).subtype (rho.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod p)
          (DegreeTwoPairedEightSharedTops.interface j).top (ZMod p))) ≤ 2 := by
  subst p
  exact literal_head_le_two j hj f hf hL rho hdim hrho B

/-- Transport the complete family through the exact original point chart. -/
theorem matched_head_le_two {p : ℕ} [Fact p.Prime] (hp : p = 2)
    {X : Type} [Finite X] (S : Subgroup (Equiv.Perm X))
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch S)
    (hj : ¬ DegreeFourEightTopEligibility.Excluded M.index)
    {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (f : MulAction.stabilizer S
      ((PermutationStabilizerTransport.pointEquiv M.points M.conjugator).symm 0) →* L)
    (hf : Function.Surjective f) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (rho : Representation (ZMod p) L V)
    (hdim : Module.finrank (ZMod p) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation (Representation.coind
      (MulAction.stabilizer S
        ((PermutationStabilizerTransport.pointEquiv M.points M.conjugator).symm 0)).subtype
      (rho.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod p) S (ZMod p))) ≤ 2 := by
  let T := (DegreeTwoPairedEightSharedTops.interface M.index).top
  let L0 := MulAction.stabilizer T (0 : Fin 8)
  let eG := PermutationStabilizerTransport.groupEquiv S T
    M.points M.conjugator M.matched
  let x := (PermutationStabilizerTransport.pointEquiv M.points M.conjugator).symm 0
  let H := MulAction.stabilizer S x
  let eH : H ≃* L0 := PermutationStabilizerTransport.stabilizerEquiv
    S T M.points M.conjugator M.matched 0
  let f' := f.comp eH.symm.toMonoidHom
  let eV : Representation.Equiv (rho.comp f) ((rho.comp f').comp eH.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl (ZMod p) V) (by
      intro h
      ext v
      change rho (f h) v = rho (f (eH.symm (eH h))) v
      rw [eH.symm_apply_apply])
  exact CoinducedGroupLocalTransport.uniform_head_le H L0 eG eH (fun _ => rfl)
    (rho.comp f) (rho.comp f') eV 2
    (fun A => literal_head_le_two_at hp M.index hj f'
      (hf.comp eH.symm.surjective) hL rho hdim hrho A) B

end DegreeFourEightTopHeads

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance degreeFourEightCompleteHeadSource_profilePrimeFact : Fact P.p.Prime := (chart block P).primeFact

local instance : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive

/-- The actual eight-point original frame has total capacity at most five. -/
def degreeFourZeroCoreEightBounds_of_match
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch block.Top) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  let T := (DegreeTwoPairedEightSharedTops.interface M.index).top
  let eG := PermutationStabilizerTransport.groupEquiv block.Top T
    M.points M.conjugator M.matched
  let x := (PermutationStabilizerTransport.pointEquiv M.points M.conjugator).symm 0
  have hj := DegreeFourEightTopEligibility.original_match_not_excluded block P hr hD
    M.index M.points M.conjugator M.matched
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD x 2 2 5 (by decide)
  · intro N _
    exact PrimitiveAffineEightTopRelativeHeads.relativeHead_le_two_of_equiv 2 M.index eG N
  · intro B
    apply DegreeFourEightTopHeads.matched_head_le_two
      (degreeFour_profilePrime_eq_two block P hr) block.Top M hj
      (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD x)
      (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD x)
      (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
      (binaryAffineLocalLinearRepresentation block P).ρ
      ?_ (binaryAffineLocalLinearRepresentation_injective block P) B
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2

/-- The nontrivial pair kernel is discharged using the actual descended
local epimorphism and the fixed eight-point family. -/
def degreeFourZeroCoreSixteenPairKernelNontrivialBounds_of_canonical
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker ≠ ⊥) (hI : Nat.card I = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let M := degreeFourPairTopMatch block P published hr hD F hI
  let T := (DegreeTwoPairedEightSharedTops.interface M.index).top
  let eG := PermutationStabilizerTransport.groupEquiv F.top.range T
    M.points M.conjugator M.matched
  let i := (PermutationStabilizerTransport.pointEquiv M.points M.conjugator).symm 0
  let f := degreeFourPairPointLocalMap block P hr hD F i
  have hf : Function.Surjective f :=
    degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD (F.frame (i, 0))
  let q := F.descendedPointLocalMap hker i f hf (degreeFourLocalTarget_eligible block P hr)
  have hq : Function.Surjective q :=
    F.descendedPointLocalMap_surjective hker i f hf (degreeFourLocalTarget_eligible block P hr)
  apply degreeFourZeroCoreSixteenPairKernelNontrivialBounds block P hr hD F hker hI i
  · intro N _
    exact PrimitiveAffineEightTopRelativeHeads.relativeHead_le_two_of_equiv 2 M.index eG N
  · intro B
    apply DegreeFourEightTopHeads.matched_head_le_two
      (degreeFour_profilePrime_eq_two block P hr) F.top.range M
      (degreeFourPairTopMatch_not_excluded block P hr hD F hker M)
      q hq (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
      (binaryAffineLocalLinearRepresentation block P).ρ
      ?_ (binaryAffineLocalLinearRepresentation_injective block P) B
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
