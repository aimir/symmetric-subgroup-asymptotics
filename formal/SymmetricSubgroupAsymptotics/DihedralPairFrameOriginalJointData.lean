import SymmetricSubgroupAsymptotics.DihedralBinaryOriginalQuotientSocles
import SymmetricSubgroupAsymptotics.SixPairCyclicOriginalKernelHead
import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Physical original dihedral pair actions with an actual two-cyclic
abelianization cover have original quotient-socle bound two. The cover is
structural group data and can include a cyclic-four coordinate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralPairFrameOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

 theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (g : U)
    (hg : F.top g=SixPairCyclicSymmetricSocles.cycle)
    (beta : F.top.range →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hB : Nat.card F.top.range=12) (hker : Nat.card beta.ker=2)
    {C D : Type} [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (cover : C × D →* U ⧸ commutator U) (hcover : Function.Surjective cover)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  let E := SixPairPrimitiveAllNormalB6.originalKernelChart F
  have hsame : F.top.rangeRestrict.ker=F.top.ker := by
    ext u
    change F.top.rangeRestrict u=1 ↔ F.top u=1
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  have hK : IsMulCommutative F.top.rangeRestrict.ker :=
    isMulCommutative_iff.mpr (fun x y =>
      E.equiv.symm.injective (by rw [map_mul,map_mul,mul_comm]))
  have hheads : ∀ (L : Subgroup U) [L.Normal], L≤F.top.rangeRestrict.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤1 := by
    intro L _hL hL
    exact SixPairCyclicOriginalKernelHead.normal_kernel_head_le_one F g hg L (hsame ▸ hL)
  have htwo : IsPGroup 2 F.top.rangeRestrict.ker :=
    E.kernel_isPGroup_two F.top.rangeRestrict (SixPairPrimitiveAllNormalB6.kernelModule F)
  exact DihedralBinaryOriginalQuotientSocles.quotientSocle beta hbeta hB hker
    F.top.rangeRestrict F.top.rangeRestrict_surjective hK hheads cover hcover
    (by simp : Nat.card (Fin 12)=12) htwo N

 def jointData (T : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame T.top (Fin 6)) (g : T.top)
    (hg : F.top g=SixPairCyclicSymmetricSocles.cycle)
    (beta : F.top.range →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hB : Nat.card F.top.range=12) (hker : Nat.card beta.ker=2)
    {C D : Type} [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (cover : C × D →* T.top ⧸ commutator T.top) (hcover : Function.Surjective cover)
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T.top (Fin 12)) 2) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData T 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    T.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle F g hg beta hbeta hB hker cover hcover N.1)
  natural := hnatural

end SymmetricSubgroupAsymptotics.DihedralPairFrameOriginalJointData
