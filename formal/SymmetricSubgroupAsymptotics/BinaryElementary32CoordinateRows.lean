import SymmetricSubgroupAsymptotics.BinaryElementary32DerivedHyperplaneOne
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateCenterCapacity
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank

/-! The sixteen literal row words are elements of the original elementary
sixteen-point top. Their bijection is certified by one point-vector orbit;
no original group element or normal-subgroup table is introduced. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance elementaryCoordinateRowsFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
namespace BinaryElementary32CoordinateRows
open BinaryElementary16GraphHeadRigidity

private theorem top_original : ∀ i : Fin 4,generatorTop i=1 ∨
    ∃ j : Fin 3,generatorTop i=BinaryMenuCayley8T3.generators j := by decide +kernel
private theorem offsets_mem : ∀ i : Fin 4,generatorOffset i∈
    (BinaryRegularEightNaturalRegistry.charts 23).2.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

def word {G : Type} [Group G] (u : Fin 4 → G) (i : Fin 16) : G :=
  (if i.val.testBit 0 then u 0 else 1)*
    ((if i.val.testBit 1 then u 1 else 1)*
      ((if i.val.testBit 2 then u 2 else 1)*(if i.val.testBit 3 then u 3 else 1)))

theorem word_action {G : Type} [Group G]
    (rho : Representation (ZMod 2) G V) (u : Fin 4 → G)
    (hu : ∀ i,rho (u i)=action i) (i : Fin 16) :
    rho (word u i)=BinaryElementary32DerivedHyperplaneOne.rowAction i := by
  unfold word BinaryElementary32DerivedHyperplaneOne.rowAction
  split_ifs <;> simp only [map_mul,map_one,hu] <;> rfl

private theorem word_vector_injective : Function.Injective
    (fun i : Fin 16 => BinaryElementary32DerivedHyperplaneOne.rowAction i
      (binaryVectorOfMask 16 257)) := by decide +kernel

theorem word_bijective {G : Type} [Group G] [Finite G]
    (rho : Representation (ZMod 2) G V) (u : Fin 4 → G)
    (hu : ∀ i,rho (u i)=action i) (hcard : Nat.card G=16) :
    Function.Bijective (word u) := by
  have hinj : Function.Injective (word u) := by
    intro i j he
    apply word_vector_injective
    have hh := congrArg (fun g => rho g (binaryVectorOfMask 16 257)) he
    simpa only [word_action rho u hu] using hh
  exact (Nat.bijective_iff_injective_and_card (word u)).mpr
    ⟨hinj,by simpa only [Nat.card_fin] using hcard.symm⟩

end BinaryElementary32CoordinateRows

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

include F E

theorem exists_original_elementary_coordinate_rows
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 23).2.space) :
    ∃ u : Fin 4 → F.top.range,
      ∀ i,E.originalCoordinateRepresentation (u i)=BinaryElementary16GraphHeadRigidity.action i := by
  have ht (i : Fin 4) : BinaryElementary16GraphHeadRigidity.generatorTop i∈E.top.range := by
    rw [hH]
    rcases BinaryElementary32CoordinateRows.top_original i with hi | ⟨j,hi⟩
    · rw [hi]
      exact Subgroup.one_mem _
    · rw [hi]
      exact Subgroup.subset_closure ⟨j,rfl⟩
  have ha (i : Fin 4) : BinaryElementary16GraphHeadRigidity.generatorOffset i∈E.kernelSpace := by
    rw [hK]
    exact BinaryElementary32CoordinateRows.offsets_mem i
  let u : Fin 4 → F.top.range := fun i => E.originalZeroRow hzero
    ⟨BinaryElementary16GraphHeadRigidity.generatorTop i,ht i⟩
    (BinaryElementary16GraphHeadRigidity.generatorOffset i) (ha i)
  refine ⟨u,fun i => ?_⟩
  exact E.originalCoordinateRepresentation_zeroRow hzero
    ⟨BinaryElementary16GraphHeadRigidity.generatorTop i,ht i⟩ _ (ha i)

/-- All four original coordinate rows and every one of their sixteen
word products belong to the same actual top, and cover it exactly. -/
theorem exists_bijective_original_elementary_coordinate_words
    [MulAction.IsPretransitive U X]
    (hpow : ∀ t : F.top.range,t^2=1)
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=BinaryRegularEightNaturalRegistry.H)
    (hK : E.kernelSpace=(BinaryRegularEightNaturalRegistry.charts 23).2.space) :
    ∃ u : Fin 4 → F.top.range,
      (∀ i,E.originalCoordinateRepresentation (u i)=BinaryElementary16GraphHeadRigidity.action i) ∧
      Function.Bijective (BinaryElementary32CoordinateRows.word u) := by
  obtain ⟨u,hu⟩ := F.exists_original_elementary_coordinate_rows E hzero hH hK
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 16) :=
    BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mpr hpow
  have hc : Nat.card F.top.range=16 := by
    simpa only [Nat.card_fin] using ElementaryBinaryTransitiveNormalRank.card_eq_degree hel (0 : Fin 16)
  exact ⟨u,hu,BinaryElementary32CoordinateRows.word_bijective
    E.originalCoordinateRepresentation u hu hc⟩

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
