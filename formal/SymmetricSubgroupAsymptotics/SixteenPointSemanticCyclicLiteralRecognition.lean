import SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicWreathSubgroupSource

/-! A single recognition template for literal cyclic-quartet actions.
Only displayed generator coordinates and their original permutation bindings
are needed. No local Singer or coordinate-projector certificates are used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicLiteralRecognition
open BinaryPlaneWreathIrreducible BinaryPlaneWreathLinearModelEquiv
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Blocks := Subgroup.zpowers (finRotate 4)
def rotation : Blocks := ⟨finRotate 4,Subgroup.mem_zpowers _⟩
abbrev Model := PointwiseModel (R := Blocks) (I := Fin 4)
abbrev TopModel := W (R := Blocks) (I := Fin 4)
def blockProjection : Model →* Blocks :=
  (PermutationalWreathProduct.rightHom : TopModel →* Blocks).comp
    (SemidirectProduct.rightHom : Model →* TopModel)

variable {m : ℕ} (lifted : Fin m → Model)
abbrev generated := Subgroup.closure (Set.range lifted)

/-- A displayed generator with the cyclic top already certifies the full
actual block image of the generated literal subgroup. -/
theorem blocks_surjective (j : Fin m) (hj : blockProjection (lifted j)=rotation) :
    Function.Surjective (blockProjection.comp (generated lifted).subtype) := by
  let beta := blockProjection.comp (generated lifted).subtype
  have hr : rotation ∈ beta.range := by
    refine ⟨⟨lifted j,Subgroup.subset_closure (Set.mem_range_self j)⟩,?_⟩
    exact hj
  intro r
  obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
  have he : rotation^z=r := Subtype.ext hz
  rw [← he]
  exact beta.range.zpow_mem hr z

theorem blocks_binary : IsPGroup 2 Blocks := by
  have hdiv : Nat.card Blocks∣2^2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by decide +kernel : (finRotate 4)^4=1)
  obtain ⟨n,_,hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  exact IsPGroup.of_card hn

theorem blocks_cycle (i : Fin 4) : ∃ n : ℕ, rotation^n • (0 : Fin 4)=i :=
  ⟨i.val,(by decide +kernel : ∀ i : Fin 4, ((finRotate 4)^i.val) 0=i) i⟩

/-- Literal clients retain their own original surjection and semantic index.
Recognition consists of one cyclic-top equation and the actual nonbinary
witness; all arbitrary retained normal denominators are handled upstream. -/
def source (j : Fin m) (hj : blockProjection (lifted j)=rotation)
    (hK : ¬ IsPGroup 2 (generated lifted))
    (i : PreE7NonPairActionClass 16)
    (phi : generated lifted →* preE7NonPairAction 16 i)
    (hphi : Function.Surjective phi)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 i :=
  SixteenPointSemanticCyclicWreathSubgroupSource.source (generated lifted) hK
    (blocks_surjective lifted j hj) rotation 0 blocks_cycle blocks_binary
    i phi hphi hMN hZmud

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicLiteralRecognition
