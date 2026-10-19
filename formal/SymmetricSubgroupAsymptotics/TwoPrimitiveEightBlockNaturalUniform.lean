import SymmetricSubgroupAsymptotics.TwoBlockSylowSevenLocalImages
import SymmetricSubgroupAsymptotics.TwoEightPrimeSevenNaturalDualUniform
import SymmetricSubgroupAsymptotics.PrimitiveEightSylowSevenOrder
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding

/-! The actual Sylow seven of a two-block action supplies the four-orbit
restriction for its entire binary natural module. Both local images are
proved Sylow images of the same original subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
local instance twoPrimitiveEightNaturalPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {G X : Type} [Group G] [Finite G] [MulAction G X]
  [MulAction.IsPretransitive G X] [FaithfulSMul G X] [Fintype X]
  {x : X} (D : OriginalMinimalBlock (A := G) x)

/-- No classification of two-block extensions or final capacity premise is
used: the bare eight-point component classification supplies the prime. -/
theorem twoPrimitiveEight_natural_uniform_four
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hf : Nat.card D.Fibre = 8) (hi : Nat.card D.Points = 2) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G X) 4 := by
  letI : MulAction.IsPretransitive G D.Points := inferInstance
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  let rho := ActualBlockWreathEmbedding.embedding D.map D.map_equivariant D.base
  have hfull : PermutationalWreathProduct.Compression.FullComponent rho :=
    ActualBlockWreathEmbedding.fullComponent D.map D.map_equivariant D.base
  let P : Sylow 7 G := Classical.choice inferInstance
  have hPcard : (Nat.card P : ZMod 2) ≠ 0 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n (by decide : (7 : ZMod 2) ≠ 0)
  letI : NeZero (Nat.card P : ZMod 2) := ⟨hPcard⟩
  let eI : D.Points ≃ Fin 2 := Finite.equivFinOfCardEq hi
  let eF : D.Fibre ≃ Fin 8 := Finite.equivFinOfCardEq hf
  let L := ActualBlockWreathEmbedding.productEquiv D.map D.map_equivariant D.base
  let points : X ≃ Fin 2 × Fin 8 :=
    (L.symm.trans (Equiv.prodComm _ _)).trans (Equiv.prodCongr eI eF)
  let phi : D.Component →* Equiv.Perm (Fin 8) :=
    eF.permCongrHom.toMonoidHom.comp D.Component.subtype
  have hphi : Function.Injective phi :=
    eF.permCongrHom.injective.comp Subtype.val_injective
  let operators : Fin 2 → P →* Equiv.Perm (Fin 8) := fun i =>
    phi.comp (TwoBlockSylowSevenLocalImages.localMap rho hi P (eI.symm i))
  have hlocal : ∀ i, Nat.card (operators i).range = 7 := by
    intro i
    have hfactor := primitiveEight_seven_factorization published D.Component hf
    have hh := TwoBlockSylowSevenLocalImages.local_range_card rho hfull hi P
      hfactor (eI.symm i)
    dsimp only [operators]
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hphi]
    exact hh
  apply twoEight_primeSeven_natural_uniform_four (P : Subgroup G).subtype
    points operators hlocal
  intro p z
  let y := L.symm z
  have hfix := TwoBlockSylowSevenLocalImages.fixes_blocks rho hi P p y.2
  have hmove : L.symm (p.val • z) = ((rho p.val).left y.2 • y.1, y.2) := by
    have hh := congrArg L.symm
      (ActualBlockWreathEmbedding.productEquiv_equivariant
        D.map D.map_equivariant D.base p.val y)
    change L.symm (L (rho p.val • y)) = L.symm (p.val • L y) at hh
    simp only [Equiv.symm_apply_apply] at hh
    have hy : L y = z := L.apply_symm_apply z
    rw [hy] at hh
    change ((rho p.val).left ((rho p.val).right • y.2) • y.1,
      (rho p.val).right • y.2) = L.symm (p.val • z) at hh
    rw [hfix] at hh
    exact hh.symm
  change (eI (L.symm (p.val • z)).2, eF (L.symm (p.val • z)).1) = _
  rw [hmove]
  change (eI y.2, eF ((rho p.val).left y.2 • y.1)) =
    (eI y.2, operators (eI y.2) p (eF y.1))
  apply Prod.ext
  · rfl
  · simp only [operators, MonoidHom.comp_apply, Equiv.symm_apply_apply,
      TwoBlockSylowSevenLocalImages.local_apply]
    simp [phi, Equiv.permCongr_apply]
    rfl

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
