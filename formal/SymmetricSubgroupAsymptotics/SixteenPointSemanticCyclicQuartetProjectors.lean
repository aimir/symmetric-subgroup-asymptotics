import SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetSource
import SymmetricSubgroupAsymptotics.FunctionBlockOrbitProjectionIrreducibility

/-! Cyclic quartet sources using actual three-term coordinate projectors.
This includes correlated odd local images: no independent local Singer
subgroups are required. The finite equations concern the literal action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetProjectors
open BinaryPlaneWreathIrreducible BinaryPlaneWreathNormalGenerators
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
variable {R : Type} [Group R] [Finite R] [IsCyclic R]
  [MulAction R (Fin 4)] [FaithfulSMul R (Fin 4)]
  (K : Subgroup (BinaryPlaneWreathNormalGenerators.Model (R := R) (I := Fin 4)))

/-- Three explicit terms isolate each binary plane, even when the odd
local factors are correlated across the four planes. -/
theorem irreducible
    (hlocal : ∀ (i : Fin 4) (u v : V), u ≠ 1 → v ≠ 1 →
      ∃ g : actualImage K, restrictedAction (actualImage K) g (Pi.mulSingle i u) =
        Pi.mulSingle i v)
    (htrans : ∀ i j : Fin 4, ∃ g : actualImage K,
      (g : W (R := R) (I := Fin 4)).right • i = j)
    (s : Fin 4 → actualImage K)
    (hprojection : ∀ i v, v * restrictedAction (actualImage K) (s i) v *
      restrictedAction (actualImage K) ((s i)^2) v = Pi.mulSingle i (v i)) :
    IrreducibleAbelianSemidirect.Irreducible (restrictedAction (actualImage K)) := by
  apply functionBlock_irreducible_of_three_term_projection_and_local_orbits
    (restrictedAction (actualImage K)) hlocal ?_ s hprojection
  intro i j
  obtain ⟨g,hg⟩ := htrans i j
  refine ⟨g,localAction ((g : W (R := R) (I := Fin 4)).left j),?_⟩
  intro v
  change action (g : W (R := R) (I := Fin 4)) (Pi.mulSingle i v) = _
  rw [action_single,hg]

theorem socle_of_surjective {Q : Type} [Group Q]
    (hirr : IrreducibleAbelianSemidirect.Irreducible
      (restrictedAction (actualImage K)))
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := Fin 4) →* R).comp
        (actualImage K).subtype))
    (c : R) (i : Fin 4) (hcycle : ∀ j : Fin 4, ∃ n : ℕ, c^n • i = j)
    (hR : Nat.Coprime 3 (Nat.card R))
    (π : K →* Q) (hπ : Function.Surjective π) : SocleNormalGeneratorBound Q 2 := by
  apply IrreducibleAbelianSemidirectSubgroup.socle_of_surjective_of_image_quotients
    BinaryPlaneWreathIrreducible.action K
    (BinaryPlaneWreathIrreducible.action_injective.comp Subtype.val_injective)
    hirr
    (by decide : 1 ≤ 2) ?_ π hπ
  intro N hN
  letI := hN
  let f := (wreathMap (R := R) (I := Fin 4)).comp (actualImage K).subtype
  let J := f.range
  let e : actualImage K ≃* J := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => (wreathMap_injective.comp Subtype.val_injective)
      (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
  have hb : Function.Surjective
      ((PermutationalWreathProduct.rightHom :
        TernaryPermutationWreathEmbedding.W (R := R) (I := Fin 4) →* R).comp J.subtype) := by
    intro r
    obtain ⟨g,hg⟩ := hsurj r
    exact ⟨f.rangeRestrict g,hg⟩
  exact TernaryPermutationWreathCyclicQuotientSocles.socle_of_surjective J hb c i hcycle hR
    ((QuotientGroup.mk' N).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective N).comp e.symm.surjective)

/-- Complete original-weight source from the actual image irreducibility.
All quotient denominators remain the supplied original normal axes. -/
def source
    (hirr : IrreducibleAbelianSemidirect.Irreducible
      (restrictedAction (actualImage K)))
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := Fin 4) →* R).comp
        (actualImage K).subtype))
    (c : R) (hcycle : ∀ j : Fin 4, ∃ n : ℕ, c^n • (0 : Fin 4) = j)
    (hR : Nat.Coprime 3 (Nat.card R))
    (i : PreE7NonPairActionClass 16)
    (pi : K →* preE7NonPairAction 16 i) (hpi : Function.Surjective pi)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7RankTailSourceOrYonedaTopData 16 i := by
  let row : DegreeTwoDegreeSixteenImportedRow i :=
    PreE7FiniteMixedPermutationMenu.censusFreeImportedRow hMN i (by decide : 2 ≤ 2)
      (fun N => by
        letI := N.2
        exact socle_of_surjective K hirr hsurj c 0 hcycle hR
          ((QuotientGroup.mk' N.1).comp pi)
          ((QuotientGroup.mk'_surjective N.1).comp hpi)) hZmud
  exact row.source

end SymmetricSubgroupAsymptotics.SixteenPointSemanticCyclicQuartetProjectors
end
