import SymmetricSubgroupAsymptotics.CFSGFFourE6RegularPositive
import SymmetricSubgroupAsymptotics.CFSGFFourE6RootSubgroups
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerSoluble
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularPositiveUniqueness
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity

/-! The ambient E6 Sylow and its soluble normalizer, together with the
actual folded regular element. Every ambient conjugate Sylow containing
this element is the displayed positive Sylow. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6AmbientPositiveSylow
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits
open CFSGFFourE6RegularPositive CFSGFFourE6RootSubgroups
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormalizerWordIdentity CFSGSignedCartanReflections
open CFSGSerreQuadraticMatrix CFSGNormTwoCoordinatePositiveSylow
open CFSGNormTwoCoordinateNormalizerSoluble CFSGExceptionalDiagramAutomorphisms

abbrev AmbientGroup (K : Type) [Field K] := canonicalElementaryGroup e6Data K
abbrev AmbientPositive (K : Type) [Field K] := (E6Positive K).subgroupOf (AmbientGroup K)

theorem positive_le_ambient (K : Type) [Field K] : E6Positive K≤AmbientGroup K := by
  change E6Positive K≤canonicalElementaryGroup
    (CFSGNormTwoGeckIntegralRealization.realizationData CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index) K
  rw [←CFSGNormTwoGeckPositivePGroup.positive_sup_negative CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K]
  exact le_sup_left

def ambientSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (AmbientGroup K) :=
  canonicalPositiveSylow CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K E6Signs E6_signs_square
    E6_signs_cartan (E6_normalizer_word_identity K) p

theorem ambientSylow_coe (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (ambientSylow K p : Subgroup (AmbientGroup K))=AmbientPositive K := rfl

theorem ambient_normalizer_soluble (K : Type) [Field K] :
    IsSolvable (Subgroup.normalizer (AmbientPositive K : Set (AmbientGroup K))) := by
  let N : Subgroup ((Matrix Index Index K)ˣ) :=
    Subgroup.normalizer (E6Positive K : Set _)⊓AmbientGroup K
  letI : IsSolvable (diagramGroup CartanMatrix.E₆) := E6_diagram_soluble
  letI : IsSolvable N := normalizer_inter_model_soluble CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K E6Signs E6_signs_square E6_signs_cartan
  have hm : (AmbientPositive K).map (AmbientGroup K).subtype=E6Positive K := by
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left (positive_le_ambient K)]
  have hn : (Subgroup.normalizer (AmbientPositive K : Set (AmbientGroup K))).map
      (AmbientGroup K).subtype≤N := by
    intro g hg
    have hu := (AmbientPositive K).le_normalizer_map (AmbientGroup K).subtype hg
    rw [hm] at hu
    obtain ⟨x,hx,rfl⟩ := hg
    exact ⟨hu,x.property⟩
  let f : Subgroup.normalizer (AmbientPositive K : Set (AmbientGroup K))→*N :=
    { toFun := fun x=>⟨x.val.val,hn ⟨x.val,x.property,rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _=>rfl }
  apply solvable_of_solvable_injective (f:=f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : N=>z.val) h

def regularAmbient (K : Type) [Field K] : AmbientGroup K :=
  ⟨foldedRegular K,foldedModel_le_ambient K (foldedRegular_mem K)⟩

theorem regularAmbient_positive (K : Type) [Field K] : regularAmbient K∈AmbientPositive K := by
  change foldedRegular K∈E6Positive K
  rw [←regularPositive_val]
  exact (regularPositive K).property

theorem regularAmbient_unique (K : Type) [Field K] [Finite K] (g : AmbientGroup K)
    (hg : g⁻¹*regularAmbient K*g∈AmbientPositive K) :
    g∈Subgroup.normalizer (AmbientPositive K : Set (AmbientGroup K)) := by
  have hn := CFSGNormTwoCoordinateRegularPositiveUniqueness.mem_normalizer_of_regular_conjugate
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K g.val (foldedRegular K) g.property
    (regularAmbient_positive K) (foldedRegular_leading_ne_zero K) hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact (Subgroup.mem_normalizer_iff.mp hn x.val)

end SymmetricSubgroupAsymptotics.CFSGFFourE6AmbientPositiveSylow
