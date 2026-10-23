import SymmetricSubgroupAsymptotics.CFSGFFourE6AmbientPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGRegularElementSylowIntersection
import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Actual good Sylow data for the literal folded F4 matrix subgroup.
The regular folded word puts its intersection with the ambient E6 Sylow
inside a unique ambient Sylow, giving a soluble normalizer. The two
displayed signed folded p-subgroups generate the actual matrix group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6GoodSylow
open CFSGFFourSerreMatrices CFSGFFourE6RootSubgroups CFSGFFourE6RegularPositive
open CFSGFFourE6AmbientPositiveSylow CFSGSerreQuadraticMatrix
open CFSGRegularElementSylowIntersection

abbrev FoldedInAmbient (K : Type) [Field K] :=
  (canonicalElementaryGroup realizationData K).subgroupOf (AmbientGroup K)

def rootPart (K : Type) [Field K] (neg : Bool) : Subgroup (FoldedInAmbient K) :=
  ((foldedRootGroup K neg).subgroupOf (AmbientGroup K)).subgroupOf (FoldedInAmbient K)

theorem rootPart_sup (K : Type) [Field K] : rootPart K false⊔rootPart K true=⊤ := by
  have hle (neg : Bool) : (foldedRootGroup K neg).subgroupOf (AmbientGroup K)≤FoldedInAmbient K :=
    Subgroup.subgroupOf_mono _ (foldedRootGroup_le_model K neg)
  have he : (foldedRootGroup K false).subgroupOf (AmbientGroup K)⊔
      (foldedRootGroup K true).subgroupOf (AmbientGroup K)=FoldedInAmbient K := by
    rw [←Subgroup.subgroupOf_sup
      ((foldedRootGroup_le_model K false).trans (foldedModel_le_ambient K))
      ((foldedRootGroup_le_model K true).trans (foldedModel_le_ambient K)),foldedRootGroup_sup]
  rw [rootPart,rootPart,←Subgroup.subgroupOf_sup (hle false) (hle true),he]
  exact Subgroup.subgroupOf_self _

theorem rootPart_isPGroup (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (neg : Bool) : IsPGroup p (rootPart K neg) := by
  let f : rootPart K neg→*foldedRootGroup K neg :=
    { toFun := fun x=>⟨x.val.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _=>rfl }
  apply (foldedRootGroup_isPGroup K p neg).of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : foldedRootGroup K neg=>z.val) h

theorem foldedInAmbient_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    CFSGReduction.GoodSylowPrime (FoldedInAmbient K) p := by
  let P := ambientSylow K p
  let R := FoldedInAmbient K
  let r := regularAmbient K
  have hrP : r∈(P : Subgroup (AmbientGroup K)) := regularAmbient_positive K
  have hrR : r∈R := foldedRegular_mem K
  have hreg : ∀g : AmbientGroup K,g⁻¹*r*g∈(P : Subgroup (AmbientGroup K))→
      g∈Subgroup.normalizer (P : Set (AmbientGroup K)) :=
    regularAmbient_unique K
  letI : IsSolvable (Subgroup.normalizer (P : Set (AmbientGroup K))) :=
    ambient_normalizer_soluble K
  let Q := intersectionSylow P R r hrP hrR hreg
  have hQ : IsSolvable (Subgroup.normalizer (Q : Set R)) :=
    normalizer_intersection_soluble P R r hrP hrR hreg
  exact CFSGReduction.goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    (rootPart K false) (rootPart K true) (rootPart_isPGroup K p false)
    (rootPart_isPGroup K p true) (rootPart_sup K) ⟨Q,hQ⟩

theorem folded_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    CFSGReduction.GoodSylowPrime (canonicalElementaryGroup realizationData K) p := by
  let e := Subgroup.subgroupOfEquivOfLe (foldedModel_le_ambient K)
  exact CFSGReduction.goodSylowPrime_surjective e.toMonoidHom e.surjective
    (foldedInAmbient_goodSylowPrime K p)

end SymmetricSubgroupAsymptotics.CFSGFFourE6GoodSylow
