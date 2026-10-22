import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenter
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalAllRootLines
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLeadingAxes
import Mathlib.GroupTheory.Commutator.Basic

/-! Actual simple-root coordinates on the ORIGINAL positive subgroup.
The map is transported through the proved literal U equivalence, and
its kernel is exactly that original group's derived subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingHom
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateDerivedFirstLayer CFSGNormTwoCoordinateRootLeadingAxes
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

private theorem commutator_map_equiv {G Q : Type*} [Group G] [Group Q] (e : G≃*Q) :
    (commutator G).map e.toMonoidHom=commutator Q := by
  rw [map_commutator_eq G e.toMonoidHom,MonoidHom.range_eq_top.mpr e.surjective]
  rfl

def originalLeadingHom (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    originalPositive A hd hs hp ho K i→*Multiplicative (Fin r→K) :=
  (leadingHom A hd hs hp ho K).comp (originalPositiveEquiv A hd hs hp ho K p i).symm.toMonoidHom

theorem originalLeadingHom_equiv_apply (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (u : PositiveGroup A hd hs hp ho K) :
    originalLeadingHom A hd hs hp ho K p i ((originalPositiveEquiv A hd hs hp ho K p i) u)=
      leadingHom A hd hs hp ho K u := by
  change leadingHom A hd hs hp ho K
    ((originalPositiveEquiv A hd hs hp ho K p i).symm
      ((originalPositiveEquiv A hd hs hp ho K p i) u))=_
  rw [MulEquiv.symm_apply_apply]

theorem originalLeadingHom_kernel (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (originalLeadingHom A hd hs hp ho K p i).ker=commutator (originalPositive A hd hs hp ho K i) := by
  calc
    _=(leadingHom A hd hs hp ho K).ker.map
        (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom :=
      MonoidHom.ker_comp_mulEquiv (leadingHom A hd hs hp ho K)
        (originalPositiveEquiv A hd hs hp ho K p i).symm
    _=(commutator (PositiveGroup A hd hs hp ho K)).map
        (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom := by
      rw [leading_kernel_eq_derived A hd hs hp ho K]
    _=_ := commutator_map_equiv (originalPositiveEquiv A hd hs hp ho K p i)

theorem original_positive_root_piece_eq_map (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (k : Roots A)
    (hk : ∀j,0≤k.val j) :
    (originalFullRootLine A hd hs hp ho K i k).subgroupOf (originalPositive A hd hs hp ho K i)=
      ((rootSubgroup A hd hs hp ho K k).subgroupOf (PositiveGroup A hd hs hp ho K)).map
        (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom := by
  have hle : originalFullRootLine A hd hs hp ho K i k≤originalPositive A hd hs hp ho K i := by
    rw [originalFullRootLine_eq_positive A hd hs hp ho K i k hk]
    rintro x ⟨u,hu,he⟩
    exact ⟨u,he⟩
  apply Subgroup.map_injective (originalPositive A hd hs hp ho K i).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hle,Subgroup.map_map]
  have hcomp : (originalPositive A hd hs hp ho K i).subtype.comp
      (originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom=
        (originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K) := rfl
  rw [hcomp]
  exact originalFullRootLine_eq_positive A hd hs hp ho K i k hk

theorem original_root_leading_image (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (k : Roots A)
    (hk : ∀j,0≤k.val j) :
    ((originalFullRootLine A hd hs hp ho K i k).subgroupOf (originalPositive A hd hs hp ho K i)).map
        (originalLeadingHom A hd hs hp ho K p i)=
      ((rootSubgroup A hd hs hp ho K k).subgroupOf (PositiveGroup A hd hs hp ho K)).map
        (leadingHom A hd hs hp ho K) := by
  rw [original_positive_root_piece_eq_map A hd hs hp ho K p i k hk,Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro u
  exact originalLeadingHom_equiv_apply A hd hs hp ho K p i u

theorem original_nonsimple_root_piece_le_derived (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (k : Roots A)
    (hk : ∀j,0≤k.val j) (hns : ∀j : Fin r,k≠(s₀ j : Roots A)) :
    (originalFullRootLine A hd hs hp ho K i k).subgroupOf (originalPositive A hd hs hp ho K i)≤
      commutator (originalPositive A hd hs hp ho K i) := by
  rw [original_positive_root_piece_eq_map A hd hs hp ho K p i k hk]
  have hh := Subgroup.map_mono (f:=(originalPositiveEquiv A hd hs hp ho K p i).toMonoidHom)
    (nonsimple_root_subgroup_le_derived A hd hs hp ho K k hns)
  exact hh.trans_eq (commutator_map_equiv (originalPositiveEquiv A hd hs hp ho K p i))

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalLeadingHom
