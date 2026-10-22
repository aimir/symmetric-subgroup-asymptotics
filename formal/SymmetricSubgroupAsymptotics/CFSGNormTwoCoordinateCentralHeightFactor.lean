import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCenterHeightLeading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootCentral
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRoot
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! A central actual h-tail element factors by a central dominant-root
factor and an actual next-tail remainder. All other height parameters
are eliminated by the proved original unit brackets. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCentralHeightFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerFactorization CFSGNormTwoCoordinateCenterHeightLeading
open CFSGNormTwoCoordinateDominantRootUnique CFSGNormTwoCoordinateHighestRoot
open CFSGNormTwoCoordinateHighestRootCentral CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGFiniteQuotientFamilyProduct
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem central_height_parameters_vanish_off_dominant (K : Type) [Field K]
    (θ : Roots A) (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (h : ℤ) (hh : 0<h) (u : PositiveGroup A hd hs hp ho K)
    (hu : u∈heightTailInPositive A hd hs hp ho K h) (hz : u∈Subgroup.center _)
    (c : ExactHeightRoot A h→K) (y : PositiveGroup A hd hs hp ho K)
    (hy : y∈heightTailInPositive A hd hs hp ho K (h+1))
    (he : u=exactHeightWord A hd hs hp ho K h c*y) :
    ∀k : ExactHeightRoot A h,k.val.val≠θ→c k=0 := by
  classical
  intro k hk
  have hndom : ¬∀i,0 ≤ integerPairing A k.val.val.val (Pi.single i (1:ℤ) : Fin r→ℤ) := by
    intro hd'
    exact hk (dominant_positive_root_unique A hd hs hp ho k.val.val θ
      k.val.property hθ hd' hdom)
  obtain ⟨i,hi⟩ := not_forall.mp hndom
  have hpair := negative_simple_pairing_eq_neg_one A hd hs hp ho k.val.val k.val.property i
    (lt_of_not_ge hi)
  have hc := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz)
    (positiveRoot A hd hs hp ho K i 1)).symm
  exact raisable_height_coordinate_zero A hd hs hp ho K h hh u c y hy he hu i hc k hpair

theorem central_height_factor (K : Type) [Field K]
    (θ : Roots A) (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (h : ℤ) (hh : 0<h) (u : PositiveGroup A hd hs hp ho K)
    (hu : u∈heightTailInPositive A hd hs hp ho K h) (hz : u∈Subgroup.center _) :
    ∃t∈(rootSubgroup A hd hs hp ho K θ).subgroupOf (PositiveGroup A hd hs hp ho K),
      t∈Subgroup.center (PositiveGroup A hd hs hp ho K) ∧
      ∃y∈heightTailInPositive A hd hs hp ho K (h+1),u=t*y := by
  classical
  obtain ⟨c,y,hy,he⟩ := heightTailInPositive_factor A hd hs hp ho K h hh u hu
  have hc := central_height_parameters_vanish_off_dominant A hd hs hp ho K θ hθ hdom
    h hh u hu hz c y hy he
  let T := (rootSubgroup A hd hs hp ho K θ).subgroupOf (PositiveGroup A hd hs hp ho K)
  have ht : exactHeightWord A hd hs hp ho K h c∈T := by
    change orderedFamilyProduct (fun k : ExactHeightRoot A h=>
      positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property (Multiplicative.ofAdd (c k)))∈T
    unfold orderedFamilyProduct
    apply T.list_prod_mem
    intro x hx
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
    change selectedRootElement A hd hs hp ho K k.val.val (c k)∈rootSubgroup A hd hs hp ho K θ
    by_cases heq : k.val.val=θ
    · rw [heq]
      exact (mem_rootSubgroup_iff_selected A hd hs hp ho K θ _).mpr ⟨c k,rfl⟩
    · rw [hc k heq,selectedRootElement_zero]
      exact (rootSubgroup A hd hs hp ho K θ).one_mem
  exact ⟨exactHeightWord A hd hs hp ho K h c,ht,
    dominant_root_subgroup_le_center A hd hs hp ho K θ hθ hdom ht,y,hy,he⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCentralHeightFactor
