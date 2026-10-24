import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedPairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCommutatorParameter
import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingIndex

/-! The actual diagram-fixed middle radical is a scalar central extension
with four vector coordinates when three is nonzero in the field. All
projection, highest-root and commutator identities retain the same raw
D4 realization; no abstract Heisenberg recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralExtensionData

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateAllRootParameters
open CFSGGTwoD4GeckHighestDiagramFixed CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
open CFSGGTwoD4GeckMiddleFixedCoordinates CFSGGTwoD4GeckMiddleFixedPairing
open CFSGTrialityGeckMiddleCommutatorParameter
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def central (K : Type) [Field K] : Multiplicative K →* fixedMiddle K :=
  (selectedRootHom A hd hs hp ho K (longRoot 2)).codRestrict (fixedMiddle K) (fun t => by
    have hhigh : selectedRootElement A hd hs hp ho K (longRoot 2) t.toAdd ∈ highestLine K :=
      (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) _).mpr ⟨t.toAdd,rfl⟩
    exact ⟨highest_le_middle K hhigh,highest_selected_fixed K t.toAdd⟩)

theorem central_val (K : Type) [Field K] (t : Multiplicative K) :
    (central K t).val = selectedRootElement A hd hs hp ho K (longRoot 2) t.toAdd := rfl

theorem central_injective (K : Type) [Field K] : Function.Injective (central K) := by
  intro s t he
  exact selected_rootHom_injective A hd hs hp ho K (longRoot 2) (congrArg Subtype.val he)

theorem central_range (K : Type) [Field K] [Finite K] : (central K).range = (projection K).ker := by
  ext u
  constructor
  · rintro ⟨t,rfl⟩
    exact (mem_projection_kernel_iff K _).mpr
      ((mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) _).mpr ⟨t.toAdd,rfl⟩)
  · intro hu
    obtain ⟨t,ht⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) u.val).mp
      ((mem_projection_kernel_iff K u).mp hu)
    exact ⟨Multiplicative.ofAdd t,Subtype.ext ht⟩

theorem central_commutator (K : Type) [Field K] [Finite K] (u v : fixedMiddle K) :
    u*v*u⁻¹*v⁻¹ = central K (Multiplicative.ofAdd (pairing K (coordinate K u) (coordinate K v))) := by
  apply Subtype.ext
  exact (middle_pairing_commutator K ⟨u.val,u.property.1⟩ ⟨v.val,v.property.1⟩
    (fixedCubeEmbedding K (coordinate K u)) (fixedCubeEmbedding K (coordinate K v))
    (coordinate_spec K u).symm (coordinate_spec K v).symm).symm

def extensionData (K : Type) [Field K] [Finite K] (hthree : (3 : K) ≠ 0) :
    CentralExtensionScalarPairingIndex.Data (F := K) (V := Fin 4 → K) (N := fixedMiddle K) where
  projection := projection K
  central := central K
  central_injective := central_injective K
  central_range := central_range K
  projection_surjective := projection_surjective K hthree
  pairing := pairing K
  alternating := pairing_alternating K
  full := pairing_full K hthree
  commutator := central_commutator K

theorem fixedMiddle_card (K : Type) [Field K] [Finite K] (hthree : (3 : K) ≠ 0) :
    Nat.card (fixedMiddle K) = Nat.card K^5 :=
  (extensionData K hthree).card_eq 2 (by simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin])

theorem central_proper_index (K : Type) [Field K] [Finite K] (hthree : (3 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p] (L : Subgroup (fixedMiddle K))
    (hL : ¬(central K).range ≤ L) : p*Nat.card K^2 ≤ L.index :=
  (extensionData K hthree).index_least p 2
    (by simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]) L hL

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralExtensionData
