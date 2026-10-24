import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointTailAction
import SymmetricSubgroupAsymptotics.BinaryQuadraticLiftDualOrbit

/-! Existing actual transvection words discharge the structural input
of the generic dual-orbit theorem. This yields a uniform lower orbit
bound for every normalized actual central character, not a chosen
quadratic-form orbit or an assumed transitivity statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointDualOrbit
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticHeisenbergWords CFSGSymplecticHeisenbergCoordinates
open CFSGSymplecticStabilizerCoordinates CFSGSymplecticHeisenbergVectorAction
open CFSGHeisenbergCoordinateGroup CFSGSymplecticBinaryPointTailAction
open BinaryQuadraticRefinementTransvections
variable (K : Type) [Field K] [CharP K 2]

private theorem vector_pairing (m : ℕ)
    (v w : (Fin m → K) × (Fin m → K)) :
    pairing m (vectorEquiv K m v) (vectorEquiv K m w) = polar v w := by
  have hh := pairing_tailVectors (⟨v.1,v.2,0⟩ : Element K m)
    (⟨w.1,w.2,0⟩ : Element K m)
  change pairing (m+1) (tailExtend m (vectorEquiv K m v))
    (tailExtend m (vectorEquiv K m w)) = dotProduct v.1 w.2-dotProduct v.2 w.1 at hh
  rw [pairing_tailExtend, CharTwo.sub_eq_add] at hh
  rw [hh]
  unfold polar
  rw [dotProduct_comm v.2 w.1]

theorem exists_vector_transvection (s : ℕ) (hs : 0 < s)
    (v : (Fin (s+1) → K) × (Fin (s+1) → K)) :
    ∃ g : elementaryRootGroup K (s+1), ∀ x,
      vectorLinearHom K (s+1) g x = transvectionMap v x := by
  let g := naturalElement K s hs (vectorEquiv K (s+1) v) 1
  refine ⟨g,?_⟩
  intro x
  apply (vectorEquiv K (s+1)).injective
  rw [vectorLinearHom_apply, (vectorEquiv K (s+1)).apply_symm_apply]
  change ((naturalElement K s hs (vectorEquiv K (s+1) v) 1).val : Mat K (s+1)) *ᵥ
    vectorEquiv K (s+1) x = _
  rw [naturalElement_apply, transvection_apply, one_mul, vector_pairing]
  change vectorEquiv K (s+1) x+polar v x • vectorEquiv K (s+1) v =
    vectorEquiv K (s+1) (x+polar v x • v)
  rw [map_add, map_smul]

theorem actual_dual_orbit_card_lower [Finite K] (hK : Nat.card K = 2)
    (s : ℕ) (hs : 0 < s)
    (φ : Module.Dual K (CFSGSymplecticBinaryPointRadical.Coordinates K (s+1)))
    (hφ : φ (0,1) = 1) :
    (Nat.card K^(s+1)-1)*Nat.card K^s ≤
      Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit (pointLinearHom K hK (s+1)) φ) := by
  have h := BinaryQuadraticLiftDualOrbit.dual_orbit_card_lower hK
    (vectorLinearHom K (s+1)) (vectorLinearHom_preserves_polar K (s+1))
    (exists_vector_transvection K s hs) φ hφ
  simpa only [Fintype.card_fin, Nat.add_sub_cancel] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointDualOrbit
