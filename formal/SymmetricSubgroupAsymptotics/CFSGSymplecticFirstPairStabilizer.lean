import SymmetricSubgroupAsymptotics.CFSGSymplecticTailRoots

/-! Restricting the original elementary hyperbolic-pair stabilizer is a
faithful homomorphism. Its range contains every original elementary root
on the smaller space. This is the concrete induction step, independent
of any symplectic order formula. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices
variable (K : Type) [Field K]

def pairStabilizerUnits (r : ℕ) : Subgroup ((Mat K (r + 1))ˣ) where
  carrier := {u | FixesFirstPair r (u : Mat K (r + 1))}
  one_mem' := by constructor <;> exact Matrix.one_mulVec _
  mul_mem' := by
    intro u v hu hv
    constructor
    · change ((u : Mat K (r + 1)) * (v : Mat K (r + 1))) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, hv.1, hu.1]
    · change ((u : Mat K (r + 1)) * (v : Mat K (r + 1))) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, hv.2, hu.2]
  inv_mem' := by
    intro u hu
    exact fixesFirstPair_inv r u hu

def firstPairElementary (r : ℕ) : Subgroup ((Mat K (r + 1))ˣ) :=
  elementaryRootGroup K (r + 1) ⊓ pairStabilizerUnits K r

def firstPairTailHom (r : ℕ) : firstPairElementary K r →* (Mat K r)ˣ where
  toFun u := tailUnits r u.val u.property.2
  map_one' := by apply Units.ext; exact tailMatrix_one r
  map_mul' u v := by
    apply Units.ext
    exact tailMatrix_mul r _ _ u.property.2

theorem firstPairTailHom_injective (r : ℕ) :
    Function.Injective (firstPairTailHom K r) := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  have hu : PreservesPairing (r + 1) (u.val : Mat K (r + 1)) :=
    preservesPairing_of_form (r + 1) _
      (elementaryRootGroup_le_formPreserving K (r + 1) u.property.1)
  have hv : PreservesPairing (r + 1) (v.val : Mat K (r + 1)) :=
    preservesPairing_of_form (r + 1) _
      (elementaryRootGroup_le_formPreserving K (r + 1) v.property.1)
  exact eq_of_same_tail r _ _ hu hv u.property.2 v.property.2
    (congrArg (fun w : (Mat K r)ˣ => (w : Mat K r)) h)

theorem elementaryRootGroup_le_firstPairTail_range (r : ℕ) :
    elementaryRootGroup K r ≤ (firstPairTailHom K r).range := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, i, t, rfl⟩
  refine ⟨⟨rootTransvection K (r + 1) neg i.succ t,
    rootTransvection_mem K (r + 1) neg i.succ t,
    rootTransvection_fixesFirstPair r neg i t⟩, ?_⟩
  apply Units.ext
  exact tailMatrix_rootTransvection r neg i t

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
