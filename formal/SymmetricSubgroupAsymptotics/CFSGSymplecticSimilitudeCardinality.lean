import SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticCardinality

/-! The similitude multiplier splitting is counted on the actual
linear group. Its unit-multiplier fibre is the same elementary symplectic
group already identified by stabilizer induction. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeGroup
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticStabilizerCoordinates
variable {K : Type} [Field K]

def elementaryToIsometries (n : ℕ) : elementaryRootGroup K n →* isometries (K := K) n where
  toFun u := ⟨CFSGProjectiveLinearPointAction.linearEquiv u.val, by
    intro v w
    exact preservesPairing_of_form n (u.val : Mat K n)
      (elementaryRootGroup_le_formPreserving K n u.property) v w⟩
  map_one' := Subtype.ext (map_one CFSGProjectiveLinearPointAction.linearEquiv.toMonoidHom)
  map_mul' u v := Subtype.ext
    (map_mul CFSGProjectiveLinearPointAction.linearEquiv.toMonoidHom u.val v.val)

theorem elementaryToIsometries_bijective (n : ℕ) :
    Function.Bijective (elementaryToIsometries (K := K) n) := by
  constructor
  · intro u v he
    apply Subtype.ext
    apply CFSGProjectiveLinearPointAction.linearEquiv.injective
    exact congrArg Subtype.val he
  · intro e
    let u : (Mat K n)ˣ := CFSGProjectiveLinearPointAction.linearEquiv.symm e.val
    have he : CFSGProjectiveLinearPointAction.linearEquiv u = e.val :=
      CFSGProjectiveLinearPointAction.linearEquiv.apply_symm_apply _
    have hu : PreservesPairing n (u : Mat K n) := by
      intro v w
      change pairing n (CFSGProjectiveLinearPointAction.linearEquiv u v)
        (CFSGProjectiveLinearPointAction.linearEquiv u w) = _
      rw [he]
      exact e.property v w
    refine ⟨⟨u, all_formPreserving_elementary K n u hu⟩, ?_⟩
    exact Subtype.ext he

def elementaryIsometryEquiv (n : ℕ) : elementaryRootGroup K n ≃* isometries (K := K) n :=
  MulEquiv.ofBijective (elementaryToIsometries n) (elementaryToIsometries_bijective n)

theorem isometries_card (n : ℕ) :
    Nat.card (isometries (K := K) n) = Nat.card (elementaryRootGroup K n) :=
  Nat.card_congr (elementaryIsometryEquiv n).symm.toEquiv

theorem similitudes_card (n : ℕ) (hn : 0 < n) :
    Nat.card (similitudes (K := K) n) = Nat.card Kˣ * Nat.card (elementaryRootGroup K n) := by
  rw [Nat.card_congr (decomposeEquiv n hn), Nat.card_prod, isometries_card]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeGroup
