import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSubgroupClassifier
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCentralPlane
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitFixed

/-! A genuinely small moved orbit is fixed pointwise by the exchanged
short central element. Normality of the actual horizontal plane upgrades
its inclusion in one stabilizer to fixedness on the entire source orbit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSmallOrbit
open CFSGGTwoCharacteristicThreeMiddleSource
open CFSGGTwoCharacteristicThreeMiddleCentralJoin
open CFSGGTwoCharacteristicThreeMiddleLayerCounts
open CFSGGTwoCharacteristicThreeMiddleSubgroupClassifier
open CFSGGTwoCharacteristicThreeMiddleCentralPlane
open CFSGGTwoOriginalPositiveRootWords
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local instance : Finite (source K) := source_finite K

theorem plane_le_of_index_lt (hcard : Nat.card K = 3)
    (M : Subgroup (source K)) (hM : highestElement K ∉ M) (hm : M.index < 54) :
    plane K ≤ M := by
  intro z hz
  change z.val ∈ planeModel K at hz
  obtain ⟨a,ha,he⟩ := hz
  have hC : a ∈ centralLayer K M := by
    change a.toAdd ∈ (centralLayer K M).toAddSubgroup'
    rw [central_layer_horizontal_of_index_lt K hcard M hM hm]
    exact ha
  have haM : sourceCentralHom K a ∈ M := hC
  have hs : sourceCentralHom K a = z := by
    apply Subtype.ext
    exact he
  rw [hs] at haM
  exact haM

def thirdElement : source K :=
  ⟨positiveModel K 3 1,planeModel_le_source K (third_root_mem_planeModel K 1)⟩

theorem thirdElement_val : (thirdElement K).val = positiveModel K 3 1 := rfl

theorem thirdElement_mem_plane : thirdElement K ∈ plane K := third_root_mem_planeModel K 1

theorem source_orbit_card_ge_twentySeven (hcard : Nat.card K = 3)
    {X : Type*} [Finite X] [MulAction (source K) X]
    (x : X) (hx : highestElement K • x ≠ x) :
    27 ≤ (MulAction.orbit (source K) x).ncard := by
  have he := source_index_ge_twentySeven K hcard (MulAction.stabilizer (source K) x) hx
  rw [MulAction.index_stabilizer] at he
  exact he

theorem third_fixes_small_source_orbit (hcard : Nat.card K = 3)
    {X : Type*} [Finite X] [MulAction (source K) X]
    (x : X) (hx : highestElement K • x ≠ x)
    (hm : (MulAction.orbit (source K) x).ncard < 54) :
    ∀ y ∈ MulAction.orbit (source K) x, thirdElement K • y = y := by
  letI := plane_normal K
  have hi : (MulAction.stabilizer (source K) x).index < 54 := by
    rw [MulAction.index_stabilizer]
    exact hm
  have hM := plane_le_of_index_lt K hcard (MulAction.stabilizer (source K) x) hx hi
  exact NormalSubgroupOrbitFixed.fixes_orbit (plane K) x (fun n hn => hM hn)
    (thirdElement K) (thirdElement_mem_plane K)

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSmallOrbit
