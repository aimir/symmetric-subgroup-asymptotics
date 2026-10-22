import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOpposedGraphShear

/-! A literal dilation of only the negative coordinates, and its exact
zero-middle decomposition in the original B vector space. It is not
asserted to be an isometry for an arbitrary parameter. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBNegativeDilation
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBVectorCoordinates
variable (K : Type) [Field K]

def map (n : ℕ) (t : K) : (Index n→K)→ₗ[K](Index n→K) where
  toFun v := Sum.elim (Sum.elim (fun i=>v (pos n i)) (fun i=>t*v (neg n i)))
    (fun _=>v (middle n))
  map_add' v w := by
    funext i
    rcases i with (i|i)|⟨⟩ <;> simp [mul_add]
  map_smul' a v := by
    funext i
    rcases i with (i|i)|⟨⟩ <;> simp [mul_left_comm]

theorem decompose (n : ℕ) (v : Index n→K) (hm : v (middle n)=0) :
    v=positiveEmbedding K n (positivePart K n v)+negativeEmbedding K n (negativePart K n v) := by
  funext i
  rcases i with (i|i)|⟨⟩ <;> simp [positiveEmbedding,negativeEmbedding,positivePart,negativePart,pos,neg,middle,hm]

theorem map_decompose (n : ℕ) (t : K) (v : Index n→K) (hm : v (middle n)=0) :
    map K n t v=positiveEmbedding K n (positivePart K n v)+t•negativeEmbedding K n (negativePart K n v) := by
  funext i
  rcases i with (i|i)|⟨⟩ <;>
    simp [map,positiveEmbedding,negativeEmbedding,positivePart,negativePart,pos,neg,middle,hm]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBNegativeDilation
