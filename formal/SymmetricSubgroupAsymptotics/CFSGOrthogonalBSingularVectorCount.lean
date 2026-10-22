import SymmetricSubgroupAsymptotics.CFSGParabolicQuadricCount
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularCoordinates

/-! The exact singular-vector count is bound to the SAME original B Gram
matrix. The factor four in its hyperbolic coordinates is retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGParabolicQuadricCount
variable (K : Type) [Field K]

theorem gram_norm_dot (n : ℕ) (v : Index n→K) :
    (gram K n).toBilin' v v =
      dotDual (fun i=>4*positivePart K n v i) (negativePart K n v)+v (middle n)^2 := by
  rw [gram_norm_coordinates]
  apply congrArg (fun a:K=>a+v (middle n)^2)
  change (∑i:Fin n,(positivePart K n v i*2*negativePart K n v i+
      negativePart K n v i*2*positivePart K n v i))=
    ∑i:Fin n,(4*positivePart K n v i)*negativePart K n v i
  apply Finset.sum_congr rfl
  intro i _
  ring

def coordinates (n : ℕ) (h4:(4:K)≠0) :
    (Index n→K) ≃ (Fin n→K) × (K × (Fin n→K)) where
  toFun v := (fun i=>4*positivePart K n v i,v (middle n),negativePart K n v)
  invFun p := Sum.elim (Sum.elim (fun i=>(4:K)⁻¹*p.1 i) p.2.2) (fun _=>p.2.1)
  left_inv v := by
    funext x
    rcases x with (i|i)|⟨⟩
    · change (4:K)⁻¹*(4*v (pos n i))=v (pos n i)
      rw [←mul_assoc,inv_mul_cancel₀ h4,one_mul]
    · rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      change (4:K)*((4:K)⁻¹*p.1 i)=p.1 i
      rw [←mul_assoc,mul_inv_cancel₀ h4,one_mul]
    · rfl

def coordinateQuadricEquiv (n : ℕ) :
    {p:(Fin n→K) × (K × (Fin n→K)) //dotDual p.1 p.2.2+p.2.1^2=0} ≃
      Quadric (K:=K) (I:=Fin n) where
  toFun p := ⟨p.val.1,⟨p.val.2,p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def singularEquiv (n : ℕ) (h4:(4:K)≠0) :
    {v:Index n→K //(gram K n).toBilin' v v=0} ≃ Quadric (K:=K) (I:=Fin n) :=
  (Equiv.subtypeEquiv (coordinates K n h4) (by
    intro v
    change (gram K n).toBilin' v v=0 ↔
      dotDual (fun i=>4*positivePart K n v i) (negativePart K n v)+v (middle n)^2=0
    rw [gram_norm_dot])).trans (coordinateQuadricEquiv K n)

theorem singular_vectors_card [Finite K] (n : ℕ) (h2:(2:K)≠0) :
    Nat.card {v:Index n→K //(gram K n).toBilin' v v=0}=Nat.card K^(2*n) := by
  have h4:(4:K)≠0 := by
    have he:(4:K)=2*2 := by ring
    rw [he]
    exact mul_ne_zero h2 h2
  exact (Nat.card_congr (singularEquiv K n h4)).trans (by
    simpa only [Fintype.card_fin] using quadric_card (K:=K) (I:=Fin n))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
