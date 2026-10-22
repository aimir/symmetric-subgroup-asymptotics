import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailGram

/-! The original coordinate tangent cone is one free head coordinate
times the SAME smaller singular cone. The paired negative coordinate is
zero, and the middle coordinate remains in the smaller cone. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBTailCoordinates
variable (K : Type) [Field K]

def cons (n : ℕ) (a : K) (v : Index n → K) : Index (n+1) → K :=
  fun x=>Sum.elim v (fun i:Fin 2=>if i=0 then a else 0) ((tailEquiv n).symm x)

@[simp] theorem cons_head_positive (n : ℕ) (a : K) (v : Index n → K) :
    cons K n a v (pos (n+1) 0)=a := by simp [cons]

@[simp] theorem cons_head_negative (n : ℕ) (a : K) (v : Index n → K) :
    cons K n a v (neg (n+1) 0)=0 := by simp [cons]

@[simp] theorem tail_cons (n : ℕ) (a : K) (v : Index n → K) :
    tailRestriction K n (cons K n a v)=v := by
  funext i
  simp [tailRestriction,cons]

theorem norm_cons (n : ℕ) (a : K) (v : Index n → K) :
    (gram K (n+1)).toBilin' (cons K n a v) (cons K n a v)=(gram K n).toBilin' v v := by
  simpa only [tail_cons] using gram_norm_tail_of_negative_head_zero K n
    (cons K n a v) (cons_head_negative K n a v)

def coordinateTangentEquiv (n : ℕ) :
    {v:Index (n+1) → K //(gram K (n+1)).toBilin' v v=0 ∧ v (neg (n+1) 0)=0} ≃
      K × {v:Index n → K //(gram K n).toBilin' v v=0} where
  toFun p := (p.val (pos (n+1) 0),⟨tailRestriction K n p.val,
    (gram_norm_tail_of_negative_head_zero K n p.val p.property.2).symm.trans p.property.1⟩)
  invFun p := ⟨cons K n p.1 p.2.val,⟨(norm_cons K n p.1 p.2.val).trans p.2.property,
    cons_head_negative K n p.1 p.2.val⟩⟩
  left_inv p := by
    apply Subtype.ext
    funext x
    obtain ⟨x,rfl⟩ := (tailEquiv n).surjective x
    rcases x with i|i
    · simp [cons,tailRestriction]
    · fin_cases i
      · simp [cons]
      · simpa [cons] using p.property.2.symm
  right_inv p := by
    apply Prod.ext
    · exact cons_head_positive K n p.1 p.2.val
    · exact Subtype.ext (tail_cons K n p.1 p.2.val)

theorem coordinate_tangent_card [Finite K] (n : ℕ) (h2:(2:K)≠0) :
    Nat.card {v:Index (n+1)→K //(gram K (n+1)).toBilin' v v=0 ∧ v (neg (n+1) 0)=0}=
      Nat.card K^(2*n+1) := by
  rw [Nat.card_congr (coordinateTangentEquiv K n),Nat.card_prod,singular_vectors_card K n h2]
  rw [pow_succ,Nat.mul_comm]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
