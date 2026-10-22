import SymmetricSubgroupAsymptotics.CFSGGradedMatrixHighLayerProducts

/-! Lowest-height multiplication before any root or characteristic
specialization. Commuting actual units have commuting lowest parts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixLowestProduct
open CFSGGradedMatrixSupport CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixHighLayerProducts
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem degreePart_supported (weight : I→ℤ) (d : ℤ) (M : Matrix I I K) :
    Supported weight (fun v=>v+d) (degreePart weight d M) := by
  intro i j hij
  change (if weight i=weight j+d then M i j else 0)=0
  exact if_neg hij

theorem lowest_product (weight : I→ℤ) (d e : ℤ) (M N : Matrix I I K)
    (hM : BelowCut weight d M) (hN : BelowCut weight e N) :
    degreePart weight (d+e) (M*N)=degreePart weight d M*degreePart weight e N := by
  have hprod : Supported weight (fun v=>v+(d+e))
      (degreePart weight d M*degreePart weight e N) := by
    apply supported_congr (supported_mul (degreePart_supported weight d M)
      (degreePart_supported weight e N))
    intro v
    dsimp only [Function.comp_apply]
    omega
  apply Matrix.ext
  intro i j
  change (if weight i=weight j+(d+e) then (M*N) i j else 0)=_
  by_cases hij : weight i=weight j+(d+e)
  · rw [if_pos hij,Matrix.mul_apply,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    change M i k*N k j=
      (if weight i=weight k+d then M i k else 0)*(if weight k=weight j+e then N k j else 0)
    by_cases hik : weight i=weight k+d
    · have hkj : weight k=weight j+e := by omega
      rw [if_pos hik,if_pos hkj]
    · rw [if_neg hik,zero_mul]
      by_cases hilow : weight i<weight k+d
      · rw [hM i k hilow,zero_mul]
      · rw [hN k j (by omega),mul_zero]
  · rw [if_neg hij]
    exact (hprod i j hij).symm

theorem commuting_units_lowest_parts (weight : I→ℤ) (d e : ℤ)
    (u v : (Matrix I I K)ˣ)
    (hu : BelowCut weight d ((u : Matrix I I K)-1))
    (hv : BelowCut weight e ((v : Matrix I I K)-1)) (hc : u*v=v*u) :
    degreePart weight d ((u : Matrix I I K)-1)*degreePart weight e ((v : Matrix I I K)-1)=
      degreePart weight e ((v : Matrix I I K)-1)*degreePart weight d ((u : Matrix I I K)-1) := by
  have hval := congrArg (fun a : (Matrix I I K)ˣ=>(a : Matrix I I K)) hc
  change (u : Matrix I I K)*(v : Matrix I I K)=(v : Matrix I I K)*(u : Matrix I I K) at hval
  have hm : ((u : Matrix I I K)-1)*((v : Matrix I I K)-1)=
      ((v : Matrix I I K)-1)*((u : Matrix I I K)-1) := by
    calc
      _=(u : Matrix I I K)*(v : Matrix I I K)-(u : Matrix I I K)-(v : Matrix I I K)+1 := by noncomm_ring
      _=(v : Matrix I I K)*(u : Matrix I I K)-(v : Matrix I I K)-(u : Matrix I I K)+1 := by rw [hval];abel
      _=_ := by noncomm_ring
  have he := congrArg (degreePart weight (d+e)) hm
  rw [lowest_product weight d e _ _ hu hv] at he
  have hswap : d+e=e+d := add_comm d e
  rw [hswap,lowest_product weight e d _ _ hv hu] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixLowestProduct
