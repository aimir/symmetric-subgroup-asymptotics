import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRationalFamily

/-! FULL ambient integer matrix coordinate map for D. Its Cartan entries
are doubled half-sums; no integral Cartan inverse outside the parity
lattice is asserted. After rational casting it is exactly twice the
proved rational coordinate map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralDoubledCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDCartanIntrinsicCoordinates
variable (r : ℕ) (hr : 4 ≤ r)

def cartanCoordinates : (Fin r→ℤ)→ₗ[ℤ](Fin r→ℤ) :=
  LinearMap.pi (fun i=>
    if i.val+2 < r then (2:ℤ) • prefixSum r i.val
    else if i.val+1 < r then
      total r-(2:ℤ) • LinearMap.proj (⟨r-1,by omega⟩ : Fin r)
    else total r)

theorem cast_cartanCoordinates (a : Fin r→ℤ) (i : Fin r) :
    (cartanCoordinates r hr a i:ℚ)=2*rationalCoordinates r hr a i := by
  by_cases hi : i.val+2 < r
  · simp only [cartanCoordinates,rationalCoordinates,LinearMap.pi_apply,if_pos hi,
      LinearMap.smul_apply,LinearMap.comp_apply]
    simp only [two_smul]
    change ((prefixSum r i.val a+prefixSum r i.val a:ℤ):ℚ)=2*(prefixSum r i.val a:ℚ)
    push_cast
    ring
  · by_cases hi' : i.val+1 < r
    · simp only [cartanCoordinates,rationalCoordinates,LinearMap.pi_apply,if_neg hi,
        if_pos hi',LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.proj_apply,
        LinearMap.comp_apply]
      change ((total r a-2*a ⟨r-1,by omega⟩:ℤ):ℚ)=
        2*((1/2:ℚ)*(total r a:ℚ)-(a ⟨r-1,by omega⟩:ℚ))
      push_cast
      ring
    · simp only [cartanCoordinates,rationalCoordinates,LinearMap.pi_apply,if_neg hi,
        if_neg hi',LinearMap.smul_apply,LinearMap.comp_apply]
      change (total r a:ℚ)=2*((1/2:ℚ)*(total r a:ℚ))
      ring

def diagonal : Mat ℤ r→ₗ[ℤ](Fin r→ℤ) where
  toFun M i:=M (.inl i) (.inl i)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def coordinates : Mat ℤ r→ₗ[ℤ](BasisIndex r→ℤ) :=
  LinearMap.pi (fun
    | .inl i=>(LinearMap.proj i).comp ((cartanCoordinates r hr).comp (diagonal r))
    | .inr j=>(2:ℤ) • (LinearMap.proj j).comp
        (CFSGOrthogonalDUniformRootCoordinates.coordinates ℤ r))

theorem cast_coordinates (M : Mat ℤ r) (j : BasisIndex r) :
    (coordinates r hr M j:ℚ)=2*CFSGOrthogonalDUniformRationalFamily.coordinates r hr
      ((Int.castRingHom ℚ).mapMatrix M) j := by
  cases j with
  | inl i =>
    change (cartanCoordinates r hr (diagonal r M) i:ℚ)=
      2*CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
        (CFSGOrthogonalDUniformRationalFamily.diagonal r ((Int.castRingHom ℚ).mapMatrix M)) i
    have hd : CFSGOrthogonalDUniformRationalFamily.diagonal r
        ((Int.castRingHom ℚ).mapMatrix M)=fun k=>(diagonal r M k:ℚ) := rfl
    rw [hd,CFSGOrthogonalDRationalCartanCoordinates.coordinates_cast]
    exact cast_cartanCoordinates r hr _ i
  | inr j =>
    simp only [coordinates,LinearMap.pi_apply,LinearMap.smul_apply,
      LinearMap.comp_apply,LinearMap.proj_apply,two_smul]
    change ((M (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
      (CFSGOrthogonalDUniformRootCoordinates.entry r j).2+
      M (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
        (CFSGOrthogonalDUniformRootCoordinates.entry r j).2:ℤ):ℚ)=
        2*((M (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
          (CFSGOrthogonalDUniformRootCoordinates.entry r j).2):ℚ)
    push_cast
    ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralDoubledCoordinates
