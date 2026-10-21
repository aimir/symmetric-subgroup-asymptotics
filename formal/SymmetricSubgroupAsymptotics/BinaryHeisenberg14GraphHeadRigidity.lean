import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementHeadBound
import SymmetricSubgroupAsymptotics.BinarySplitAffineFunctionCoordinates
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenberg14GraphHeadRigidity
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
private def cBasis : Fin 8 → Fin 10 → ℕ := ![![34560,26112,7680,129,65,33,17,9,5,3],![34561,26112,7680,129,65,33,17,9,5,3],![34560,26113,7680,129,65,33,17,9,5,3],![34561,26113,7680,129,65,33,17,9,5,3],![34560,26112,7681,129,65,33,17,9,5,3],![34561,26112,7681,129,65,33,17,9,5,3],![34560,26113,7681,129,65,33,17,9,5,3],![34561,26113,7681,129,65,33,17,9,5,3]]
private def cCoordinates : Fin 8 → Fin 16 → ℕ := ![![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1],![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1],![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1],![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1],![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1],![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1],![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1],![0,512,256,128,64,32,16,8,0,0,0,0,4,0,2,1]]
private def dBasis : Fin 7 → Fin 7 → ℕ := ![![135,6,102,30,5,65280,85],![135,6,102,30,65285,65280,85],![135,6,102,30,5,65285,85],![135,6,102,30,65280,65285,85],![135,6,102,30,5,65280,85],![135,6,102,30,65285,85,65280],![135,6,102,30,5,65285,85]]
private def dCoordinates : Fin 7 → Fin 16 → ℕ := ![![0,18,16,0,10,92,90,3,0,0,0,0,0,0,0,32],![0,50,48,0,10,124,122,3,0,0,0,0,0,0,0,32],![0,18,16,0,10,92,90,3,0,0,0,0,0,0,0,48],![0,50,48,0,10,124,122,3,0,0,0,0,0,0,0,16],![0,18,16,0,10,92,90,3,0,0,0,0,0,0,0,32],![0,82,80,0,10,124,122,3,0,0,0,0,0,0,0,64],![0,18,16,0,10,92,90,3,0,0,0,0,0,0,0,48]]
private def cInclude (p : Fin 8) := (binaryRectangularMatrixOfColumnMasks 16 10 (cBasis p)).mulVecLin
private def cCoords (p : Fin 8) := (binaryRectangularMatrixOfColumnMasks 10 16 (cCoordinates p)).mulVecLin
private def dInclude (p : Fin 7) := (binaryRectangularMatrixOfColumnMasks 16 7 (dBasis p)).mulVecLin
private def dCoords (p : Fin 7) := (binaryRectangularMatrixOfColumnMasks 7 16 (dCoordinates p)).mulVecLin
private theorem c_basis : ∀ p i, cCoords p (cInclude p (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem d_basis : ∀ p i, dCoords p (dInclude p (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem c_left (p : Fin 8) (v : Fin 10 → ZMod 2) : cCoords p (cInclude p v) = v := by
  have he : (cCoords p).comp (cInclude p) = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, c_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private theorem d_left (p : Fin 7) (v : Fin 7 → ZMod 2) : dCoords p (dInclude p v) = v := by
  have he : (dCoords p).comp (dInclude p) = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, d_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v

def stateChart (p : Fin 8) : BinaryCoordinateSpace 16 10 := ⟨cInclude p,cCoords p,c_left p⟩
private def displacementChart (p : Fin 7) : BinaryCoordinateSpace 16 7 := ⟨dInclude p,dCoords p,d_left p⟩
private def topImages : Fin 7 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![2,7,0,5,6,3,4,1],![4,5,6,7,0,1,2,3],![0,2,1,4,3,5,6,7],![0,2,1,3,4,6,5,7]]
private theorem top_involution : ∀ i j, topImages i (topImages i j) = j := by decide +kernel
def generatorTop (i : Fin 7) : Equiv.Perm (Fin 8) := {
  toFun := topImages i
  invFun := topImages i
  left_inv := top_involution i
  right_inv := top_involution i }
def generatorOffsetMasks : Fin 7 → ℕ := ![135,102,30,0,0,0,0]
def generatorOffset (i : Fin 7) := binaryVectorOfMask 8 (generatorOffsetMasks i)
def action (i : Fin 7) : V →ₗ[ZMod 2] V :=
  (BinaryPairFrame.pairLayerFlatten (w := 8)).toLinearMap.comp
    ((BinaryPairFrame.affinePairLayerMap (generatorTop i) (generatorOffset i)).comp
      (BinaryPairFrame.pairLayerFlatten (w := 8)).symm.toLinearMap)
private def generatorIndex : Fin 7 → Fin 7 → Fin 7 := ![![0,0,1,2,3,3,3],![0,0,1,2,3,3,3],![0,0,1,2,3,3,3],![0,0,1,2,3,3,3],![0,0,1,2,3,3,3],![0,0,1,2,3,3,4],![0,0,1,2,3,3,3]]
private def basisIndex : Fin 7 → Fin 7 → Fin 10 := ![![0,1,1,2,0,1,4],![0,1,1,2,1,2,4],![0,1,1,2,0,1,4],![0,1,1,2,1,2,4],![0,1,1,2,0,1,4],![0,1,1,2,1,4,0],![0,1,1,2,0,1,4]]
def nonzeroForm (p : Fin 7) : Fin 8 := ⟨p.val+1,by omega⟩
private theorem selected_moves : ∀ p j,
    (displacementChart p).inclusion (Pi.single j 1) =
      action (generatorIndex p j) ((stateChart (nonzeroForm p)).inclusion (Pi.single (basisIndex p j) 1)) -
        (stateChart (nonzeroForm p)).inclusion (Pi.single (basisIndex p j) 1) := by decide +kernel

theorem head_le_of_nonzero_form {G : Type} [Group G]
    (rho : Representation (ZMod 2) G V) (u : Fin 7 → G) (B : Subrepresentation rho)
    (p : Fin 7) (hB : B.toSubmodule = (stateChart (nonzeroForm p)).space)
    (hact : ∀ i, rho (u i) = action i) :
    Module.finrank (ZMod 2) B.toRepresentation.Coinvariants ≤ 3 := by
  apply binary_coinvariant_head_le_of_coordinate_displacements rho u B
    (stateChart (nonzeroForm p)) (displacementChart p) hB
    (generatorIndex p) (basisIndex p) _ 3 (by decide)
  intro j
  rw [hact]
  exact selected_moves p j

/-- Only the literal zero coefficient form can attain the required head. -/
theorem form_eq_zero_of_large_head {G : Type} [Group G]
    (rho : Representation (ZMod 2) G V) (u : Fin 7 → G) (B : Subrepresentation rho)
    (phi : Fin 8) (hB : B.toSubmodule = (stateChart phi).space)
    (hact : ∀ i, rho (u i) = action i)
    (hlarge : 4 ≤ Module.finrank (ZMod 2) B.toRepresentation.Coinvariants) : phi = 0 := by
  by_contra hne
  have hpos : 0 < phi.val := by
    by_contra hh
    apply hne
    apply Fin.ext
    omega
  let p : Fin 7 := ⟨phi.val-1,by omega⟩
  have he : nonzeroForm p = phi := by
    apply Fin.ext
    change (phi.val-1)+1=phi.val
    omega
  have hb := head_le_of_nonzero_form rho u B p (by rwa [he]) hact
  omega
end SymmetricSubgroupAsymptotics.BinaryHeisenberg14GraphHeadRigidity
