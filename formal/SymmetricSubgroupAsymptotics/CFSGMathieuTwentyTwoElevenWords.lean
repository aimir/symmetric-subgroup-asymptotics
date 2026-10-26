import SymmetricSubgroupAsymptotics.External.CFSG.Models.Mathieu22

/-! The two selected literal words and the exact recovery words suggested
by the bounded primary diagnostic. Definitions alone certify nothing;
the separate finite certificates check the actual original permutations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
open CFSG.Models.Mathieu22Construction

def firstWord : Equiv.Perm (Fin 22) := a^3*b^2
def secondWord : Equiv.Perm (Fin 22) := a*firstWord*a⁻¹

def recoverA {G : Type*} [Group G] (x y : G) : G :=
  x^2*y⁻¹*x*y⁻¹*x*y*x*y^2*x*y⁻¹

def recoverB {G : Type*} [Group G] (x y : G) : G :=
  x*y⁻¹*x*y*x^4*y*x*y

theorem recoverA_mem {G : Type*} [Group G] (H : Subgroup G) (x y : G)
    (hx : x∈H) (hy : y∈H) : recoverA x y∈H := by
  have h1 := H.mul_mem (H.pow_mem hx 2) (H.inv_mem hy)
  have h2 := H.mul_mem h1 hx
  have h3 := H.mul_mem h2 (H.inv_mem hy)
  have h4 := H.mul_mem h3 hx
  have h5 := H.mul_mem h4 hy
  have h6 := H.mul_mem h5 hx
  have h7 := H.mul_mem h6 (H.pow_mem hy 2)
  have h8 := H.mul_mem h7 hx
  exact H.mul_mem h8 (H.inv_mem hy)

theorem recoverB_mem {G : Type*} [Group G] (H : Subgroup G) (x y : G)
    (hx : x∈H) (hy : y∈H) : recoverB x y∈H := by
  have h1 := H.mul_mem hx (H.inv_mem hy)
  have h2 := H.mul_mem h1 hx
  have h3 := H.mul_mem h2 hy
  have h4 := H.mul_mem h3 (H.pow_mem hx 4)
  have h5 := H.mul_mem h4 hy
  have h6 := H.mul_mem h5 hx
  exact H.mul_mem h6 hy

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenWords
