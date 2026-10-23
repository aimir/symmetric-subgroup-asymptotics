import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators

/-! The TWO folded G2 Cartans primitively detect EVERY positive D4
lattice root. The 12-root cover is proved; the displayed integer Bezout
coefficients then give nonzero weights in every nontrivial ring. No
modular weight-character separation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFoldedWeights
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootCover
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGNormTwoCoordinatePositiveRootGenerators
local notation "A" => CartanMatrix.D 4

def orbitCartan (i : Fin 2) : Fin 4→ℤ :=
  ![(Pi.single 0 (1:ℤ) : Fin 4→ℤ)+Pi.single 2 1+Pi.single 3 1,Pi.single 1 1] i

def foldedWeight (k : Roots A) (i : Fin 2) : ℤ := integerPairing A k.val (orbitCartan i)

private def shortA : Fin 3→ℤ := ![0,0,1]
private def shortB : Fin 3→ℤ := ![-1,1,0]
private def longA : Fin 3→ℤ := ![1,0,0]
private def longB : Fin 3→ℤ := ![2,-1,1]

private theorem vec4_two {R : Type*} (a b c d : R) :
    ![a,b,c,d] (2 : Fin 4)=c := rfl

private theorem vec4_three {R : Type*} (a b c d : R) :
    ![a,b,c,d] (3 : Fin 4)=d := rfl

/- The two matrix-vector products are evaluated once, before any root
coordinates are substituted. This keeps the finite root certificates
independent of the nested bilinear-form sums. -/
private theorem outer_column :
    (A) *ᵥ orbitCartan 0 = ![(2:ℤ),-3,2,2] := by
  change (A) *ᵥ (((Pi.single 0 (1:ℤ) : Fin 4→ℤ)+Pi.single 2 1)+Pi.single 3 1) = _
  rw [Matrix.mulVec_add,Matrix.mulVec_add,Matrix.mulVec_single_one,
    Matrix.mulVec_single_one,Matrix.mulVec_single_one]
  funext j
  fin_cases j <;> norm_num [Matrix.col,cartan_eq,vec4_two,vec4_three]

private theorem central_column :
    (A) *ᵥ orbitCartan 1 = ![(-1:ℤ),2,-1,-1] := by
  change (A) *ᵥ (Pi.single 1 (1:ℤ) : Fin 4→ℤ) = _
  rw [Matrix.mulVec_single_one]
  funext j
  fin_cases j <;> norm_num [Matrix.col,cartan_eq,vec4_two,vec4_three]

private theorem outer_weight (k : Roots A) :
    foldedWeight k 0 = 2*k.val 0-3*k.val 1+2*k.val 2+2*k.val 3 := by
  change (A).toBilin' k.val (orbitCartan 0) = _
  rw [Matrix.toBilin'_apply',outer_column]
  simp only [dotProduct,Fin.sum_univ_succ]
  change k.val 0*2+(k.val 1*(-3)+(k.val 2*2+(k.val 3*2+0))) = _
  ring

private theorem central_weight (k : Roots A) :
    foldedWeight k 1 = -k.val 0+2*k.val 1-k.val 2-k.val 3 := by
  change (A).toBilin' k.val (orbitCartan 1) = _
  rw [Matrix.toBilin'_apply',central_column]
  simp only [dotProduct,Fin.sum_univ_succ]
  change k.val 0*(-1)+(k.val 1*2+(k.val 2*(-1)+(k.val 3*(-1)+0))) = _
  ring

private theorem short_weight_identity (s k : Fin 3) :
    shortA s*foldedWeight (shortRoot s k) 0+shortB s*foldedWeight (shortRoot s k) 1=1 := by
  rw [outer_weight,central_weight]
  fin_cases s <;> fin_cases k <;>
    norm_num [shortA,shortB,shortRoot,shortCoordinates,vec4_two,vec4_three]

private theorem long_weight_identity (s : Fin 3) :
    longA s*foldedWeight (longRoot s) 0+longB s*foldedWeight (longRoot s) 1=1 := by
  rw [outer_weight,central_weight]
  fin_cases s <;>
    norm_num [longA,longB,longRoot,longCoordinates,vec4_two,vec4_three]

theorem foldedWeights_generate_one (k : PositiveRoot A) :
    ∃a b : ℤ,a*foldedWeight k.val 0+b*foldedWeight k.val 1=1 := by
  rcases positive_root_cover k.val k.property with ⟨s,j,hk⟩|⟨s,hk⟩
  · refine ⟨shortA s,shortB s,?_⟩
    rw [hk]
    exact short_weight_identity s j
  · refine ⟨longA s,longB s,?_⟩
    rw [hk]
    exact long_weight_identity s

theorem exists_foldedWeight_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (k : PositiveRoot A) :
    ∃i : Fin 2,(foldedWeight k.val i : R)≠0 := by
  by_contra hn
  have hz : ∀i : Fin 2,(foldedWeight k.val i : R)=0 := by
    simpa only [not_exists,not_not] using hn
  obtain ⟨a,b,h⟩ := foldedWeights_generate_one k
  have he := congrArg (Int.cast : ℤ→R) h
  simp only [Int.cast_add,Int.cast_mul,Int.cast_one,hz,mul_zero,add_zero] at he
  exact zero_ne_one he

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFoldedWeights
