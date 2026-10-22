import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! For any literal Weyl word n and simple i, one of n^-1 U_i n and
n^-1 U_i^- n is contained in the original positive group. The choice
depends only on the reflected integer root, not on its field parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootDichotomy
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckSelfRootConjugation
open CFSGSerreQuadraticMatrix
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem conjugate_root_dichotomy (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) :
    (∀a : K,(wordUnit A hs hp b₀ s₀ K w)⁻¹*
      canonicalRoot (realizationData A hs hp b₀ s₀) K false i a*
      wordUnit A hs hp b₀ s₀ K w∈rootGroup A hs hp b₀ s₀ K false) ∨
    (∀a : K,(wordUnit A hs hp b₀ s₀ K w)⁻¹*
      canonicalRoot (realizationData A hs hp b₀ s₀) K true i a*
      wordUnit A hs hp b₀ s₀ K w∈rootGroup A hs hp b₀ s₀ K false) := by
  let v := inverseWord w
  let k := wordRoot A hs hp b₀ s₀ v (s₀ i)
  have hv : wordUnit A hs hp b₀ s₀ K v=(wordUnit A hs hp b₀ s₀ K w)⁻¹ :=
    wordUnit_inverseWord A hs hp b₀ s₀ K w
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
      (fun j=>by rw [hd j];exact even_two) ho k.val k.property with hpos|hneg
  · left
    intro a
    have hh := positive_word_mem A hd hs hp ho K v i a hpos
    change wordUnit A hs hp b₀ s₀ K v*
      canonicalRoot (realizationData A hs hp b₀ s₀) K false i a*
      (wordUnit A hs hp b₀ s₀ K v)⁻¹∈_ at hh
    rw [hv,inv_inv] at hh
    exact hh
  · right
    intro a
    have hsign : ∀l,0≤(wordRoot A hs hp b₀ s₀ (v++[i]) (s₀ i)).val l := by
      intro l
      rw [wordRoot_append]
      change 0≤(wordRoot A hs hp b₀ s₀ v (negativeIndex A hs hp (s₀ i))).val l
      rw [wordRoot_negative_val]
      exact neg_nonneg.mpr (hneg l)
    have hh := positive_word_mem A hd hs hp ho K (v++[i]) i (-a) hsign
    change wordUnit A hs hp b₀ s₀ K (v++[i])*
      canonicalRoot (realizationData A hs hp b₀ s₀) K false i (-a)*
      (wordUnit A hs hp b₀ s₀ K (v++[i]))⁻¹∈_ at hh
    rw [wordUnit_append] at hh
    simp only [wordUnit,mul_one] at hh
    have he : canonicalRoot (realizationData A hs hp b₀ s₀) K true i a=
        canonicalWeyl (realizationData A hs hp b₀ s₀) K i*
          canonicalRoot (realizationData A hs hp b₀ s₀) K false i (-a)*
          (canonicalWeyl (realizationData A hs hp b₀ s₀) K i)⁻¹ := by
      simpa only [neg_neg] using (self_root_word A hs hp b₀ s₀ K i (-a)).symm
    rw [he]
    have hg : (wordUnit A hs hp b₀ s₀ K w)⁻¹*
        (canonicalWeyl (realizationData A hs hp b₀ s₀) K i*
          canonicalRoot (realizationData A hs hp b₀ s₀) K false i (-a)*
          (canonicalWeyl (realizationData A hs hp b₀ s₀) K i)⁻¹)*
        wordUnit A hs hp b₀ s₀ K w=
      (wordUnit A hs hp b₀ s₀ K v*canonicalWeyl (realizationData A hs hp b₀ s₀) K i)*
        canonicalRoot (realizationData A hs hp b₀ s₀) K false i (-a)*
        (wordUnit A hs hp b₀ s₀ K v*canonicalWeyl (realizationData A hs hp b₀ s₀) K i)⁻¹ := by
      rw [hv]
      group
    rw [hg]
    exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootDichotomy
