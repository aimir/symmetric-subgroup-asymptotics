import SymmetricSubgroupAsymptotics.BinaryFourNonsplitKernelGenerators
import SymmetricSubgroupAsymptotics.BinaryKleinTernaryNormalChain
import Mathlib.Algebra.CharP.Two

/-! The kernels needed for normal-generator transfer are forced by every
normal subgroup outside the actual translation kernel. The displayed
Klein commutators force two diagonal directions. The square of an actual
Klein lift, and its ternary conjugates, supply the remaining directions.
The nonsplit source is never replaced by a split extension. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

def sourceNormalSpace (full : Bool) (N : Subgroup (NonsplitSource full)) :
    Submodule Scalar (space full) where
  carrier := {x | sourceTranslation full (Multiplicative.ofAdd x) ∈ N}
  zero_mem' := by
    change sourceTranslation full 1 ∈ N
    rw [map_one]
    exact N.one_mem
  add_mem' := by
    intro x y hx hy
    change sourceTranslation full (Multiplicative.ofAdd x * Multiplicative.ofAdd y) ∈ N
    rw [map_mul]
    exact N.mul_mem hx hy
  smul_mem' := by
    intro a x hx
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simp only [zero_smul]
      change sourceTranslation full 1 ∈ N
      rw [map_one]
      exact N.one_mem
    · simpa only [one_smul] using hx

theorem sourceNormalSpace_conjugate (full : Bool)
    (N : Subgroup (NonsplitSource full)) (hN : N.Normal)
    (g : NonsplitSource full) (x : space full) (hx : x ∈ sourceNormalSpace full N) :
    restrictedLinear full g.val.right x ∈ sourceNormalSpace full N := by
  have h := hN.conj_mem _ hx g
  rw [source_conjugate_translation] at h
  exact h

theorem sourceNormalSpace_difference (full : Bool)
    (N : Subgroup (NonsplitSource full)) (hN : N.Normal)
    (g : NonsplitSource full) (hg : g ∈ N) (x : space full) :
    restrictedLinear full g.val.right x - x ∈ sourceNormalSpace full N := by
  let t := sourceTranslation full (Multiplicative.ofAdd x)
  have h : g * t * g⁻¹ * t⁻¹ ∈ N := by
    have hc := hN.conj_mem g⁻¹ (N.inv_mem hg) t
    simpa only [mul_assoc] using N.mul_mem hg hc
  dsimp only [t] at h
  rw [source_conjugate_translation, ← map_inv, ← map_mul] at h
  change sourceTranslation full
    (Multiplicative.ofAdd (restrictedLinear full g.val.right x - x)) ∈ N
  simpa only [ofAdd_sub, div_eq_mul_inv] using h

def sourceSmallBasis (full : Bool) (i : Fin 5) : space full :=
  ⟨basisVector i.castSucc, by
    intro h
    fin_cases i <;> simp [basisVector]⟩

def coverSeed (full : Bool) : space full :=
  ⟨if full then basisVector 4 + basisVector 5 else basisVector 3, by
    cases full
    · intro h; simp [basisVector]
    · intro h; cases h⟩

def coverOrbit (full : Bool) : Fin 5 → space full :=
  ![sourceSmallBasis full 0, sourceSmallBasis full 1, coverSeed full,
    restrictedLinear full cElement (coverSeed full),
    restrictedLinear full cElement (restrictedLinear full cElement (coverSeed full))]

def coverCoefficients (full : Bool) (x : Coordinates) : Fin 5 → Scalar :=
  if full then ![x 0 + x 2 + x 3, x 1 + x 2, x 4 + x 3, x 3, x 2 + x 3]
  else ![x 0, x 1, x 3, x 4, x 2]

theorem coverOrbit_coordinates (full : Bool) (i : Fin 5) :
    (coverOrbit full i : Coordinates) =
      (if full then
        ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0],
          ![0, 0, 0, 0, 1, 1], ![0, 1, 1, 1, 1, 1], ![1, 1, 1, 0, 0, 1]]
      else
        ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0],
          ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0]]) i := by
  cases full <;> fin_cases i <;>
    dsimp only [coverOrbit, coverSeed, sourceSmallBasis, restrictedLinear] <;>
    (try simp only [linear_c]) <;>
    ext j <;> revert j <;> decide +kernel

theorem coverOrbit_decomposition (full : Bool) (x : space full)
    (htail : full = true → tailSum (includeAugmentation (x : Coordinates)) = 0) :
    x = ∑ i : Fin 5, coverCoefficients full x i • coverOrbit full i := by
  apply Subtype.ext
  change (x : Coordinates) =
    ∑ i : Fin 5, coverCoefficients full x i • (coverOrbit full i : Coordinates)
  simp_rw [coverOrbit_coordinates]
  cases full
  · have hx5 : (x : Coordinates) 5 = 0 := x.property rfl
    ext i
    fin_cases i <;>
      simp [coverCoefficients, Fin.sum_univ_succ, hx5]
  · have ht : (x : Coordinates) 5 + (x : Coordinates) 2 +
        (x : Coordinates) 3 + (x : Coordinates) 4 = 0 := htail rfl
    have hx5 : (x : Coordinates) 5 =
        (x : Coordinates) 2 + (x : Coordinates) 3 + (x : Coordinates) 4 := by
      have h := (CharTwo.add_eq_iff_eq_add
        (a := (x : Coordinates) 5)
        (b := (x : Coordinates) 2 + (x : Coordinates) 3 + (x : Coordinates) 4)
        (c := (0 : Scalar))).mp (by simpa only [add_assoc] using ht)
      simpa only [zero_add] using h
    ext i
    fin_cases i <;>
      simp [coverCoefficients, Fin.sum_univ_succ, hx5] <;>
      ring_nf <;>
      simp [show (2 : Scalar) = 0 from by decide +kernel,
        show (3 : Scalar) = 1 from by decide +kernel]

theorem source_lift_u_augmentation (full : Bool) (g : NonsplitSource full)
    (hg : g.val.right = uElement) :
    augmentation g.val.left.toAdd = if full then ![1, 1] else ![1, 0] := by
  cases full
  · have h : augmentation g.val.left.toAdd = g.val.right.left.toAdd := g.property.1
    rw [h, hg]
    rfl
  · have h : augmentation g.val.left.toAdd = localCycle g.val.right.left.toAdd := g.property
    rw [h, hg]
    rfl

def liftSquareDiagonal (full : Bool) (g : NonsplitSource full) : space full :=
  (g.val.left.toAdd 4 + g.val.left.toAdd 5) • sourceSmallBasis full 0 +
    (g.val.left.toAdd 2 + g.val.left.toAdd 4 + g.val.left.toAdd 5) •
      sourceSmallBasis full 1

theorem source_lift_u_square (full : Bool) (g : NonsplitSource full)
    (hg : g.val.right = uElement) :
    g ^ 2 = sourceTranslation full
      (Multiplicative.ofAdd (liftSquareDiagonal full g + coverSeed full)) := by
  have ha := source_lift_u_augmentation full g hg
  have h6 := congrFun ha 0
  have h7 := congrFun ha 1
  rw [pow_two]
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change g.val.left.toAdd + fullComplementLinear g.val.right g.val.left.toAdd =
      includeAugmentation ((liftSquareDiagonal full g + coverSeed full : space full) : Coordinates)
    rw [hg, fullLinear_u]
    cases full <;>
      change g.val.left.toAdd 6 = _ at h6 <;>
      change g.val.left.toAdd 7 = _ at h7 <;>
      ext i <;> fin_cases i <;>
      simp [fullU, includeAugmentation, liftSquareDiagonal, sourceSmallBasis,
        coverSeed, basisVector, h6, h7] <;>
      ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide, mul_zero, zero_add, add_zero]
  · change g.val.right * g.val.right = 1
    rw [hg]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      ext i
      revert i
      decide +kernel
    · rfl

theorem sourceNormalSpace_diagonals (full : Bool)
    (N : Subgroup (NonsplitSource full)) (hN : N.Normal)
    (g : NonsplitSource full) (hgN : g ∈ N) (hg : g.val.right = uElement) :
    sourceSmallBasis full 0 ∈ sourceNormalSpace full N ∧
      sourceSmallBasis full 1 ∈ sourceNormalSpace full N := by
  have h1 := sourceNormalSpace_difference full N hN g hgN (sourceSmallBasis full 2)
  have h01 := sourceNormalSpace_difference full N hN g hgN (sourceSmallBasis full 4)
  rw [hg] at h1 h01
  have e1 : restrictedLinear full uElement (sourceSmallBasis full 2) -
      sourceSmallBasis full 2 = sourceSmallBasis full 1 := by
    apply Subtype.ext
    change complementLinear uElement (basisVector 2) - basisVector 2 = basisVector 1
    rw [linear_u]
    ext i
    revert i
    decide +kernel
  have e01 : restrictedLinear full uElement (sourceSmallBasis full 4) -
      sourceSmallBasis full 4 = sourceSmallBasis full 0 + sourceSmallBasis full 1 := by
    apply Subtype.ext
    change complementLinear uElement (basisVector 4) - basisVector 4 = basisVector 0 + basisVector 1
    rw [linear_u]
    ext i
    revert i
    decide +kernel
  rw [e1] at h1
  rw [e01] at h01
  exact ⟨by simpa only [add_sub_cancel_right] using
    (sourceNormalSpace full N).sub_mem h01 h1, h1⟩

theorem sourceNormalSpace_coverOrbit (full : Bool)
    (N : Subgroup (NonsplitSource full)) (hN : N.Normal)
    (g : NonsplitSource full) (hgN : g ∈ N) (hg : g.val.right = uElement)
    (i : Fin 5) : coverOrbit full i ∈ sourceNormalSpace full N := by
  obtain ⟨h0, h1⟩ := sourceNormalSpace_diagonals full N hN g hgN hg
  have hd : liftSquareDiagonal full g ∈ sourceNormalSpace full N :=
    (sourceNormalSpace full N).add_mem
      ((sourceNormalSpace full N).smul_mem _ h0)
      ((sourceNormalSpace full N).smul_mem _ h1)
  have hs : liftSquareDiagonal full g + coverSeed full ∈ sourceNormalSpace full N := by
    have h := N.pow_mem hgN 2
    rw [source_lift_u_square full g hg] at h
    exact h
  have hseed : coverSeed full ∈ sourceNormalSpace full N := by
    simpa only [add_sub_cancel_left] using (sourceNormalSpace full N).sub_mem hs hd
  have hc (x : space full) (hx : x ∈ sourceNormalSpace full N) :
      restrictedLinear full cElement x ∈ sourceNormalSpace full N :=
    sourceNormalSpace_conjugate full N hN (sourceC full) x hx
  fin_cases i
  · exact h0
  · exact h1
  · exact hseed
  · exact hc _ hseed
  · exact hc _ (hc _ hseed)

theorem outside_kernel_lift_u (full : Bool) (N : Subgroup (NonsplitSource full))
    (hN : N.Normal) (hNE : ¬ N ≤ sourceKernel full) :
    ∃ g ∈ N, g.val.right = uElement := by
  let pi := blockProjection full
  have hmapN : (N.map pi).Normal := hN.map pi (blockProjection_surjective full)
  have hmapb : N.map pi ≠ ⊥ := by
    intro hb
    apply hNE
    intro g hg
    have h : pi g ∈ N.map pi := ⟨g, hg, rfl⟩
    rw [hb] at h
    exact Subgroup.mem_bot.mp h
  have hu : uElement ∈ N.map pi :=
    BinaryKleinTernaryNormalChain.kleinKernel_le_normal (N.map pi) hmapN hmapb (by rfl)
  obtain ⟨g, hg, hgu⟩ := hu
  exact ⟨g, hg, hgu⟩

theorem outside_kernel_translation_mem (full : Bool)
    (N : Subgroup (NonsplitSource full)) (hN : N.Normal)
    (hNE : ¬ N ≤ sourceKernel full) (x : space full)
    (htail : full = true → tailSum (includeAugmentation (x : Coordinates)) = 0) :
    sourceTranslation full (Multiplicative.ofAdd x) ∈ N := by
  obtain ⟨g, hgN, hg⟩ := outside_kernel_lift_u full N hN hNE
  change x ∈ sourceNormalSpace full N
  rw [coverOrbit_decomposition full x htail]
  exact (sourceNormalSpace full N).sum_mem fun i _ =>
    (sourceNormalSpace full N).smul_mem _
      (sourceNormalSpace_coverOrbit full N hN g hgN hg i)

theorem row10_kernel_cover (N : Subgroup Row10Model) (hN : N.Normal)
    (hNE : ¬ N ≤ row10Projection.ker) : row10Projection.ker ≤ N := by
  intro g hg
  let x := (sourceKernelEquiv false) (⟨g, hg⟩ : sourceKernel false)
  have h := outside_kernel_translation_mem false N hN hNE x.toAdd (by intro h; cases h)
  have he : sourceTranslation false x = g :=
    congrArg Subtype.val ((sourceKernelEquiv false).symm_apply_apply ⟨g, hg⟩)
  change sourceTranslation false x ∈ N at h
  rwa [he] at h

theorem row12_kernel_cover (N : Subgroup Row12Model) (hN : N.Normal)
    (hNE : ¬ N ≤ row12Projection.ker) : row12Quotient.ker ≤ N := by
  intro g hg
  obtain ⟨hr, ht⟩ := (row12Quotient_kernel g).mp hg
  let x := (sourceKernelEquiv true) (⟨g, hr⟩ : sourceKernel true)
  have he : sourceTranslation true x = g :=
    congrArg Subtype.val ((sourceKernelEquiv true).symm_apply_apply ⟨g, hr⟩)
  have htail : tailSum (includeAugmentation (x.toAdd : Coordinates)) = 0 := by
    have hleft := congrArg (fun k : Row12Model => k.val.left.toAdd) he
    change includeAugmentation (x.toAdd : Coordinates) = g.val.left.toAdd at hleft
    rw [hleft]
    exact ht
  have h := outside_kernel_translation_mem true N hN hNE x.toAdd (fun _ => htail)
  change sourceTranslation true x ∈ N at h
  rwa [he] at h

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
