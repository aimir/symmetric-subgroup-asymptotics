import SymmetricSubgroupAsymptotics.CFSGNormalKernelFixedVector
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoEquivalence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBImageRealization
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction
import SymmetricSubgroupAsymptotics.CFSGUnitConjugation

/-! The characteristic-two natural B action on the SAME original Serre
image is faithful. A kernel element fixes a terminal natural basis vector;
kernel normality and actual B/C vector transitivity then force it to be
the identity. No C simplicity or odd-characteristic commutant is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix TensorProduct CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley CFSGOrthogonalBGenerationBlockRestriction
open CFSGOrthogonalBGenerationCharTwoRestriction
open CFSGOrthogonalBGenerationCharTwoEquivalence
variable (K : Type) [Field K] [Finite K] [CharP K 2]

def restrictionRepresentation (r : ℕ) : elementaryRootGroup K r →*
    ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  CFSGProjectiveLinearPointAction.linearEquiv.toMonoidHom.comp (naturalRestriction K r)

omit [Finite K] in
theorem restrictionRepresentation_injective (r : ℕ) :
    Function.Injective (restrictionRepresentation K r) :=
  CFSGProjectiveLinearPointAction.linearEquiv.injective.comp (naturalRestriction_injective K r)

private theorem terminal_kernel_fixed (r : ℕ) (g : elementaryRootGroup K (r + 1))
    (hg : g ∈ (elementaryImageAction K (r + 1)).ker) :
    restrictionRepresentation K (r + 1) g
      (Pi.single (Sum.inl (Fin.last r)) 1) = Pi.single (Sum.inl (Fin.last r)) 1 := by
  let i : Fin (r + 1) := Fin.last r
  let y := (orthogonalBaseChange K (r + 1)).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator (CartanMatrix.B (r + 1)).transpose
      (CartanMatrix.Generators.E i))
  have hy : y.val = Matrix.single (pos (r + 1) i) (middle (r + 1)) 1 := by
    have hi : ¬i.val + 1 < r + 1 := by
      change ¬r + 1 < r + 1
      exact Nat.lt_irrefl _
    calc
      y.val = positive K (r + 1) i := orthogonalBaseChange_E K (r + 1) i
      _ = _ := by
        simp only [positive, dif_neg hi, CharTwo.two_eq_zero, Matrix.single_zero, sub_zero]
  have hfix := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) y
  have hc := congrArg Subtype.val hfix
  change (g.val : Mat K (r + 1)) * y.val * (↑g.val⁻¹ : Mat K (r + 1)) = y.val at hc
  have hcomm := (CFSGUnitConjugation.fix_iff_commute g.val y.val).mp hc
  rw [hy] at hcomm
  have hrow := elementary_le_rowSubgroup K (r + 1) g.property
  have hdiag : (g.val : Mat K (r + 1)) (middle (r + 1)) (middle (r + 1)) = 1 := by
    simpa only [middle, if_pos rfl] using hrow (middle (r + 1))
  change upperBlock K (Fin (r + 1) ⊕ Fin (r + 1)) (g.val : Mat K (r + 1)) *ᵥ
    Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1
  rw [Matrix.mulVec_single_one]
  funext j
  have he := congrArg (fun M : Mat K (r + 1) => M (Sum.inl j) (middle (r + 1))) hcomm
  dsimp only at he
  rw [Matrix.mul_single_apply_same] at he
  by_cases hj : j = Sum.inl i
  · subst j
    rw [Matrix.single_mul_apply_same, hdiag] at he
    simpa only [upperBlock, Matrix.submatrix_apply, Matrix.col, pos, mul_one,
      one_mul, Pi.single_eq_same] using he
  · have hj' : (Sum.inl j : Index (r + 1)) ≠ pos (r + 1) i := by
      intro heq
      exact hj (Sum.inl.inj heq)
    rw [Matrix.single_mul_apply_of_ne 1 _ _ _ _ hj'] at he
    simpa only [upperBlock, Matrix.submatrix_apply, Matrix.col, pos, mul_one,
      Pi.single_eq_of_ne hj] using he

theorem restrictionRepresentation_nonzero_orbit (r : ℕ) (hr : 0 < r)
    (v : Fin (r + 1) ⊕ Fin (r + 1) → K) (hv : v ≠ 0) :
    ∃ g : elementaryRootGroup K (r + 1), restrictionRepresentation K (r + 1) g
      (Pi.single (Sum.inl (Fin.last r)) 1) = v := by
  let v₀ : Fin (r + 1) ⊕ Fin (r + 1) → K := Pi.single (Sum.inl (Fin.last r)) 1
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have he := congrFun h (Sum.inl (Fin.last r))
    have hzero : (1 : K) = 0 := by simpa only [v₀, Pi.single_eq_same, Pi.zero_apply] using he
    exact one_ne_zero hzero
  obtain ⟨a, ha⟩ := CFSGSymplecticSerreMatrices.exists_elementary_mulVec_first_basis K r hr v hv
  obtain ⟨b, hb⟩ := CFSGSymplecticSerreMatrices.exists_elementary_mulVec_first_basis K r hr v₀ hv₀
  let e := elementaryEquiv K (r + 1)
  refine ⟨e.symm (a * b⁻¹), ?_⟩
  change CFSGProjectiveLinearPointAction.linearEquiv (e (e.symm (a * b⁻¹))).val v₀ = v
  rw [e.apply_symm_apply]
  change CFSGProjectiveLinearPointAction.linearEquiv (a.val * b.val⁻¹) v₀ = v
  rw [map_mul, map_inv]
  let la := CFSGProjectiveLinearPointAction.linearEquiv a.val
  let lb := CFSGProjectiveLinearPointAction.linearEquiv b.val
  change la (lb.symm v₀) = v
  have hb' : lb (Pi.single (Sum.inl (0 : Fin (r + 1))) 1) = v₀ := hb
  rw [← hb', lb.symm_apply_apply]
  exact ha

theorem elementaryImageAction_ker_charTwo (r : ℕ) (hr : 0 < r) :
    (elementaryImageAction K (r + 1)).ker = ⊥ :=
  CFSGNormalKernelFixedVector.kernel_eq_bot (elementaryImageAction K (r + 1))
    (restrictionRepresentation K (r + 1)) (restrictionRepresentation_injective K (r + 1))
    (Pi.single (Sum.inl (Fin.last r)) 1) (terminal_kernel_fixed K r)
    (restrictionRepresentation_nonzero_orbit K r hr)

def elementaryImageActionEquiv_charTwo (r : ℕ) (hr : 0 < r) :
    elementaryRootGroup K (r + 1) ≃* (elementaryImageAction K (r + 1)).range :=
  MonoidHom.ofInjective ((elementaryImageAction K (r + 1)).ker_eq_bot_iff.mp
    (elementaryImageAction_ker_charTwo K r hr))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
