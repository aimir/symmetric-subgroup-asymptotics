import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! All distinct simple roots in the actual norm-two base have Cartan
entry zero or minus one. Thus the two checked collecting cases exhaust
the other simple positive generators; no Cartan-case premise remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOffDiagonalCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoPairingBounds
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem cartan_eq_integer_pairing (i j : Fin r) :
    cartan b s i j=integerPairing A (s j:Roots A).val (s i:Roots A).val := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  change algebraMap ℤ ℚ (b.cartanMatrixIn ℤ (s j) (s i))=_
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply,pairing_cast]

theorem cartan_zero_or_neg_one (i j : Fin r) (hne : i≠j) :
    cartan b s i j=0 ∨ cartan b s i j= -1 := by
  have hsupport : s j≠s i := fun h=>hne (s.injective h).symm
  have hroots : (s j:Roots A)≠(s i:Roots A) :=
    fun h=>hsupport (Subtype.ext h)
  have hopp : (s j:Roots A).val≠ -(s i:Roots A).val := by
    intro h
    apply b.root_ne_neg_of_ne (s j).property (s i).property hroots
    change castVector (s j:Roots A).val= -castVector (s i:Roots A).val
    simpa only [castVector,Pi.neg_apply,Int.cast_neg] using congrArg castVector h
  have hb := root_pairing_interior A hs hp (s j) (s i) hroots hopp
  have hnonpos := b.cartanMatrix_le_zero_of_ne (s j) (s i) hsupport
  change cartan b s i j ≤ 0 at hnonpos
  simp only [cartan_eq_integer_pairing A hs hp b s] at hnonpos ⊢
  omega

theorem distinct_simple_conjugate_mem_positive (K : Type) [Field K]
    (i j : Fin r) (hne : i≠j) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈
        rootGroup A hs hp b s K false := by
  rcases cartan_zero_or_neg_one A hs hp b s i j hne with hz|hn
  · exact CFSGNormTwoGeckOrthogonalCollecting.orthogonal_conjugate_mem_positive
      A hs hp b s K i j hz a
  · exact CFSGNormTwoGeckPositiveCollecting.adjacent_conjugate_mem_positive
      A hs hp b s K i j hn a

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOffDiagonalCollecting
