import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExcludedHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! The literal positive complement at node i is exactly the vanishing
locus of the i-th actual first coordinate. The proof uses its genuine
excluded-height support and the proved positive factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementKernel
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckColumns
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveComplement
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoGeckComplementGrading
open CFSGNormTwoCoordinateExcludedHeight CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateLeadingHom CFSGGradedMatrixSubgroups
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "U" => rootGroup A hs hp b₀ s₀ K false
local notation "M" => positiveComplement A hs hp b₀ s₀ K

theorem complement_leading_zero (i : Fin r)
    (v : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) (hv : v∈M i) :
    leadingCoordinates A hd hs hp ho K v i=0 := by
  have hstrict := complement_le_strict A hs hp b₀ s₀ (excludedHeight i) i
    (excluded_simple_zero A hd hs hp ho i)
    (fun j hij=>excluded_other_positive A hd hs hp ho i j hij) K hv
  have hle : weight A hs hp b₀ (excludedHeight i) (Sum.inl (s₀ i))≤
      weight A hs hp b₀ (excludedHeight i) (Sum.inr (negativeIndex A hs hp (s₀ i))) := by
    change 0≤excludedHeight i (negativeIndex A hs hp (s₀ i)).val
    simpa only [negative_val,map_neg,excluded_simple_zero A hd hs hp ho i,neg_zero]
      using (le_refl (0:ℤ))
  have he := hstrict (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i))) hle
  change (v : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)
    (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=0
  simpa only [Matrix.one_apply,Sum.inl_ne_inr,if_false] using he

theorem positive_mem_complement_iff_leading_zero (i : Fin r) (u : U) :
    u.val∈M i↔leadingCoordinates A hd hs hp ho K u.val i=0 := by
  constructor
  · exact complement_leading_zero A hd hs hp ho K i u.val
  · intro hu
    obtain ⟨v,hv,a,he⟩ := positive_factor A hs hp b₀ s₀ K i u.val u.property
    have hvU := complement_le_positive A hs hp b₀ s₀ K i hv
    have hroot := congrArg (fun c : Multiplicative (Fin r→K)=>c.toAdd i)
      (leadingHom_positiveRoot A hd hs hp ho K i a)
    change leadingCoordinates A hd hs hp ho K (canonicalRoot D K false i a) i=
      (Pi.single i a : Fin r→K) i at hroot
    have hroot' : leadingCoordinates A hd hs hp ho K (canonicalRoot D K false i a) i=a := by
      simpa [Pi.single_apply] using hroot
    have hc := congrArg
      (fun g : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ=>
        leadingCoordinates A hd hs hp ho K g i) he
    change leadingCoordinates A hd hs hp ho K u.val i=
      leadingCoordinates A hd hs hp ho K (v*(positiveRoot A hd hs hp ho K i a).val) i at hc
    rw [leadingCoordinates_mul A hd hs hp ho K ⟨v,hvU⟩ (positiveRoot A hd hs hp ho K i a)] at hc
    change leadingCoordinates A hd hs hp ho K u.val i=
      leadingCoordinates A hd hs hp ho K v i+
        leadingCoordinates A hd hs hp ho K (canonicalRoot D K false i a) i at hc
    rw [complement_leading_zero A hd hs hp ho K i v hv,hroot',zero_add] at hc
    have ha : a=0 := hc.symm.trans hu
    rw [ha,canonicalRoot_zero,mul_one] at he
    rw [he]
    exact hv

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementKernel
