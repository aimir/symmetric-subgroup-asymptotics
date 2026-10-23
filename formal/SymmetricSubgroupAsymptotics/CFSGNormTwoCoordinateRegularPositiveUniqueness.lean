import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularLeadingBorel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularLeadingWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover

/-! A positive element with every simple leading coordinate nonzero
belongs to a unique conjugate of the actual positive group. The proof
uses the literal Bruhat cover and graded matrix support, without an
assumed BN-pair, group recognition, or a regular-unipotent theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularPositiveUniqueness
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelNormalization
open CFSGNormTwoCoordinateBruhatCover CFSGNormTwoCoordinateRegularLeadingWord
open CFSGNormTwoCoordinateRegularLeadingBorel
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev Mat (K : Type) := Matrix ((b₀).support ⊕ Roots A) ((b₀).support ⊕ Roots A) K

theorem mem_normalizer_of_regular_conjugate (K : Type) [Field K] [Finite K]
    (g u : (Mat A hd hs hp ho K)ˣ)
    (hg : g ∈ canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K)
    (hu : u ∈ rootGroup A hs hp b₀ s₀ K false)
    (hreg : ∀ i, leadingCoordinates A hd hs hp ho K u i ≠ 0)
    (hgu : g⁻¹ * u * g ∈ rootGroup A hs hp b₀ s₀ K false) :
    g ∈ Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _) := by
  obtain ⟨w, b, hb, c, hc, he⟩ := canonical_bruhat_cover A hd hs hp ho K g hg
  let U := rootGroup A hs hp b₀ s₀ K false
  let N := Subgroup.normalizer (U : Set (Mat A hd hs hp ho K)ˣ)
  have hbN : b ∈ N := borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hb
  have hcN : c ∈ N := borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K hc
  let v := c * (g⁻¹ * u * g) * c⁻¹
  have hv : v ∈ U := (Subgroup.mem_normalizer_iff.mp hcN _).mp hgu
  have hword : wordUnit A hs hp b₀ s₀ K w * v *
      (wordUnit A hs hp b₀ s₀ K w)⁻¹ = b⁻¹ * u * b := by
    dsimp only [v]
    rw [he]
    group
  have hwN : wordUnit A hs hp b₀ s₀ K w ∈ N := by
    apply regular_leading_word_mem_normalizer A hd hs hp ho K w v hv
    intro i
    rw [hword]
    exact borel_conjugate_regular A hd hs hp ho K b u hb hu hreg i
  rw [he]
  exact N.mul_mem (N.mul_mem hbN hwN) hcN

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRegularPositiveUniqueness
