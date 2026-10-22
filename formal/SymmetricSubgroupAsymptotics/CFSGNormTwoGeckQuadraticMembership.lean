import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementGrading
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit

/-! Actual positive-group membership plus homogeneous quadratic degree
detects the original simple-root factor or complement. These are local
steps for the Weyl-word induction; positive membership is not assumed
for an arbitrary word by this module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadraticMembership
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckPositiveComplement CFSGNormTwoGeckComplementNormalizer
open CFSGNormTwoGeckComplementGrading CFSGSerreQuadraticMatrix
open CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups CFSGGradedQuadraticUnit
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem height_latticeWeight (height : (n→ℤ)→ₗ[ℤ]ℤ) (j : b.support⊕Roots A) :
    height (latticeWeight A hs hp b j)=weight A hs hp b height j := by
  cases j with
  | inl j=>exact map_zero height
  | inr j=>rfl

theorem quadratic_strict (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : 0<height d) :
    g∈strictUnits (weight A hs hp b height) := by
  have hh := strict_of_height_positive (latticeWeight A hs hp b) d
    height.toAddMonoidHom g hg hd
  intro j k hjk
  apply hh j k
  change height (latticeWeight A hs hp b j)≤height (latticeWeight A hs hp b k)
  rw [height_latticeWeight,height_latticeWeight]
  exact hjk

theorem quadratic_preserves (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : height d=0) :
    g∈preservingUnits (weight A hs hp b height) := by
  have hh := preserves_of_height_zero (latticeWeight A hs hp b) d
    height.toAddMonoidHom g hg hd
  intro j k hjk
  apply hh j k
  change height (latticeWeight A hs hp b j)≠height (latticeWeight A hs hp b k)
  rw [height_latticeWeight,height_latticeWeight]
  exact hjk

theorem positive_quadratic_mem_complement (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : 0<height d) :
    g∈positiveComplement A hs hp b s K i :=
  positive_mem_complement_of_strict A hs hp b s height i hi hother K g hg
    (quadratic_strict A hs hp b height K d g hgrade hd)

theorem positive_quadratic_mem_simple (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : height d=0) :
    g∈canonicalRootSubgroup (realizationData A hs hp b s) K false i :=
  positive_mem_simple_of_preserves A hs hp b s height i hi hother K g hg
    (quadratic_preserves A hs hp b height K d g hgrade hd)

theorem weyl_conjugate_positive (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : 0<height d) :
    canonicalWeyl (realizationData A hs hp b s) K i*g*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈rootGroup A hs hp b s K false := by
  have hV := positive_quadratic_mem_complement A hs hp b s height i hi hother K d g hg hgrade hd
  have hh := (Subgroup.mem_normalizer_iff.mp
    (weyl_mem_normalizer A hs hp b s K i) g).mp hV
  exact complement_le_positive A hs hp b s K i hh

theorem weyl_inverse_conjugate_positive (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : 0<height d) :
    (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹*g*
      canonicalWeyl (realizationData A hs hp b s) K i∈rootGroup A hs hp b s K false := by
  have hV := positive_quadratic_mem_complement A hs hp b s height i hi hother K d g hg hgrade hd
  let V : Subgroup (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
    positiveComplement A hs hp b s K i
  let N : Subgroup (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
    Subgroup.normalizer (V : Set _)
  have hW : canonicalWeyl (realizationData A hs hp b s) K i∈N :=
    weyl_mem_normalizer A hs hp b s K i
  have hN : (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈N := N.inv_mem hW
  have hN' : (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈
      Subgroup.normalizer (V : Set _) := hN
  have hh := (Subgroup.mem_normalizer_iff.mp hN' g).mp hV
  simpa only [inv_inv] using complement_le_positive A hs hp b s K i hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadraticMembership
