import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeParabolicIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagonalFactor
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! The full negative normalizer inside the actual elementary group can
replace the literal negative Borel in simple-root recovery. Diagonal
Weyl words are never assumed to belong to the generated torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeNormalizerIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateExcludedHeight CFSGNormTwoGeckHeightSupport
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckQuadraticMembership
open CFSGNormTwoGeckOppositionDegree CFSGNormTwoGeckFieldOpposition
open CFSGNormTwoGeckOppositionWeyl CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups
open CFSGGradedMatrixTriangularUnits CFSGNormTwoCoordinateOppositeParabolicIntersection
open CFSGNormTwoCoordinateNormalizerDiagonalFactor CFSGSubgroupConjugateOrbitCardinality
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "w(" i ")" => weight A hs hp b₀ (excludedHeight i)

theorem opposition_negative_eq_positive (K : Type) [Field K] :
    (rootGroup A hs hp b₀ s₀ K true).map
      (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom=
        rootGroup A hs hp b₀ s₀ K false := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    exact opposition_conjugate_mem A hs hp b₀ s₀ K true g hg
  · intro g hg
    refine ⟨_,opposition_conjugate_mem A hs hp b₀ s₀ K false g hg,?_⟩
    exact opposition_twice A hs hp b₀ K g

theorem opposition_elementary_eq_elementary (K : Type) [Field K] :
    (canonicalElementaryGroup D K).map
      (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom=canonicalElementaryGroup D K := by
  rw [←positive_sup_negative A hs hp b₀ s₀ K,Subgroup.map_sup,
    opposition_positive_eq_negative,opposition_negative_eq_positive,sup_comm]

theorem opposition_diagonal_preserving (K : Type) [Field K] (i : Fin r)
    (d : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hdiag : (d : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K).IsDiag) :
    oppositionUnit A hs hp b₀ K*d*(oppositionUnit A hs hp b₀ K)⁻¹∈preservingUnits w(i) := by
  have hO : Supported w(i) (fun z=> -z)
      (oppositionUnit A hs hp b₀ K : Matrix _ _ K) := by
    intro j k hjk
    apply opposition_lattice_support A hs hp b₀ K j k
    intro he
    apply hjk
    change CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp b₀ j=
      -CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp b₀ k at he
    have hh := congrArg (excludedHeight i) he
    simpa only [height_latticeWeight,map_neg] using hh
  have hOi : Supported w(i) (fun z=> -z)
      (↑((oppositionUnit A hs hp b₀ K)⁻¹) : Matrix _ _ K) := by
    rwa [opposition_inverse]
  have hD : Supported w(i) id (d : Matrix _ _ K) := by
    intro j k hjk
    apply hdiag
    intro he
    subst k
    exact hjk rfl
  apply supported_congr (supported_mul (supported_mul hO hD) hOi)
  intro z
  exact neg_neg z

theorem negative_normalizer_le_excluded_triangular (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (i : Fin r) :
    Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _)⊓canonicalElementaryGroup D K≤
      triangularUnits w(i) := by
  intro g hg
  let e := (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom
  have hN := Subgroup.le_normalizer_map e ⟨g,hg.1,rfl⟩
  rw [opposition_negative_eq_positive A hd hs hp ho K] at hN
  have hH : e g∈canonicalElementaryGroup D K := by
    rw [←opposition_elementary_eq_elementary A hd hs hp ho K]
    exact ⟨g,hg.2,rfl⟩
  obtain ⟨u,hu,d,hdD,he⟩ := normalizer_diagonal_factor A hd hs hp ho K ε hε hA hidentity
    (e g) hH hN
  have hge : g=e u*e d := by
    calc
      g=e (e g) := (opposition_twice A hs hp b₀ K g).symm
      _=e (u*d) := congrArg e he
      _=e u*e d := map_mul e u d
  rw [hge]
  apply (triangularUnits w(i)).mul_mem
  · exact negative_le_excluded_triangular A hd hs hp ho K i
      (opposition_conjugate_mem A hs hp b₀ s₀ K false u hu)
  · exact preserving_le_triangular _ (opposition_diagonal_preserving A hd hs hp ho K i d hdD)

theorem opposite_normalizer_parabolic_intersection (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (i : Fin r) :
    rootGroup A hs hp b₀ s₀ K false ⊓
      ((Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _)⊓canonicalElementaryGroup D K)⊔
        canonicalRootSubgroup D K false i)=canonicalRootSubgroup D K false i := by
  apply le_antisymm
  · have hP : (Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K true : Set _)⊓
        canonicalElementaryGroup D K)⊔canonicalRootSubgroup D K false i≤triangularUnits w(i) :=
      sup_le (negative_normalizer_le_excluded_triangular A hd hs hp ho K ε hε hA hidentity i)
        ((CFSGNormTwoGeckComplementGrading.simple_le_preserving A hs hp b₀ s₀
          (excludedHeight i) i (excluded_simple_zero A hd hs hp ho i) K).trans
            (preserving_le_triangular _))
    intro g hg
    apply coordinate_positive_mem_simple_of_preserves A hd hs hp ho i K g hg.1
    exact (triangular_inf_reverse_eq_preserving w(i)).le
      ⟨hP hg.2,positive_le_reverse_excluded_triangular A hd hs hp ho K i hg.1⟩
  · apply le_inf _ le_sup_right
    rintro g ⟨t,rfl⟩
    exact Subgroup.subset_closure ⟨(i,t),rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeNormalizerIntersection
