import SymmetricSubgroupAsymptotics.CFSGFFourBinaryActualNormalizerCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryPositiveLeviNativeCovariance
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviWeylNativeCovariance
import SymmetricSubgroupAsymptotics.CFSGConjugationGraphNormalLift
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryShortGeneration

/-! The actual F4 conjugation graph contains the required native
isotropic transvections. Its first image is kept literal; only displayed
positive roots and short Weyl words are lifted, and no full symplectic
image or complement is assumed. The second projection is faithful. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviConjugationGraph
open CFSGFFourBinaryActualNormalizerCoordinates CFSGFFourBinaryFoldedRadicalNormalizer
open CFSGFFourBinaryNativeCentralAction CFSGFFourBinaryLeviNativeVectorCoordinates
open CFSGFFourBinaryPositiveLeviNativeCovariance CFSGFFourBinaryLeviWeylNativeCovariance
open CFSGFFourBinaryCentralCoordinateWords CFSGFFourBinaryRadicalCentralLayers
open CFSGConjugationActionGraph CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGSymplecticBinaryPointTailAction
local instance fFourLeviGraphRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K=2)
private theorem range_element_lift {A B : Type} [Group A] [Group B]
    (f : A →* B) (b : f.range) : ∃ a : A, f a = b.val := b.property

private abbrev UnitsK := (Matrix Index Index K)ˣ
private abbrev Native := CFSGSymplecticSerreMatrices.elementaryRootGroup K 3

abbrev Graph := intertwiningPairs (nativeCentralAction K hK) (centralHom K)

def first : Graph K hK →* Native K :=
  (MonoidHom.fst (Native K) (Normalizer K)).comp (Graph K hK).subtype

def second : Graph K hK →* Normalizer K :=
  CFSGConjugationGraphNormalLift.second (nativeCentralAction K hK) (centralHom K)

theorem second_injective : Function.Injective (second K hK) :=
  CFSGConjugationGraphNormalLift.second_injective (nativeCentralAction K hK) (centralHom K)
    (nativeCentralAction_injective K hK) (centralHom_injective K)

private def positiveUnit (i : Fin 3) (a : K) : Normalizer K :=
  ⟨canonicalElementaryRoot realizationData K false i.castSucc a,positive_mem_normalizer K i a⟩
private def weylUnit (n : Fin 2) : Normalizer K :=
  ⟨foldedWeyl K n.castSucc,weyl_mem_normalizer K n.castSucc⟩

def positiveLift (i : Fin 3) (a : K) : Graph K hK :=
  ⟨(nativePositive K i a,positiveUnit K i a),by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    let g : UnitsK K := canonicalRoot realizationData K false i.castSucc a
    change g*centralMatrixHom K z =
      centralMatrixHom K (nativeCentralAction K hK (nativePositive K i a) z)*g
    have hcov : g*centralMatrixHom K z*g⁻¹ =
        centralMatrixHom K (nativeCentralAction K hK (nativePositive K i a) z) :=
      positive_central_covariance K hK i a z
    exact (mul_inv_eq_iff_eq_mul).mp hcov⟩

def weylLift (n : Fin 2) : Graph K hK :=
  ⟨(CFSGSymplecticSerreMatrices.simpleWeyl K 3 n.castSucc,weylUnit K n),by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    let g : UnitsK K := CFSGSerreQuadraticMatrix.canonicalWeyl realizationData K n.castSucc.castSucc
    change g*centralMatrixHom K z =
      centralMatrixHom K (nativeCentralAction K hK
        (CFSGSymplecticSerreMatrices.simpleWeyl K 3 n.castSucc) z)*g
    have hcov : g*centralMatrixHom K z*g⁻¹ =
        centralMatrixHom K (nativeCentralAction K hK
          (CFSGSymplecticSerreMatrices.simpleWeyl K 3 n.castSucc) z) := by
      fin_cases n
      · exact weyl_central_covariance K hK 0 z
      · exact weyl_central_covariance K hK 1 z
    exact (mul_inv_eq_iff_eq_mul).mp hcov⟩

private theorem first_positiveLift (i : Fin 3) (a : K) :
    first K hK (positiveLift K hK i a) = nativePositive K i a := rfl
private theorem first_weylLift (n : Fin 2) :
    first K hK (weylLift K hK n) = CFSGSymplecticSerreMatrices.simpleWeyl K 3 n.castSucc := rfl
private theorem positive_mem_first_range (i : Fin 3) (a : K) :
    CFSGSymplecticSerreMatrices.elementaryRoot K 3 false i a ∈ (first K hK).range :=
  ⟨positiveLift K hK i a,first_positiveLift K hK i a⟩
private theorem weyl_mem_first_range (i : Fin 3) (hi : i.val+1<3) :
    CFSGSymplecticSerreMatrices.simpleWeyl K 3 i ∈ (first K hK).range := by
  let n : Fin 2 := ⟨i.val,by omega⟩
  have hn : n.castSucc=i := Fin.ext rfl
  refine ⟨weylLift K hK n,?_⟩
  exact (first_weylLift K hK n).trans (congrArg (CFSGSymplecticSerreMatrices.simpleWeyl K 3) hn)

set_option maxHeartbeats 600000 in
theorem exists_Y_transvection (v : Fin 3 → K) :
    ∃ g : Graph K hK, ∀ x : (Fin 3 → K) × (Fin 3 → K),
      vectorLinearHom K 3 (first K hK g) x =
        BinaryQuadraticRefinementTransvections.transvectionMap (0,v) x := by
  obtain ⟨g,hg⟩ := CFSGSymplecticBinaryShortGeneration.exists_paired_Y_transvection
    K hK 2 (by decide) (first K hK).range
    (positive_mem_first_range K hK) (weyl_mem_first_range K hK) v
  obtain ⟨u,hu⟩ := range_element_lift (first K hK) g
  refine ⟨u,?_⟩
  intro x
  rw [hu]
  exact hg x

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviConjugationGraph
