import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterKernelBracketRootData
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareRootWordValues

/-! The five designated whole blocks for the inner commutator review.
All five are conjugates of the SAME outer parameter or middle four-cycle.
This file certifies their actual signed-root supports in characteristic two.
It asserts no five-block factorization and no new derived membership. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketFixedBlocks
open CFSGReeFFourInversionSuffixSignPilot CFSGIntegerMatrixPairing
open CFSGReeFFourMiddleSquareBracketRootData CFSGReeFFourMiddleSquareBracketRootRelations
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGReeFFourMiddleSquareRootWordValues
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateSelectedRootElement CFSGFFourE6PositiveRootUnits
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

/-- C,D,E, in that order. -/
def outerWord : Fin 3 → List (Fin 6) :=
  ![[2,4,3,2,4,3], [0,5,1,2,4,3,2,4,3],
    [2,4,3,2,4,3,0,5,1,2,4,3,2,4,3]]

/-- T,S, in that order. -/
def middleWord : Fin 2 → List (Fin 6) :=
  ![[2,4,3,2,4,3,0,5,1], [0,5,1,2,4,3,2,4,3,0,5,1]]

def outerVector : Fin 3 → Fin 3 → Fin 6 → ℤ :=
  ![![![1,0,1,1,1,0], ![0,0,1,1,1,1], ![0,1,1,2,1,0]],
    ![![0,1,1,1,1,1], ![1,1,1,1,1,0], ![1,1,1,2,1,1]],
    ![![0,1,1,2,1,1], ![1,1,1,2,1,0], ![1,1,2,2,2,1]]]

def middleVector : Fin 2 → Fin 4 → Fin 6 → ℤ :=
  ![![![1,0,1,1,0,0], ![0,0,0,1,1,1], ![0,1,1,1,1,0], ![1,1,2,3,2,1]],
    ![![0,1,1,1,0,0], ![0,1,0,1,1,0], ![1,0,1,1,1,1], ![1,2,2,3,2,1]]]

theorem root_properties :
    (∀ b i : Fin 3, integerPairing A (outerVector b i) (outerVector b i)=2 ∧
      ∀ t : Fin 6, 0≤outerVector b i t) ∧
    (∀ b : Fin 2, ∀ i : Fin 4,
      integerPairing A (middleVector b i) (middleVector b i)=2 ∧
      ∀ t : Fin 6, 0≤middleVector b i t) := by
  decide +kernel

private theorem outer_transport_certificate : ∀ b i : Fin 3, ∀ t : Fin 6,
    vectorWord (outerWord b)
      (Pi.single ((![0,5,1] : Fin 3 → Fin 6) i) (1 : ℤ)) t = outerVector b i t := by
  decide +kernel

private theorem middle_transport_certificate : ∀ b : Fin 2, ∀ i : Fin 4, ∀ t : Fin 6,
    vectorWord (middleWord b) (yVector i) t = middleVector b i t := by
  decide +kernel

theorem outer_transport (b i : Fin 3) :
    vectorWord (outerWord b)
      (Pi.single ((![0,5,1] : Fin 3 → Fin 6) i) (1 : ℤ)) = outerVector b i := by
  funext t
  exact outer_transport_certificate b i t

theorem middle_transport (b : Fin 2) (i : Fin 4) :
    vectorWord (middleWord b) (yVector i) = middleVector b i := by
  funext t
  exact middle_transport_certificate b i t

def outerRoot (b i : Fin 3) : Roots A := ⟨outerVector b i, (root_properties.1 b i).1⟩
def middleRoot (b : Fin 2) (i : Fin 4) : Roots A :=
  ⟨middleVector b i, (root_properties.2 b i).1⟩

variable (K : Type) [CommRing K] [CharP K 2]

abbrev outerParameter (b i : Fin 3) := selectedRootElement A hd hs hp ho K (outerRoot b i) 1
abbrev middleParameter (b : Fin 2) (i : Fin 4) :=
  selectedRootElement A hd hs hp ho K (middleRoot b i) 1

theorem outer_parameter_conjugate (b i : Fin 3) :
    (MulAut.conj (canonicalWord e6Data K (outerWord b)))
      (canonicalRoot e6Data K false ((![0,5,1] : Fin 3 → Fin 6) i) 1) =
        outerParameter K b i := by
  exact word_simple_one K (outerWord b) _ (outerRoot b i) (outer_transport b i)

theorem middle_parameter_conjugate (b : Fin 2) (i : Fin 4) :
    (MulAut.conj (canonicalWord e6Data K (middleWord b))) (yParameter K i 1) =
      middleParameter K b i := by
  exact selected_word_one K (middleWord b) (yRoot i) (middleRoot b i)
    (middle_transport b i)

def outerBlock (b : Fin 3) :=
  (MulAut.conj (canonicalWord e6Data K (outerWord b)))
    (canonicalRoot e6Data K false 0 1 * canonicalRoot e6Data K false 5 1 *
      canonicalRoot e6Data K false 1 1)

def middleBlock (b : Fin 2) :=
  (MulAut.conj (canonicalWord e6Data K (middleWord b))) (yWord K)

theorem outerBlock_eq (b : Fin 3) : outerBlock K b =
    outerParameter K b 0 * outerParameter K b 1 * outerParameter K b 2 := by
  have h0 := outer_parameter_conjugate K b 0
  have h1 := outer_parameter_conjugate K b 1
  have h2 := outer_parameter_conjugate K b 2
  change _ = outerParameter K b 0 at h0
  change _ = outerParameter K b 1 at h1
  change _ = outerParameter K b 2 at h2
  simp only [outerBlock, map_mul]
  exact congrArg₂ (fun a c => a*c) (congrArg₂ (fun a c => a*c) h0 h1) h2

private theorem map_four {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b c d : G) : f (a*b*c*d) = f a*f b*f c*f d := by
  rw [map_mul,map_mul,map_mul]

theorem middleBlock_eq (b : Fin 2) : middleBlock K b =
    middleParameter K b 0 * middleParameter K b 1 *
      middleParameter K b 2 * middleParameter K b 3 := by
  let F := (MulAut.conj (canonicalWord e6Data K (middleWord b))).toMonoidHom
  have h0 : F (yParameter K 0 1) = middleParameter K b 0 :=
    middle_parameter_conjugate K b 0
  have h1 : F (yParameter K 1 1) = middleParameter K b 1 :=
    middle_parameter_conjugate K b 1
  have h2 : F (yParameter K 2 1) = middleParameter K b 2 :=
    middle_parameter_conjugate K b 2
  have h3 : F (yParameter K 3 1) = middleParameter K b 3 :=
    middle_parameter_conjugate K b 3
  have hm := map_four F (yParameter K 0 1) (yParameter K 1 1)
    (yParameter K 2 1) (yParameter K 3 1)
  change F (yWord K) = _
  exact (congrArg F (yWord_eq K)).trans (hm.trans
    (congrArg₂ (fun a c => a*c)
      (congrArg₂ (fun a c => a*c) (congrArg₂ (fun a c => a*c) h0 h1) h2) h3))

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketFixedBlocks
