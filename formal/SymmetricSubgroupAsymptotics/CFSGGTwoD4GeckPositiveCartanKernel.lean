import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckCartanDiagonals
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLeadingKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveGeneration

/-! Both actual folded G2 Cartans have trivial centralizer in the
ENTIRE ambient D4 positive group. Integer leading root degrees are
separated before reduction; the proved primitive two-Cartan weights
kill every height parameter in all characteristics. This gives positive
injectivity for the SAME original G2 cubic integral-image action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPositiveCartanKernel
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckCartanDiagonals
open CFSGGTwoD4GeckFoldedWeights CFSGGTwoD4GeckImageRealization CFSGFFourGradedCartanAction
open CFSGTrialityD4NormTwo CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckHeightQuotientTwist CFSGTrialityGeckFixedPositiveGeneration
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateHeightLayerFactorization
open CFSGNormTwoCoordinateHeightLeadingKernel CFSGNormTwoCoordinateRootHeightSupport
open CFSGNormTwoCoordinateRootCoefficientCoordinates CFSGNormTwoCoordinateRootBracketTransport
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixSupport
open CFSGNormTwoCoordinateRootHeightFiltration CFSGNormTwoCoordinateRootHeightBound

private def scalarWeight : GeckIndex → ℤ :=
  CFSGNormTwoCoordinateRootHeightLeading.heightWeight (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)

private def coefficient (K : Type) [Field K] (k : Roots (CartanMatrix.D 4)) : Matrix GeckIndex GeckIndex K :=
  selectedFieldCoefficient (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k

private theorem coefficient_support (K : Type) [Field K] (k : Roots (CartanMatrix.D 4)) :
    Supported rootWeight (fun v=>v+k.val) (coefficient K k) :=
  selectedFieldCoefficient_support (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k

private theorem coefficient_ne_zero (K : Type) [Field K] (k : Roots (CartanMatrix.D 4)) :
    coefficient K k≠0 :=
  selectedFieldCoefficient_ne_zero (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k

theorem commuting_cartans_next_tail (K : Type) [Field K] (u : Positive K)
    (hc : ∀i : Fin 2,Commute (u.val : Matrix GeckIndex GeckIndex K) (fieldCartan K i))
    (h : ℤ) (hh : 0<h) (hu : u∈TailInPositive K h) :
    u∈TailInPositive K (h+1) := by
  obtain ⟨c,y,hy,he⟩ := heightTailInPositive_factor (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h hh u hu
  have hlead : degreePart
      scalarWeight h
      ((u.val : Matrix GeckIndex GeckIndex K)-1) =
      ∑k : ExactHeightRoot (CartanMatrix.D 4) h,c k • coefficient K k.val.val := by
    rw [he]
    exact factored_height_leading (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h hh c y hy
  have hz (k : ExactHeightRoot (CartanMatrix.D 4) h) : c k=0 := by
    obtain ⟨i,hi⟩ := exists_foldedWeight_ne_zero K k.val
    have hm := hc i
    rw [fieldCartan_eq_diagonal] at hm
    have hdev : Commute (cartanDiagonal (K:=K) rootWeight (cartanFunctional i))
        ((u.val : Matrix GeckIndex GeckIndex K)-1) := by
      change cartanDiagonal (K:=K) rootWeight (cartanFunctional i) *
          ((u.val : Matrix GeckIndex GeckIndex K)-1) =
        ((u.val : Matrix GeckIndex GeckIndex K)-1) * cartanDiagonal (K:=K) rootWeight (cartanFunctional i)
      simp only [mul_sub,sub_mul,mul_one,one_mul]
      exact congrArg (fun M : Matrix GeckIndex GeckIndex K=>M-
        cartanDiagonal (K:=K) rootWeight (cartanFunctional i)) hm.eq.symm
    have hbr := degreePart_lie_zero_of_commute
      scalarWeight h
      (fun a : GeckIndex=>(cartanFunctional i (rootWeight a) : K))
      ((u.val : Matrix GeckIndex GeckIndex K)-1) hdev
    change ⁅cartanDiagonal (K:=K) rootWeight (cartanFunctional i),
      degreePart scalarWeight h
        ((u.val : Matrix GeckIndex GeckIndex K)-1)⁆=0 at hbr
    rw [hlead] at hbr
    exact homogeneous_coordinate_zero rootWeight (cartanFunctional i)
      (fun j : ExactHeightRoot (CartanMatrix.D 4) h=>j.val.val.val)
      (fun _ _ he=>Subtype.ext (Subtype.ext (Subtype.ext he)))
      (fun j=>coefficient K j.val.val) (fun j=>coefficient_support K j.val.val)
      c hbr k (coefficient_ne_zero K k.val.val) hi
  apply (height_leading_zero_iff_next_tail (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h hh u hu).mp
  exact hlead.trans (by
    simp only [hz,zero_smul,Finset.sum_const_zero]
    rfl)

theorem positive_cartan_centralizer_trivial (K : Type) [Field K] (u : Positive K)
    (hc : ∀i : Fin 2,Commute (u.val : Matrix GeckIndex GeckIndex K) (fieldCartan K i)) : u=1 := by
  have ht : ∀n : ℕ,u∈TailInPositive K ((n : ℤ)+1) := by
    intro n
    induction n with
    | zero =>
      change u∈TailInPositive K 1
      rw [first_tail_eq_top]
      exact Subgroup.mem_top u
    | succ n ih =>
      have he := commuting_cartans_next_tail K u hc ((n : ℤ)+1) (by omega) ih
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using he
  have hu := ht (rootHeightBound (CartanMatrix.D 4))
  rw [terminal_tail_eq_bot] at hu
  exact Subgroup.mem_bot.mp hu

theorem image_kernel_eq_one_of_positive (K : Type) [Field K]
    (g : foldedGroup K)
    (hg : g∈(foldedImageAction K).ker) (hu : g.val∈Positive K) : g=1 := by
  let u : Positive K := ⟨g.val,hu⟩
  have he : u=1 := positive_cartan_centralizer_trivial K u
    (fun i=>image_kernel_commutes_cartan K g hg i)
  apply Subtype.ext
  have hv := congrArg (fun z : Positive K=>z.val) he
  change g.val=1 at hv
  exact hv

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPositiveCartanKernel
