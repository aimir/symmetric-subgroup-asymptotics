import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentPair
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! A normal subgroup containing ONE full positive simple root line is
the whole actual canonical matrix group. Actual Cartan connectivity and
the checked adjacent Weyl word propagate the line, in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalSimpleRootGeneration
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGGeckSerreRepresentation CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateDominantSupport CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoGeckAdjacentPair CFSGNormTwoGeckSelfRootConjugation
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

include hd hs hp ho
theorem offdiagonal_nonzero_eq_neg_one (i j : Fin r) (hij : i≠j) (hA : A i j≠0) : A i j= -1 := by
  have hne : (s₀ i : Roots A)≠(s₀ j : Roots A) := by
    intro he
    exact hij ((s₀).injective (Subtype.ext he))
  have hopp : (s₀ i : Roots A).val≠ -(s₀ j : Roots A).val := by
    intro he
    have hx := congrFun he i
    change (Pi.single i (1:ℤ) : Fin r→ℤ) i= -(Pi.single j (1:ℤ) : Fin r→ℤ) i at hx
    simp [Pi.single_apply,hij,Ne.symm hij] at hx
  have hi := root_pairing_interior A hs hp (s₀ i) (s₀ j) hne hopp
  have hentry : integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val=A i j := by
    change Matrix.toBilin' A (Pi.single i (1:ℤ)) (Pi.single j (1:ℤ))=A i j
    exact Matrix.toBilin'_single A i j
  rw [hentry] at hi
  have hn := ho i j hij
  omega

theorem normal_eq_top_of_simple_root_line (K : Type) [Field K]
    (N : Subgroup (ElementaryGroup A hd hs hp ho K)) [N.Normal] (i : Fin r)
    (hseed : ∀a : K,canonicalElementaryRoot D K false i a∈N) : N=⊤ := by
  have hpos : ∀j : Fin r,∀a : K,canonicalElementaryRoot D K false j a∈N := by
    intro j
    apply coordinate_cartan_induction A hd hs hp ho
      (fun j=>∀a : K,canonicalElementaryRoot D K false j a∈N) i j hseed
    intro a b ha hab
    by_cases heq : a=b
    · subst b
      exact ha
    have hba : A b a= -1 := offdiagonal_nonzero_eq_neg_one A hd hs hp ho b a (Ne.symm heq) hab
    have hab' : A a b= -1 := by
      have hs' : A a b=A b a := congrFun (congrFun hs b) a
      exact hs'.trans hba
    have hcAB : cartan b₀ s₀ a b= -1 := by
      change (b₀).cartanMatrix (s₀ b) (s₀ a)= -1
      rw [coordinate_cartan_transpose A hd hs hp ho]
      exact hab'
    have hcBA : cartan b₀ s₀ b a= -1 := by
      change (b₀).cartanMatrix (s₀ a) (s₀ b)= -1
      rw [coordinate_cartan_transpose A hd hs hp ho]
      exact hba
    intro t
    let w := elementaryWord A hd hs hp ho K [a,b]
    have hw : w.val=canonicalWeyl D K a*canonicalWeyl D K b := by
      change wordUnit A hs hp b₀ s₀ K [a,b]=_
      simp only [wordUnit,mul_one]
    have he : w*canonicalElementaryRoot D K false a t*w⁻¹=canonicalElementaryRoot D K false b t := by
      apply Subtype.ext
      change w.val*canonicalRoot D K false a t*w.val⁻¹=canonicalRoot D K false b t
      rw [hw]
      exact adjacent_pair_word A hs hp b₀ s₀ K a b hcAB hcBA t
    have hn := (inferInstance : N.Normal).conj_mem (canonicalElementaryRoot D K false a t) (ha t) w
    rw [he] at hn
    exact hn
  have hneg : ∀j : Fin r,∀a : K,canonicalElementaryRoot D K true j a∈N := by
    intro j a
    let w := elementaryWord A hd hs hp ho K [j]
    have hw : w.val=canonicalWeyl D K j := by
      change wordUnit A hs hp b₀ s₀ K [j]=_
      simp only [wordUnit,mul_one]
    have he : w*canonicalElementaryRoot D K false j (-a)*w⁻¹=canonicalElementaryRoot D K true j a := by
      apply Subtype.ext
      change w.val*canonicalRoot D K false j (-a)*w.val⁻¹=canonicalRoot D K true j a
      rw [hw]
      simpa only [neg_neg] using self_root_word A hs hp b₀ s₀ K j (-a)
    have hn := (inferInstance : N.Normal).conj_mem (canonicalElementaryRoot D K false j (-a)) (hpos j (-a)) w
    rw [he] at hn
    exact hn
  have hle : Subgroup.closure (elementaryRootSet K (canonicalRoot D K))≤N := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨neg,j,a,rfl⟩
    cases neg with
    | false=>exact hpos j a
    | true=>exact hneg j a
  rw [elementaryRootSet_generate] at hle
  exact top_unique hle

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalSimpleRootGeneration
