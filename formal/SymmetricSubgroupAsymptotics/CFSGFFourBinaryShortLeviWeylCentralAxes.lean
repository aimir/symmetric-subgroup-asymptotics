import SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviWeylRoots
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryCentralCoordinateWords
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergCharTwoRootRange
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute

/-! The literal short Weyl matrices swap the paired central coordinate
axes, with no extra central term. Internal reversal of the remaining
orthogonal pair is paid by actual root commutation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviWeylCentralAxes
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGFFourE6HeisenbergLeviRoots
open CFSGFFourE6RelativeWords CFSGFFourE6PositiveRootUnits
open CFSGNormTwoCoordinateWordRootElementSign CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateSelectedRootElement CFSGTwistedE6RelativeWeylOrbits
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourBinaryShortLeviWeylRoots CFSGFFourBinaryCentralCoordinateWords
open CFSGExceptionalHeisenbergCharTwoRootRange CFSGExceptionalHeisenbergProduct
local instance fFourShortWeylCentralRootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev U (K : Type) [CommRing K] := (Matrix Index Index K)ˣ
private abbrev param (K : Type) [CommRing K] (k : Roots A) (t : K) : U K :=
  selectedRootElement A hd hs hp ho K k t
private abbrev py (K : Type) [CommRing K] (i : Fin 10) (t : K) : U K :=
  yNegative A hd hs hp ho configuration K i (Multiplicative.ofAdd t)
private def node : Fin 2 → Fin 4 := ![0,1]
private abbrev pairWord (K : Type) [CommRing K] (second : Bool) (i : Fin 3) (t : K) : U K :=
  param K (pairedRoot second i 0) t * param K (pairedRoot second i 1) t
private theorem paired_pairing (second : Bool) (i : Fin 3) :
    integerPairing A (pairedRoot second i 0).val (pairedRoot second i 1).val=0 := by
  cases second
  · exact (paired_roots_orthogonal i).1
  · exact (paired_roots_orthogonal i).2
private theorem short_weyl_pair (K : Type) [Field K] [CharP K 2]
    (second : Bool) (n : Fin 2) (i : Fin 3) (t : K) :
    canonicalWeyl realizationData K (node n) * pairWord K second i t *
      (canonicalWeyl realizationData K (node n))⁻¹ = pairWord K second (swapIndex n i) t := by
  let g : U K := canonicalWeyl realizationData K (node n)
  have h0 : g*param K (pairedRoot second i 0) t*g⁻¹ =
      param K (pairedRoot second (swapIndex n i) (swapFactor n i 0)) t :=
    short_weyl_conjugate_root K second n i 0 t
  have h1 : g*param K (pairedRoot second i 1) t*g⁻¹ =
      param K (pairedRoot second (swapIndex n i) (swapFactor n i 1)) t :=
    short_weyl_conjugate_root K second n i 1 t
  change g*(param K (pairedRoot second i 0) t*param K (pairedRoot second i 1) t)*g⁻¹ = _
  calc
    _=(g*param K (pairedRoot second i 0) t*g⁻¹)*
        (g*param K (pairedRoot second i 1) t*g⁻¹) := by group
    _=param K (pairedRoot second (swapIndex n i) (swapFactor n i 0)) t *
        param K (pairedRoot second (swapIndex n i) (swapFactor n i 1)) t := by rw [h0,h1]
    _=pairWord K second (swapIndex n i) t := by
      by_cases hi : i=(![2,0] : Fin 2 → Fin 3) n
      · simp only [swapFactor,if_pos hi]
        change param K (pairedRoot second (swapIndex n i) 1) t *
          param K (pairedRoot second (swapIndex n i) 0) t = _
        exact (CFSGNormTwoCoordinateRootPairCommute.pair_commute A hd hs hp ho K
          (pairedRoot second (swapIndex n i) 0) (pairedRoot second (swapIndex n i) 1)
          (Or.inl (paired_pairing second (swapIndex n i))) t t).eq.symm
      · simp only [swapFactor,if_neg hi]

theorem short_weyl_central_first (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (i : Fin 3) (t : K) :
    canonicalWeyl realizationData K (node n) *
      centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single i t,0))) *
      (canonicalWeyl realizationData K (node n))⁻¹ =
        centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single (swapIndex n i) t,0))) := by
  have hchart (j : Fin 3) : centralMatrixHom K (Multiplicative.ofAdd (0,(Pi.single j t,0))) =
      pairWord K false j t := by
    rw [central_first_word]
    rfl
  rw [hchart,hchart]
  exact short_weyl_pair K false n i t

theorem short_weyl_central_second (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (i : Fin 3) (t : K) :
    canonicalWeyl realizationData K (node n) *
      centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single i t))) *
      (canonicalWeyl realizationData K (node n))⁻¹ =
        centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single (swapIndex n i) t))) := by
  have hy (j : Fin 10) : py K j t=param K (configuration.yRoot j).val t :=
    DFunLike.congr_fun (yNegative_eq_selectedRootHom A hd hs hp ho configuration K j)
      (Multiplicative.ofAdd t)
  have hchart (j : Fin 3) : centralMatrixHom K (Multiplicative.ofAdd (0,(0,Pi.single j t))) =
      pairWord K true j t := by
    rw [central_second_word]
    change py K (pairPick j) t*py K (partner (pairPick j)) t = _
    rw [hy,hy]
    rfl
  rw [hchart,hchart]
  exact short_weyl_pair K true n i t

private def step (j : Fin 6) (v : Fin 6 → ℤ) : Fin 6 → ℤ :=
  v-integerPairing A v (Pi.single j (1 : ℤ)) • Pi.single j (1 : ℤ)
private theorem central_word (n : Fin 2) :
    wordRoot A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) (orbitWord (node n)) configuration.zRoot.val =
        configuration.zRoot.val := by
  apply Subtype.ext
  fin_cases n
  · change step 0 (step 5 configuration.z)=configuration.z
    decide
  · change step 2 (step 4 configuration.z)=configuration.z
    decide

theorem short_weyl_central_scalar (K : Type) [Field K] [CharP K 2]
    (n : Fin 2) (c : K) :
    canonicalWeyl realizationData K (node n) *
      centralMatrixHom K (Multiplicative.ofAdd (c,(0,0))) *
      (canonicalWeyl realizationData K (node n))⁻¹ =
        centralMatrixHom K (Multiplicative.ofAdd (c,(0,0))) := by
  have hchart : centralMatrixHom K (Multiplicative.ofAdd (c,(0,0))) =
      param K configuration.zRoot.val c := central_scalar_word K c
  obtain ⟨e,he,htransport⟩ := word_selected_root_sign A hd hs hp ho
    (orbitWord (node n)) configuration.zRoot.val
  have hsign : (e : K)=1 := by
    rcases he with rfl | rfl <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  have ht := htransport K c
  rw [central_word,hsign,one_mul] at ht
  calc
    _=canonicalWeyl realizationData K (node n) * param K configuration.zRoot.val c *
        (canonicalWeyl realizationData K (node n))⁻¹ :=
      congrArg (fun y : U K => canonicalWeyl realizationData K (node n) * y *
        (canonicalWeyl realizationData K (node n))⁻¹) hchart
    _=param K configuration.zRoot.val c := by
      rw [foldedWeyl_eq_orbitWord]
      exact ht
    _=_ := hchart.symm

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryShortLeviWeylCentralAxes
