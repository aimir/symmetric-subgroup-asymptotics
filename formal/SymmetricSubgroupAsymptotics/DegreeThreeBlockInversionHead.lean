import SymmetricSubgroupAsymptotics.BlockKernelSignCoordinates
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart
import SymmetricSubgroupAsymptotics.PrimeLayerVanishing
import SymmetricSubgroupAsymptotics.RelativeAmbientSubgroup
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.RelativeSecondIsomorphism
import SymmetricSubgroupAsymptotics.TernaryRelativeSignHead

/-!
# The inversion-image branch for blocks of degree three

Inside the literal original block kernel, intersect the kernels of all fibre
signs.  After relabelling each three-point fibre, every remaining coordinate
lies in the actual alternating group and hence has an explicit ternary chart.
The charts jointly separate the retained subgroup and conjugation acts on each
coordinate by the original binary sign.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeThreeBlockInversionHead

open OriginalBlockSignCoordinates OddMarkerTernaryChart

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
variable [∀ x : X, Fintype (originalBlockFibre b x)]

abbrev Kernel : Subgroup A := OriginalBlockSignCoordinates.Kernel (A := A) (X := X)

/-- Relabel the literal fibre permutation onto the fixed three-point chart. -/
def relabeledCoordinate (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    Kernel (A := A) (X := X) →* OddMarkerGroup :=
  (e x).symm.permCongrHom.toMonoidHom.comp
    (OriginalBlockClassBound.coordinate b hb x)

theorem relabeledCoordinate_sign
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x : X) (k : Kernel (A := A) (X := X)) :
    oddMarkerSign (relabeledCoordinate (hb := hb) b e x k) = coordinateSign b hb x k := by
  calc
    oddMarkerSign (relabeledCoordinate (hb := hb) b e x k) =
        permutationBinarySign (Fin 3) (relabeledCoordinate (hb := hb) b e x k) := by
      have binary_ext_one (u v : Multiplicative (ZMod 2))
          (huv : u = 1 ↔ v = 1) : u = v := by
        apply Multiplicative.toAdd.injective
        have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        rcases htwo u.toAdd with hu | hu <;> rcases htwo v.toAdd with hv | hv
        · exact hu.trans hv.symm
        · exfalso
          have huOne : u = 1 := Multiplicative.toAdd.injective (by simpa using hu)
          have hvNotOne : v ≠ 1 := by
            intro hvOne
            have := congrArg Multiplicative.toAdd hvOne
            simp [hv] at this
          exact hvNotOne (huv.mp huOne)
        · exfalso
          have huNotOne : u ≠ 1 := by
            intro huOne
            have := congrArg Multiplicative.toAdd huOne
            simp [hu] at this
          have hvOne : v = 1 := Multiplicative.toAdd.injective (by simpa using hv)
          exact huNotOne (huv.mpr hvOne)
        · exact hu.trans hv.symm
      apply binary_ext_one
      constructor
      · intro hm
        have hs := (oddMarkerSign_eq_one _).mp hm
        have hs' : @Equiv.Perm.sign (Fin 3)
            (fun a b => Classical.propDecidable (a = b)) _
            (relabeledCoordinate (hb := hb) b e x k) = 1 := by
          rw [← @Equiv.Perm.sign_eq_sign_of_equiv
            (Fin 3) (instDecidableEqFin 3) (Fin 3) inferInstance
            (fun a b => Classical.propDecidable (a = b)) inferInstance
            (relabeledCoordinate (hb := hb) b e x k)
            (relabeledCoordinate (hb := hb) b e x k)
            (Equiv.refl _) (fun _ => rfl)]
          exact hs
        exact (permutationBinarySign_eq_one (Fin 3) _).mpr hs'
      · intro hp
        have hs := (permutationBinarySign_eq_one (Fin 3) _).mp hp
        have hs' : @Equiv.Perm.sign (Fin 3) (instDecidableEqFin 3) _
            (relabeledCoordinate (hb := hb) b e x k) = 1 := by
          rw [@Equiv.Perm.sign_eq_sign_of_equiv
            (Fin 3) (instDecidableEqFin 3) (Fin 3) inferInstance
            (fun a b => Classical.propDecidable (a = b)) inferInstance
            (relabeledCoordinate (hb := hb) b e x k)
            (relabeledCoordinate (hb := hb) b e x k)
            (Equiv.refl _) (fun _ => rfl)]
          exact hs
        exact (oddMarkerSign_eq_one _).mpr hs'
    _ = permutationBinarySign (originalBlockFibre b x)
        (OriginalBlockClassBound.coordinate b hb x k) :=
      permutationBinarySign_permCongr (e x).symm
        (OriginalBlockClassBound.coordinate b hb x k)
    _ = coordinateSign b hb x k := rfl

/-- The actual subgroup on which every literal fibre permutation is even. -/
def evenKernel : Subgroup (Kernel (A := A) (X := X)) :=
  ⨅ x : X, (coordinateSign b hb x).ker

instance evenKernel_normal : (evenKernel b hb).Normal := by
  constructor
  intro l hl k
  apply Subgroup.mem_iInf.mpr
  intro x
  have hx := Subgroup.mem_iInf.mp hl x
  exact Subgroup.Normal.conj_mem inferInstance _ hx k

/-- All original fibre signs, retained simultaneously on the literal block
kernel. -/
def coordinateSigns : Kernel (A := A) (X := X) →*
    (X → Multiplicative (ZMod 2)) where
  toFun k x := coordinateSign b hb x k
  map_one' := by funext x; exact map_one (coordinateSign b hb x)
  map_mul' k l := by funext x; exact map_mul (coordinateSign b hb x) k l

theorem coordinateSigns_ker : (coordinateSigns b hb).ker = evenKernel b hb := by
  ext k
  constructor
  · intro hk
    apply Subgroup.mem_iInf.mpr
    intro x
    exact congrFun (MonoidHom.mem_ker.mp hk) x
  · intro hk
    apply MonoidHom.mem_ker.mpr
    funext x
    exact Subgroup.mem_iInf.mp hk x

/-- Every binary sign tuple has exponent two. -/
theorem binarySignFunctions_isPGroup :
    IsPGroup 2 (X → Multiplicative (ZMod 2)) := by
  intro f
  refine ⟨1, ?_⟩
  simp only [pow_one]
  funext x
  exact binary_mul_pow_two (f x)

/-- The all-even kernel has a literal elementary binary quotient, even when
the simultaneous sign image is a proper correlated subspace. -/
theorem quotient_evenKernel_isPGroup :
    IsPGroup 2 (Kernel (A := A) (X := X) ⧸ evenKernel b hb) := by
  have hker : IsPGroup 2
      (Kernel (A := A) (X := X) ⧸ (coordinateSigns b hb).ker) :=
    ((binarySignFunctions_isPGroup (X := X)).to_subgroup
    (coordinateSigns b hb).range).of_equiv
      (QuotientGroup.quotientKerEquivRange (coordinateSigns b hb)).symm
  exact hker.of_equiv
    (QuotientGroup.quotientMulEquivOfEq (coordinateSigns_ker b hb))

theorem evenKernel_coordinateSign (l : evenKernel b hb) (x : X) :
    coordinateSign b hb x (l : Kernel (A := A) (X := X)) = 1 := by
  exact Subgroup.mem_iInf.mp l.2 x

/-- Each relabelled even coordinate lands in the literal natural `A₃`. -/
def evenPermutationCoordinate
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    evenKernel b hb →* oddMarkerSign.ker :=
  ((relabeledCoordinate (hb := hb) b e x).comp (evenKernel b hb).subtype).codRestrict
    oddMarkerSign.ker (fun l => by
      change oddMarkerSign (relabeledCoordinate (hb := hb) b e x
        (l : Kernel (A := A) (X := X))) = 1
      rw [relabeledCoordinate_sign]
      exact evenKernel_coordinateSign b hb l x)

/-- Literal ternary rotation coordinate on the actual all-even kernel. -/
def evenTernaryCoordinate
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    evenKernel b hb →* Multiplicative (ZMod 3) :=
  OddMarkerTernaryChart.chart.symm.toMonoidHom.comp
    (evenPermutationCoordinate (hb := hb) b e x)

/-- The ternary coordinates retain every correlation but jointly separate
the original all-even subgroup. -/
theorem evenTernaryCoordinates_injective
    [FaithfulSMul A Ω]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) :
    Function.Injective (fun l x => evenTernaryCoordinate (hb := hb) b e x l) := by
  intro l m hlm
  apply Subtype.ext
  apply OriginalBlockClassBound.coordinates_injective b hb
  funext x
  apply (e x).symm.permCongrHom.injective
  have hx := congrFun hlm x
  have hp := OddMarkerTernaryChart.chart.symm.injective hx
  exact congrArg Subtype.val hp

omit [∀ x : X, Fintype (originalBlockFibre b x)] in
/-- On a fixed fibre, conjugation inside the block kernel becomes literal
conjugation of the relabelled three-point permutations. -/
theorem relabeledCoordinate_conjugation
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x : X) (k : Kernel (A := A) (X := X))
    (l : Kernel (A := A) (X := X)) :
    relabeledCoordinate (hb := hb) b e x (k * l * k⁻¹) =
      relabeledCoordinate (hb := hb) b e x k *
        relabeledCoordinate (hb := hb) b e x l *
        (relabeledCoordinate (hb := hb) b e x k)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

/-- The subgroup-valued even coordinate carries literal conjugation to
literal conjugation inside the natural alternating group. -/
theorem evenPermutationCoordinate_conjugation
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x : X) (k : Kernel (A := A) (X := X))
    (l : evenKernel b hb) :
    evenPermutationCoordinate (hb := hb) b e x (MulAut.conjNormal k l) =
      MulAut.conjNormal (relabeledCoordinate (hb := hb) b e x k)
        (evenPermutationCoordinate (hb := hb) b e x l) := by
  apply Subtype.ext
  exact relabeledCoordinate_conjugation (hb := hb) b e x k
    (l : Kernel (A := A) (X := X))

/-- The actual ternary coordinate transforms by the original binary sign on
that same fibre. -/
theorem evenTernaryCoordinate_conjugation
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x : X) (k : Kernel (A := A) (X := X))
    (l : evenKernel b hb) :
    (evenTernaryCoordinate (hb := hb) b e x (MulAut.conjNormal k l)).toAdd =
      signScalar (coordinateSign b hb x k) •
        (evenTernaryCoordinate (hb := hb) b e x l).toAdd := by
  change (OddMarkerTernaryChart.chart.symm
      (evenPermutationCoordinate (hb := hb) b e x (MulAut.conjNormal k l))).toAdd = _
  rw [evenPermutationCoordinate_conjugation (hb := hb) b e x k l]
  have hchart := OddMarkerTernaryChart.chart_symm_conjugate
    (relabeledCoordinate (hb := hb) b e x k)
      (evenPermutationCoordinate (hb := hb) b e x l)
  rw [smul_eq_mul, ← relabeledCoordinate_sign (hb := hb) b e x k]
  exact hchart

/-- Additive form of a literal ternary fibre coordinate. -/
def evenTernaryAdditiveCoordinate
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    Additive (evenKernel b hb) →+ ZMod 3 :=
  (evenTernaryCoordinate (hb := hb) b e x).toAdditive

/-- The literal ternary coordinate descends to an equivariant linear
coordinate on the actual elementary 3-abelianization of the all-even kernel. -/
def evenPrimeCoordinate [Finite A]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    (primeAbelianizationRepresentation 3
      (normalChainSourceAction (evenKernel b hb))).IntertwiningMap
        (ternarySignRepresentation (A := ZMod 3) (coordinateSign b hb x)) where
  toLinearMap := primeAbelianizationLift 3 (evenKernel b hb)
    (evenTernaryAdditiveCoordinate (hb := hb) b e x)
  isIntertwining' := fun k => by
    apply LinearMap.ext
    intro v
    obtain ⟨l, rfl⟩ := primeAbelianizationMap_surjective 3 (evenKernel b hb) v
    change primeAbelianizationLift 3 (evenKernel b hb)
        (evenTernaryAdditiveCoordinate (hb := hb) b e x)
        (primeAbelianizationRepresentation 3
          (normalChainSourceAction (evenKernel b hb)) k
            (primeAbelianizationMap 3 (evenKernel b hb)
              (Additive.ofMul l.toMul))) =
      signScalar (coordinateSign b hb x k) •
        primeAbelianizationLift 3 (evenKernel b hb)
          (evenTernaryAdditiveCoordinate (hb := hb) b e x)
          (primeAbelianizationMap 3 (evenKernel b hb)
            (Additive.ofMul l.toMul))
    rw [primeAbelianizationRepresentation_eval,
      primeAbelianizationLift_apply, primeAbelianizationLift_apply]
    exact evenTernaryCoordinate_conjugation (hb := hb) b e x k l.toMul

/-- The descended linear coordinates still jointly separate the entire
elementary quotient; no direct-product decomposition is used. -/
theorem evenPrimeCoordinates_injective
    [Finite A] [FaithfulSMul A Ω]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) :
    Function.Injective (fun v x => evenPrimeCoordinate (hb := hb) b e x v) := by
  intro v w hvw
  obtain ⟨l, rfl⟩ := primeAbelianizationMap_surjective 3 (evenKernel b hb) v
  obtain ⟨m, rfl⟩ := primeAbelianizationMap_surjective 3 (evenKernel b hb) w
  have hlm : l = m := by
    apply evenTernaryCoordinates_injective (hb := hb) b e
    funext x
    apply Multiplicative.toAdd.injective
    have hx := congrFun hvw x
    change primeAbelianizationLift 3 (evenKernel b hb)
        (evenTernaryAdditiveCoordinate (hb := hb) b e x)
          (primeAbelianizationMap 3 (evenKernel b hb) l) =
      primeAbelianizationLift 3 (evenKernel b hb)
        (evenTernaryAdditiveCoordinate (hb := hb) b e x)
          (primeAbelianizationMap 3 (evenKernel b hb) m) at hx
    simpa only [primeAbelianizationLift_apply] using hx
  rw [hlm]

/-- Restrict the actual ternary fibre coordinates to an arbitrary retained
normal subgroup of the all-even kernel. -/
def restrictedTernaryCoordinate
    (N : Subgroup (Kernel (A := A) (X := X)))
    (hN : N ≤ evenKernel b hb)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    N →* Multiplicative (ZMod 3) :=
  (evenTernaryCoordinate (hb := hb) b e x).comp (Subgroup.inclusion hN)

/-- The restricted coordinates remain jointly injective on every proper
subdirect or diagonal retained subgroup. -/
theorem restrictedTernaryCoordinates_injective
    [FaithfulSMul A Ω]
    (N : Subgroup (Kernel (A := A) (X := X)))
    (hN : N ≤ evenKernel b hb)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) :
    Function.Injective (fun n x =>
      restrictedTernaryCoordinate (hb := hb) b N hN e x n) := by
  intro n m hnm
  apply Subgroup.inclusion_injective hN
  apply evenTernaryCoordinates_injective (hb := hb) b e
  exact hnm

/-- Conjugation by the whole literal block kernel still acts on each
restricted coordinate through that fibre's original binary sign. -/
theorem restrictedTernaryCoordinate_conjugation
    (N : Subgroup (Kernel (A := A) (X := X))) [N.Normal]
    (hN : N ≤ evenKernel b hb)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x : X) (k : Kernel (A := A) (X := X)) (n : N) :
    (restrictedTernaryCoordinate (hb := hb) b N hN e x
      (MulAut.conjNormal k n)).toAdd =
        signScalar (coordinateSign b hb x k) •
          (restrictedTernaryCoordinate (hb := hb) b N hN e x n).toAdd := by
  simpa only [restrictedTernaryCoordinate, MonoidHom.comp_apply] using
    evenTernaryCoordinate_conjugation (hb := hb) b e x k
      (Subgroup.inclusion hN n)

/-- Additive form of a restricted literal ternary coordinate. -/
def restrictedTernaryAdditiveCoordinate
    (N : Subgroup (Kernel (A := A) (X := X)))
    (hN : N ≤ evenKernel b hb)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    Additive N →+ ZMod 3 :=
  (restrictedTernaryCoordinate (hb := hb) b N hN e x).toAdditive

/-- Equivariant linear coordinate on the actual elementary 3-quotient of
an arbitrary retained normal subgroup. -/
def restrictedPrimeCoordinate [Finite A]
    (N : Subgroup (Kernel (A := A) (X := X))) [N.Normal]
    (hN : N ≤ evenKernel b hb)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) (x : X) :
    (primeAbelianizationRepresentation 3
      (normalChainSourceAction N)).IntertwiningMap
        (ternarySignRepresentation (A := ZMod 3) (coordinateSign b hb x)) where
  toLinearMap := primeAbelianizationLift 3 N
    (restrictedTernaryAdditiveCoordinate (hb := hb) b N hN e x)
  isIntertwining' := fun k => by
    apply LinearMap.ext
    intro v
    obtain ⟨n, rfl⟩ := primeAbelianizationMap_surjective 3 N v
    change primeAbelianizationLift 3 N
        (restrictedTernaryAdditiveCoordinate (hb := hb) b N hN e x)
        (primeAbelianizationRepresentation 3 (normalChainSourceAction N) k
          (primeAbelianizationMap 3 N (Additive.ofMul n.toMul))) =
      signScalar (coordinateSign b hb x k) •
        primeAbelianizationLift 3 N
          (restrictedTernaryAdditiveCoordinate (hb := hb) b N hN e x)
          (primeAbelianizationMap 3 N (Additive.ofMul n.toMul))
    rw [primeAbelianizationRepresentation_eval,
      primeAbelianizationLift_apply, primeAbelianizationLift_apply]
    exact restrictedTernaryCoordinate_conjugation (hb := hb) b N hN e x k n.toMul

/-- The restricted descended coordinates jointly separate the actual
elementary 3-quotient. -/
theorem restrictedPrimeCoordinates_injective
    [Finite A] [FaithfulSMul A Ω]
    (N : Subgroup (Kernel (A := A) (X := X))) [N.Normal]
    (hN : N ≤ evenKernel b hb)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) :
    Function.Injective (fun v x =>
      restrictedPrimeCoordinate (hb := hb) b N hN e x v) := by
  intro v w hvw
  obtain ⟨n, rfl⟩ := primeAbelianizationMap_surjective 3 N v
  obtain ⟨m, rfl⟩ := primeAbelianizationMap_surjective 3 N w
  have hnm : n = m := by
    apply restrictedTernaryCoordinates_injective (hb := hb) b N hN e
    funext x
    apply Multiplicative.toAdd.injective
    have hx := congrFun hvw x
    change primeAbelianizationLift 3 N
        (restrictedTernaryAdditiveCoordinate (hb := hb) b N hN e x)
          (primeAbelianizationMap 3 N n) =
      primeAbelianizationLift 3 N
        (restrictedTernaryAdditiveCoordinate (hb := hb) b N hN e x)
          (primeAbelianizationMap 3 N m) at hx
    simpa only [primeAbelianizationLift_apply] using hx
  rw [hnm]

/-- Nontrivial fibre inversion annihilates the complete relative ternary
head of every retained normal subgroup inside the translation kernel. -/
theorem restricted_primeRelativeCharacters_eq_zero
    [Finite A] [Fintype X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (N : Subgroup (Kernel (A := A) (X := X))) [N.Normal]
    (hN : N ≤ evenKernel b hb)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x₀ : X) (hx₀ : coordinateSign b hb x₀ ≠ 1) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  exact primeRelativeCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    (N := N) (fun _ : X => ZMod 3)
    (fun x => coordinateSign b hb x)
    (all_coordinateSigns_nontrivial b hb x₀ hx₀)
    (fun x => restrictedPrimeCoordinate (hb := hb) b N hN e x)
    (restrictedPrimeCoordinates_injective (hb := hb) b N hN e)

/-- The complete relative ternary head of any normal block-kernel core is
zero.  Its intersection with the all-even kernel is killed by the signed
C₃ coordinates, while the remaining quotient is a 2-group. -/
theorem blockKernelNormal_primeRelativeCharacters_eq_zero
    [Finite A] [Fintype X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (P : Subgroup (Kernel (A := A) (X := X))) [P.Normal]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x₀ : X) (hx₀ : coordinateSign b hb x₀ ≠ 1) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 P) = 0 := by
  let B : Subgroup (Kernel (A := A) (X := X)) := P ⊓ evenKernel b hb
  letI : B.Normal := inferInstance
  have hB : B ≤ evenKernel b hb := by
    intro z hz
    exact hz.2
  have hBzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 B) = 0 :=
    restricted_primeRelativeCharacters_eq_zero (hb := hb) b B hB e x₀ hx₀
  have hEvenQuotient : IsPGroup 2
      (Kernel (A := A) (X := X) ⧸ evenKernel b hb) :=
    quotient_evenKernel_isPGroup b hb
  have hImage : IsPGroup 2 (normalChainQuotient (evenKernel b hb) P) :=
    hEvenQuotient.to_subgroup (normalChainQuotient (evenKernel b hb) P)
  have hQuotient : IsPGroup 2 (normalChainQuotient B P) := by
    exact hImage.of_equiv (relativeSecondIsomorphism P (evenKernel b hb)).symm
  have hQzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (normalChainQuotient B P)) = 0 :=
    primeRelativeHead_power_group 3 (normalChainQuotient B P) 2 (by decide) hQuotient
  have hchain := primeRelativeHead_chain_le B P 3 inf_le_left
  rw [hBzero, hQzero] at hchain
  exact Nat.eq_zero_of_le_zero hchain

/-- The physical intersection of an original normal subgroup with the
literal block kernel also has zero head under the whole original ambient
group. -/
theorem originalIntersection_primeRelativeCharacters_eq_zero
    [Finite A] [Fintype X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x₀ : X) (hx₀ : coordinateSign b hb x₀ ≠ 1) :
    Module.finrank (ZMod 3)
      (primeRelativeCharacters 3
        (N ⊓ Kernel (A := A) (X := X))) = 0 := by
  let P : Subgroup (Kernel (A := A) (X := X)) :=
    N.subgroupOf (Kernel (A := A) (X := X))
  letI : P.Normal := inferInstance
  have hPzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 P) = 0 :=
    blockKernelNormal_primeRelativeCharacters_eq_zero
      (hb := hb) b P e x₀ hx₀
  have hle := primeRelativeHead_inf_le_subgroupOf 3 N
    (Kernel (A := A) (X := X))
  change Module.finrank (ZMod 3)
      (primeRelativeCharacters 3
        (N ⊓ Kernel (A := A) (X := X))) ≤
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 P) at hle
  rw [hPzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- In the nontrivial inversion-image branch, the original normal pair's
entire ternary head is bounded by its actual normal image in the top block
action. -/
theorem originalNormal_primeRelativeHead_le_top
    [Finite A] [Fintype X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x₀ : X) (hx₀ : coordinateSign b hb x₀ ≠ 1) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      Module.finrank (ZMod 3)
        (primeRelativeCharacters 3
          (originalNormalRange
            (OriginalBlockClassBound.topMap (A := A) (X := X)) N)) := by
  let K := Kernel (A := A) (X := X)
  have hkernel : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ K)) = 0 :=
    originalIntersection_primeRelativeCharacters_eq_zero (hb := hb) b N e x₀ hx₀
  have hchain := primeRelativeHead_chain_le (N ⊓ K) N 3 inf_le_left
  rw [hkernel, primeRelativeHead_second_isomorphism 3 N K,
    primeRelativeHead_original_range 3
      (OriginalBlockClassBound.topMap (A := A) (X := X)) N] at hchain
  simpa only [zero_add] using hchain

/-- Numerical endpoint used by the degree-27 mixed case: a top relative
head at most two forces the full original relative head to be at most two,
and therefore strictly below the `3/20` line in degree 27. -/
theorem originalNormal_degreeTwentySeven_inversion_safe
    [Finite A] [Fintype X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x₀ : X) (hx₀ : coordinateSign b hb x₀ ≠ 1)
    (htop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3
        (originalNormalRange
          (OriginalBlockClassBound.topMap (A := A) (X := X)) N)) ≤ 2) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 ∧
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3 * 27 := by
  have hhead := (originalNormal_primeRelativeHead_le_top (hb := hb)
    b N e x₀ hx₀).trans htop
  exact ⟨hhead, by omega⟩

/-- A nontrivial inversion image on one fibre annihilates the complete
ternary relative head of the literal all-even kernel.  Transitivity spreads
the sign to every fibre, while the actual C₃ coordinates retain all diagonal
and subdirect correlations. -/
theorem evenKernel_primeRelativeCharacters_eq_zero
    [Finite A] [Fintype X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (x₀ : X) (hx₀ : coordinateSign b hb x₀ ≠ 1) :
    Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (evenKernel b hb)) = 0 := by
  exact primeRelativeCharacterHead_eq_zero_of_nontrivial_sign_coordinates
    (N := evenKernel b hb) (fun _ : X => ZMod 3)
    (fun x => coordinateSign b hb x)
    (all_coordinateSigns_nontrivial b hb x₀ hx₀)
    (fun x => evenPrimeCoordinate (hb := hb) b e x)
    (evenPrimeCoordinates_injective (hb := hb) b e)

end DegreeThreeBlockInversionHead
end SymmetricSubgroupAsymptotics

end
