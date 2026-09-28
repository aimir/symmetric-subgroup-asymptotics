import SymmetricSubgroupAsymptotics.TransitiveTernaryHeadBound
import SymmetricSubgroupAsymptotics.DegreeTwentySevenClosure
import SymmetricSubgroupAsymptotics.DegreeTwelveCoherentTernaryCoordinates
import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient

/-!
# The literal ternary block-kernel module

For a faithful transitive `3`-group action, take the literal block system
whose fibres have size three.  Odd order kills every fibre sign, so the
complete block kernel lies in the correlated ternary-coordinate module.
This file retains that concrete kernel and prepares its elementary quotient
as an original-kernel module chart over the actual top action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A homomorphism from a ternary group to an elementary binary group is
trivial.  This is the reusable odd-order input in the fibre-sign argument. -/
theorem binaryHom_eq_one_of_isPGroup
    {G : Type} [Group G] (hG : IsPGroup 3 G)
    (f : G →* Multiplicative (ZMod 2)) : f = 1 := by
  apply MonoidHom.ext
  intro g
  obtain ⟨n, hn⟩ := hG g
  have hthree : (f g) ^ (3 ^ n) = 1 := by
    rw [← map_pow, hn, map_one]
  have htwo : (f g) ^ 2 = 1 := binary_mul_pow_two (f g)
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3))
    (orderOf_dvd_of_pow_eq_one htwo)
    (orderOf_dvd_of_pow_eq_one hthree)

namespace DegreeThreeBlockInversionHead

open OriginalBlockSignCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
variable [∀ x : X, Fintype (originalBlockFibre b x)]

/-- A ternary group has no nontrivial image in the simultaneous binary
fibre-sign group. -/
theorem coordinateSigns_eq_one_of_isPGroup
    (hK : IsPGroup 3 (Kernel (A := A) (X := X))) :
    coordinateSigns b hb = 1 := by
  apply MonoidHom.ext
  intro k
  funext x
  let f : Kernel (A := A) (X := X) →* Multiplicative (ZMod 2) :=
    coordinateSign b hb x
  exact DFunLike.congr_fun (binaryHom_eq_one_of_isPGroup hK f) k

end DegreeThreeBlockInversionHead

namespace TernaryThreeBlockKernelChart

open OriginalBlockSignCoordinates DegreeThreeBlockInversionHead
open DegreeTwelveCoherentTernaryCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable [MulAction.IsPretransitive A X]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
variable [∀ x : X, Fintype (originalBlockFibre b x)]

/-- Every point stabilizer in a ternary group acts evenly on its literal
three-point fibre. -/
theorem stabilizer_sign_eq_one (hA : IsPGroup 3 A) (x : X)
    (s : MulAction.stabilizer A x) :
    Equiv.Perm.sign (originalBlockFibreAction b hb x s) = 1 := by
  let f : MulAction.stabilizer A x →* Multiplicative (ZMod 2) :=
    (permutationBinarySign (originalBlockFibre b x)).comp
      (originalBlockFibreAction b hb x)
  have hf := binaryHom_eq_one_of_isPGroup
    (hA.to_subgroup (MulAction.stabilizer A x)) f
  have hs := (permutationBinarySign_eq_one (originalBlockFibre b x) _).mp
    (DFunLike.congr_fun hf s)
  have hsign : Equiv.Perm.sign (originalBlockFibreAction b hb x s) =
      @Equiv.Perm.sign (originalBlockFibre b x)
        (fun u v => Classical.propDecidable (u = v)) _
        (originalBlockFibreAction b hb x s) := by
    exact @Equiv.Perm.sign_eq_sign_of_equiv
      (originalBlockFibre b x) inferInstance
      (originalBlockFibre b x) inferInstance
      (fun u v => Classical.propDecidable (u = v)) inferInstance
      (originalBlockFibreAction b hb x s)
      (originalBlockFibreAction b hb x s)
      (Equiv.refl _) (fun _ => rfl)
  rw [hsign]
  exact hs

private def transporter (x₀ x : X) : A :=
  Classical.choose (MulAction.exists_smul_eq A x₀ x)

private theorem transporter_spec (x₀ x : X) :
    transporter (A := A) x₀ x • x₀ = x :=
  Classical.choose_spec (MulAction.exists_smul_eq A x₀ x)

/-- Fibre charts transported from one base fibre by literal original
group elements. -/
def coherentChart (x₀ : X) (e₀ : Fin 3 ≃ originalBlockFibre b x₀) (x : X) :
    Fin 3 ≃ originalBlockFibre b x where
  toFun i := ⟨transporter (A := A) x₀ x • (e₀ i).1, by
    rw [hb, (e₀ i).2, transporter_spec]⟩
  invFun ω := e₀.symm ⟨(transporter (A := A) x₀ x)⁻¹ • ω.1, by
    rw [hb, ω.2]
    calc
      (transporter (A := A) x₀ x)⁻¹ • x =
          (transporter (A := A) x₀ x)⁻¹ •
            (transporter (A := A) x₀ x • x₀) :=
        congrArg (fun y : X => (transporter (A := A) x₀ x)⁻¹ • y)
          (transporter_spec (A := A) x₀ x).symm
      _ = x₀ := inv_smul_smul _ _⟩
  left_inv i := by
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    exact Subtype.ext (inv_smul_smul _ _)
  right_inv ω := by
    apply Subtype.ext
    change transporter (A := A) x₀ x •
      (e₀ (e₀.symm ⟨(transporter (A := A) x₀ x)⁻¹ • ω.1, _⟩)).1 = ω.1
    rw [e₀.apply_symm_apply]
    exact smul_inv_smul _ _

/-- The transported charts have even transition maps because every
transition is a relabelled action of an actual point-stabilizer element. -/
theorem coherentChart_transition_sign
    (hA : IsPGroup 3 A) (x₀ : X)
    (e₀ : Fin 3 ≃ originalBlockFibre b x₀) (a : A) (x : X) :
    oddMarkerSign
      (transition b hb (coherentChart b hb x₀ e₀) a x) = 1 := by
  let s : MulAction.stabilizer A x₀ :=
    ⟨(transporter (A := A) x₀ (a • x))⁻¹ * a *
        transporter (A := A) x₀ x, by
      change ((transporter (A := A) x₀ (a • x))⁻¹ * a *
        transporter (A := A) x₀ x) • x₀ = x₀
      rw [mul_smul, mul_smul, transporter_spec]
      calc
        (transporter (A := A) x₀ (a • x))⁻¹ • (a • x) =
            (transporter (A := A) x₀ (a • x))⁻¹ •
              (transporter (A := A) x₀ (a • x) • x₀) :=
          congrArg (fun y : X =>
            (transporter (A := A) x₀ (a • x))⁻¹ • y)
              (transporter_spec (A := A) x₀ (a • x)).symm
        _ = x₀ := inv_smul_smul _ _⟩
  have he : transition b hb (coherentChart b hb x₀ e₀) a x =
      e₀.symm.permCongr (originalBlockFibreAction b hb x₀ s) := by
    apply Equiv.ext
    intro i
    change (coherentChart b hb x₀ e₀ (a • x)).symm
        (fibreTransport b hb a x (coherentChart b hb x₀ e₀ x i)) =
      e₀.symm (originalBlockFibreAction b hb x₀ s (e₀ i))
    apply e₀.injective
    change e₀ (e₀.symm ⟨(transporter (A := A) x₀ (a • x))⁻¹ •
        (a • (transporter (A := A) x₀ x • (e₀ i).1)), _⟩) =
      e₀ (e₀.symm ⟨((transporter (A := A) x₀ (a • x))⁻¹ * a *
        transporter (A := A) x₀ x) • (e₀ i).1, _⟩)
    rw [e₀.apply_symm_apply, e₀.apply_symm_apply]
    apply Subtype.ext
    simp only [mul_smul]
  apply (oddMarkerSign_eq_one _).mpr
  rw [he, Equiv.Perm.sign_permCongr]
  exact stabilizer_sign_eq_one b hb hA x₀ s

/-- Coherence of all transported fibre charts for the original ternary
group action. -/
theorem coherentChart_coherent (hA : IsPGroup 3 A) (x₀ : X)
    (e₀ : Fin 3 ≃ originalBlockFibre b x₀) :
    Coherent b hb (coherentChart b hb x₀ e₀) :=
  coherentChart_transition_sign b hb hA x₀ e₀

end TernaryThreeBlockKernelChart

namespace TransitiveThreeBlockCover

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] {x : X}
    (D : TransitiveThreeBlockCover U x)

noncomputable instance fibreFintype (y : D.Points) :
    Fintype (originalBlockFibre D.map y) := Fintype.ofFinite _

/-- All literal fibre signs vanish for the block cover of a ternary group. -/
theorem coordinateSigns_eq_one (hU : IsPGroup 3 U) :
    DegreeThreeBlockInversionHead.coordinateSigns D.map D.map_equivariant = 1 := by
  apply DegreeThreeBlockInversionHead.coordinateSigns_eq_one_of_isPGroup
  exact hU.to_subgroup D.topMap.ker

/-- One concrete chart on the base fibre. -/
def baseFibreChart : Fin 3 ≃ D.Fibre :=
  (Finite.equivFinOfCardEq D.fibre_card).symm

/-- Coherent charts on all literal fibres, transported from the base fibre
by actual elements of the original ternary group. -/
def coherentFibreCharts :
    ∀ y : D.Points, Fin 3 ≃ originalBlockFibre D.map y :=
  TernaryThreeBlockKernelChart.coherentChart
    D.map D.map_equivariant D.base D.baseFibreChart

theorem coherentFibreCharts_coherent (hU : IsPGroup 3 U) :
    DegreeTwelveCoherentTernaryCoordinates.Coherent
      D.map D.map_equivariant D.coherentFibreCharts :=
  TernaryThreeBlockKernelChart.coherentChart_coherent
    D.map D.map_equivariant hU D.base D.baseFibreChart

/-- The kernel of the onto map to the literal faithful top. -/
abbrev TopKernel : Subgroup U := D.topMap.rangeRestrict.ker

/-- The range-restricted top map has the same physical kernel as the
unrestricted block-action map. -/
def physicalKernelEquiv : D.TopKernel ≃* D.topMap.ker :=
  MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict D.topMap)

/-- All correlated ternary fibre coordinates of the exact physical kernel. -/
def ternaryCoordinates (hU : IsPGroup 3 U) :
    D.TopKernel →* Multiplicative (D.Points → ZMod 3) where
  toFun k := Multiplicative.ofAdd (fun y =>
    (DegreeTwelveCoherentTernaryCoordinates.kernelTernaryCoordinate
      D.map D.map_equivariant D.coherentFibreCharts
      (D.coordinateSigns_eq_one hU) y (D.physicalKernelEquiv k)).toAdd)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    funext y
    exact congrArg Multiplicative.toAdd
      (map_one (DegreeTwelveCoherentTernaryCoordinates.kernelTernaryCoordinate
        D.map D.map_equivariant D.coherentFibreCharts
        (D.coordinateSigns_eq_one hU) y))
  map_mul' k l := by
    apply congrArg Multiplicative.ofAdd
    funext y
    exact congrArg Multiplicative.toAdd
      (map_mul (DegreeTwelveCoherentTernaryCoordinates.kernelTernaryCoordinate
        D.map D.map_equivariant D.coherentFibreCharts
        (D.coordinateSigns_eq_one hU) y)
        (D.physicalKernelEquiv k) (D.physicalKernelEquiv l))

theorem ternaryCoordinates_injective (hU : IsPGroup 3 U) :
    Function.Injective (D.ternaryCoordinates hU) := by
  intro k l hkl
  apply D.physicalKernelEquiv.injective
  apply DegreeTwelveCoherentTernaryCoordinates.kernelTernaryCoordinates_injective
    D.map D.map_equivariant D.coherentFibreCharts (D.coordinateSigns_eq_one hU)
  funext y
  apply Multiplicative.toAdd.injective
  exact congrFun (congrArg Multiplicative.toAdd hkl) y

/-- Ambient conjugation is the literal permutation action on the coherent
ternary coordinate vector. -/
theorem ternaryCoordinates_conjugation (hU : IsPGroup 3 U)
    (u : U) (k : D.TopKernel) :
    permutationFunctionRepresentation (ZMod 3) D.Top D.Points
        (D.topMap.rangeRestrict u) (D.ternaryCoordinates hU k).toAdd =
      (D.ternaryCoordinates hU (MulAut.conjNormal u k)).toAdd := by
  funext y
  change
    (DegreeTwelveCoherentTernaryCoordinates.kernelTernaryCoordinate
      D.map D.map_equivariant D.coherentFibreCharts
      (D.coordinateSigns_eq_one hU)
      ((D.topMap.rangeRestrict u)⁻¹ • y) (D.physicalKernelEquiv k)).toAdd =
    (DegreeTwelveCoherentTernaryCoordinates.kernelTernaryCoordinate
      D.map D.map_equivariant D.coherentFibreCharts
      (D.coordinateSigns_eq_one hU) y
      (D.physicalKernelEquiv (MulAut.conjNormal u k))).toAdd
  have hc :=
    DegreeTwelveCoherentTernaryCoordinates.kernelTernaryCoordinate_conjugation
      D.map D.map_equivariant D.coherentFibreCharts
      (D.coordinateSigns_eq_one hU) (D.coherentFibreCharts_coherent hU)
      u (u⁻¹ • y) (D.physicalKernelEquiv k)
  have hpoint : (D.topMap.rangeRestrict u)⁻¹ • y = u⁻¹ • y := by
    rfl
  have hkernel :
      D.physicalKernelEquiv (MulAut.conjNormal u k) =
        MulAut.conjNormal u (D.physicalKernelEquiv k) := by
    apply Subtype.ext
    rfl
  rw [hpoint, hkernel]
  simpa only [smul_inv_smul] using congrArg Multiplicative.toAdd hc.symm

/-- The exact correlated image of the physical block kernel. -/
def kernelSpace (hU : IsPGroup 3 U) :
    Submodule (ZMod 3) (D.Points → ZMod 3) :=
  (AddMonoidHom.toMultiplicativeRight.symm
    (D.ternaryCoordinates hU)).range.toZModSubmodule 3

/-- The physical kernel with its coordinate image as exact codomain. -/
def kernelSpaceHom (hU : IsPGroup 3 U) :
    D.TopKernel →* Multiplicative (D.kernelSpace hU) where
  toFun k := Multiplicative.ofAdd
    ⟨(D.ternaryCoordinates hU k).toAdd, ⟨Additive.ofMul k, rfl⟩⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (D.ternaryCoordinates hU).map_one
  map_mul' k l := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((D.ternaryCoordinates hU).map_mul k l)

theorem kernelSpaceHom_bijective (hU : IsPGroup 3 U) :
    Function.Bijective (D.kernelSpaceHom hU) := by
  constructor
  · intro k l hkl
    apply D.ternaryCoordinates_injective hU
    exact congrArg (fun z : Multiplicative (D.kernelSpace hU) =>
      Multiplicative.ofAdd z.toAdd.val) hkl
  · intro v
    obtain ⟨k, hk⟩ := v.toAdd.property
    refine ⟨k.toMul, ?_⟩
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext hk

/-- Reversible coordinates on the complete physical block kernel. -/
def kernelEquiv (hU : IsPGroup 3 U) :
    D.TopKernel ≃* Multiplicative (D.kernelSpace hU) :=
  MulEquiv.ofBijective (D.kernelSpaceHom hU)
    (D.kernelSpaceHom_bijective hU)

/-- The correlated coordinate image as a literal subrepresentation of the
top permutation module. -/
def kernelSubrepresentation (hU : IsPGroup 3 U) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 3) D.Top D.Points) where
  toSubmodule := D.kernelSpace hU
  apply_mem_toSubmodule t v hv := by
    obtain ⟨u, rfl⟩ := D.topMap.rangeRestrict_surjective t
    obtain ⟨k, rfl⟩ := hv
    change permutationFunctionRepresentation (ZMod 3) D.Top D.Points
      (D.topMap.rangeRestrict u) (D.ternaryCoordinates hU k.toMul).toAdd ∈
        D.kernelSpace hU
    rw [D.ternaryCoordinates_conjugation hU]
    exact ⟨Additive.ofMul (MulAut.conjNormal u k.toMul), rfl⟩

@[simp] theorem kernelSubrepresentation_apply (hU : IsPGroup 3 U)
    (u : U) (k : D.TopKernel) :
    (D.kernelSubrepresentation hU).toRepresentation
        (D.topMap.rangeRestrict u) (D.kernelSpaceHom hU k).toAdd =
      (D.kernelSpaceHom hU (MulAut.conjNormal u k)).toAdd := by
  apply Subtype.ext
  exact D.ternaryCoordinates_conjugation hU u k

/-- The concrete ternary block-kernel module over the actual faithful top. -/
abbrev kernelModule (hU : IsPGroup 3 U) : Rep (ZMod 3) D.Top :=
  Rep.of (D.kernelSubrepresentation hU).toRepresentation

/-- Exact original-kernel chart for the onto block-top map. -/
def originalKernelChart (hU : IsPGroup 3 U) :
    OriginalKernelModuleChart D.topMap.rangeRestrict (D.kernelModule hU) where
  equiv := (D.kernelEquiv hU).symm
  conjugate u a := by
    let k : D.TopKernel :=
      (D.kernelEquiv hU).symm (Multiplicative.ofAdd a)
    have hk : (D.kernelSpaceHom hU k).toAdd = a :=
      congrArg Multiplicative.toAdd
        ((D.kernelEquiv hU).apply_symm_apply (Multiplicative.ofAdd a))
    have hact := D.kernelSubrepresentation_apply hU u k
    rw [hk] at hact
    have he : (D.kernelEquiv hU).symm
        (Multiplicative.ofAdd
          ((D.kernelModule hU).ρ (D.topMap.rangeRestrict u) a)) =
        MulAut.conjNormal u k := by
      apply (D.kernelEquiv hU).injective
      rw [(D.kernelEquiv hU).apply_symm_apply]
      apply Multiplicative.toAdd.injective
      exact hact
    exact congrArg (fun z : D.TopKernel => (z : U)) he

end TransitiveThreeBlockCover

end SymmetricSubgroupAsymptotics

end
