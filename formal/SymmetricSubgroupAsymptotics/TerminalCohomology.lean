import SymmetricSubgroupAsymptotics.TerminalCentralFibres
import SymmetricSubgroupAsymptotics.BinaryAbelianization
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# The retained terminal annihilator in actual group cohomology

The scalar defect of the original extension defines its actual H² class.
The character-extension annihilator equals the kernel of this class map.
The inflation kernel below is also an actual subspace, not only a dimension.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory

namespace SymmetricSubgroupAsymptotics

variable {X Y K : Type} [Group X] [Group Y] [AddCommGroup K] [Module (ZMod 2) K]
    (π : X →* Y) (e : Multiplicative K ≃* π.ker)
    (hπ : Function.Surjective π) (hcentral : π.ker ≤ Subgroup.center X)

/-- Scalarization of the actual normalized section defect. -/
def terminalScalarCocycle (ell : Module.Dual (ZMod 2) K) :
    groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) Y (ZMod 2)) :=
  ⟨fun yz ↦ ell (terminalSectionDefect π e hπ yz.1 yz.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro x y z
    have h := congrArg ell (terminalSectionDefect_cocycle π e hπ hcentral x y z)
    simpa only [map_add, Rep.trivial_ρ_apply, add_comm] using h⟩

/-- Scalar classes vary linearly in the original kernel character. -/
def terminalScalarCocycleMap : Module.Dual (ZMod 2) K →ₗ[ZMod 2]
    groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) Y (ZMod 2)) where
  toFun := terminalScalarCocycle π e hπ hcentral
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual scalar H² class of this extension. -/
def terminalScalarClassMap : Module.Dual (ZMod 2) K →ₗ[ZMod 2]
    groupCohomology.H2 (Rep.trivial (ZMod 2) Y (ZMod 2)) :=
  (groupCohomology.H2π (Rep.trivial (ZMod 2) Y (ZMod 2))).hom.comp
    (terminalScalarCocycleMap π e hπ hcentral)

theorem terminalScalarClass_eq_zero_iff (ell : Module.Dual (ZMod 2) K) :
    terminalScalarClassMap π e hπ hcentral ell = 0 ↔
      TerminalScalarCoboundary π e hπ ell := by
  change groupCohomology.H2π _ (terminalScalarCocycle π e hπ hcentral ell) = 0 ↔ _
  rw [groupCohomology.H2π_eq_zero_iff]
  change (∃ b : Y → ZMod 2,
    (groupCohomology.d₁₂ (Rep.trivial (ZMod 2) Y (ZMod 2))).hom b =
      fun yz ↦ ell (terminalSectionDefect π e hπ yz.1 yz.2)) ↔ _
  constructor
  · rintro ⟨b,hb⟩
    have he (y z : Y) : b z - b (y*z) + b y =
        ell (terminalSectionDefect π e hπ y z) := congrFun hb (y,z)
    refine ⟨b,?_,?_⟩
    · have h := he 1 1
      simpa using h
    · intro y z
      rw [← he y z]
      abel
  · rintro ⟨b,_,hb⟩
    refine ⟨b,funext fun yz ↦ ?_⟩
    change b yz.2 - b (yz.1*yz.2) + b yz.1 = _
    rw [hb]
    abel

/-- The retained character subspace is literally the kernel of the map to
mathlib's H² of the entire (possibly nonabelian) exterior image. -/
theorem terminalSplittingAnnihilator_eq_H2_kernel :
    terminalSplittingAnnihilator π e = (terminalScalarClassMap π e hπ hcentral).ker := by
  ext ell
  rw [LinearMap.mem_ker, terminalScalarClass_eq_zero_iff,
    terminalSplittingAnnihilator_iff_coboundary π e hπ hcentral]

section Inflation

variable {T B : Type} [Group T] [Group B]

/-- Pullback in actual degree-two group cohomology with binary coefficients. -/
def binaryH2Pullback (β : T →* B) :
    groupCohomology.H2 (Rep.trivial (ZMod 2) B (ZMod 2)) →ₗ[ZMod 2]
      groupCohomology.H2 (Rep.trivial (ZMod 2) T (ZMod 2)) :=
  (groupCohomology.map β (𝟙 (Rep.trivial (ZMod 2) T (ZMod 2))) 2).hom

/-- The corresponding pullback of literal scalar cocycles. -/
def binaryCocyclePullback (β : T →* B)
    (c : groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) B (ZMod 2))) :
    groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) T (ZMod 2)) :=
  ⟨fun xy ↦ c (β xy.1,β xy.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro x y z
    have h := (groupCohomology.mem_cocycles₂_iff c).mp c.2 (β x) (β y) (β z)
    simpa only [map_mul, Rep.trivial_ρ_apply] using h⟩

/-- Cohomology pullback uses the very same cocycle, evaluated on the actual
quotient map; it is not replaced by an unrelated class of equal dimension. -/
theorem binaryH2Pullback_class (β : T →* B)
    (c : groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) B (ZMod 2))) :
    binaryH2Pullback β (groupCohomology.H2π _ c) =
      groupCohomology.H2π _ (binaryCocyclePullback β c) := by
  exact congrArg (fun f ↦ f c)
    (groupCohomology.H2π_comp_map β (𝟙 (Rep.trivial (ZMod 2) T (ZMod 2))))

/-- Membership in the retained kernel is precisely the coboundary test
after pullback to the whole source, without asserting vanishing before it. -/
theorem binaryH2Pullback_kernel_iff (β : T →* B)
    (c : groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) B (ZMod 2))) :
    groupCohomology.H2π _ c ∈ (binaryH2Pullback β).ker ↔
      (fun xy : T × T ↦ c (β xy.1,β xy.2)) ∈
        groupCohomology.coboundaries₂ (Rep.trivial (ZMod 2) T (ZMod 2)) := by
  rw [LinearMap.mem_ker, binaryH2Pullback_class, groupCohomology.H2π_eq_zero_iff]
  rfl

/-- The actual pullback kernel of the evaluation map, which is the canonical
quotient A₂(T) for finite T. No dimension replacement or vanishing assumption
is made. -/
def terminalRestrictedInflationKernel (T : Type) [Group T] :
    Submodule (ZMod 2)
      (groupCohomology.H2 (Rep.trivial (ZMod 2)
        (Multiplicative (BinaryAbelianization T)) (ZMod 2))) :=
  (binaryH2Pullback
    (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T))).ker

theorem terminalRestrictedInflationKernel_mem_iff
    (c : groupCohomology.cocycles₂ (Rep.trivial (ZMod 2)
      (Multiplicative (BinaryAbelianization T)) (ZMod 2))) :
    groupCohomology.H2π _ c ∈ terminalRestrictedInflationKernel T ↔
      (fun xy : T × T ↦ c
        (Multiplicative.ofAdd (binaryAbelianizationMap T (Additive.ofMul xy.1)),
         Multiplicative.ofAdd (binaryAbelianizationMap T (Additive.ofMul xy.2)))) ∈
        groupCohomology.coboundaries₂ (Rep.trivial (ZMod 2) T (ZMod 2)) :=
  binaryH2Pullback_kernel_iff _ c

end Inflation

end SymmetricSubgroupAsymptotics
