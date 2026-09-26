import SymmetricSubgroupAsymptotics.TerminalCohomology
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
import Mathlib.Tactic.LinearCombination

/-! An actual inflated coboundary determines a relative character on the
original kernel. Vanishing of this character descends the primitive to the
original quotient. A linear space of cocycle/primitive pairs gives the
inflation-kernel dimension bound without selecting representatives linearly
or assuming a spectral sequence, a split extension, or an odd-order action. -/
set_option autoImplicit false
noncomputable section
open CategoryTheory

namespace SymmetricSubgroupAsymptotics
namespace BinaryInflationKernel

variable {G Q : Type} [Group G] [Group Q] (β : G →* Q)

/-- Literal quotient cocycles paired with actual primitives of their pullback. -/
def primitives : Submodule (ZMod 2)
    (groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) Q (ZMod 2)) × (G → ZMod 2)) where
  carrier := {z | ∀ x y : G, z.2 y - z.2 (x*y) + z.2 x = z.1 (β x,β y)}
  zero_mem' := by
    intro x y
    change (0 : ZMod 2) - 0 + 0 = 0
    simp
  add_mem' := by
    intro z t hz ht x y
    change (z.2 y+t.2 y) - (z.2 (x*y)+t.2 (x*y)) + (z.2 x+t.2 x) =
      z.1 (β x,β y)+t.1 (β x,β y)
    rw [← hz x y,← ht x y]
    abel
  smul_mem' := by
    intro a z hz x y
    change a • z.2 y - a • z.2 (x*y) + a • z.2 x = a • z.1 (β x,β y)
    rw [← hz x y,smul_add,smul_sub]

variable (z : primitives β)

theorem cocycle_one : z.1.1 (1,1) = z.1.2 1 := by
  simpa only [map_one,one_mul,sub_self,zero_add] using (z.2 1 1).symm

theorem primitive_mul_kernel_right (x : G) (n : β.ker) :
    z.1.2 (x*(n : G)) = z.1.2 x + z.1.2 n - z.1.2 1 := by
  have h := z.2 x (n : G)
  rw [show β (n : G)=1 from n.2,
    groupCohomology.cocycles₂_map_one_snd,Rep.trivial_ρ_apply,cocycle_one β z] at h
  linear_combination -h

theorem primitive_mul_kernel_left (n : β.ker) (x : G) :
    z.1.2 ((n : G)*x) = z.1.2 n + z.1.2 x - z.1.2 1 := by
  have h := z.2 (n : G) x
  rw [show β (n : G)=1 from n.2,
    groupCohomology.cocycles₂_map_one_fst,cocycle_one β z] at h
  linear_combination -h

/-- Normalization is essential: arbitrary cocycles and primitives need not
vanish at the identity. The resulting character is on the literal kernel. -/
def kernelCharacter : PrimeCharacters 2 β.ker where
  toFun n := z.1.2 (n.toMul : G) - z.1.2 1
  map_zero' := by change z.1.2 1-z.1.2 1=0; exact sub_self _
  map_add' n m := by
    change z.1.2 ((n.toMul : G)*(m.toMul : G))-z.1.2 1 =
      (z.1.2 (n.toMul : G)-z.1.2 1)+(z.1.2 (m.toMul : G)-z.1.2 1)
    rw [primitive_mul_kernel_right β z (n.toMul : G) m.toMul]
    abel

/-- The whole original G acts on its kernel; no smaller acting group is used. -/
theorem kernelCharacter_invariant : kernelCharacter β z ∈
    primeRelativeCharacters 2 β.ker := by
  intro g n
  have h₁ := primitive_mul_kernel_right β z g n
  have h₂ := z.2 (g*(n : G)) g⁻¹
  have h₃ := z.2 g g⁻¹
  rw [map_mul,show β (n : G)=1 from n.2,mul_one] at h₂
  rw [mul_inv_cancel] at h₃
  change z.1.2 (g*(n : G)*g⁻¹)-z.1.2 1 = z.1.2 n-z.1.2 1
  linear_combination h₁ - h₂ + h₃

/-- Restriction of the actual primitive, retaining original ambient conjugation. -/
def restriction : primitives β →ₗ[ZMod 2] primeRelativeCharacters 2 β.ker where
  toFun z := ⟨kernelCharacter β z,kernelCharacter_invariant β z⟩
  map_add' z t := by
    apply Subtype.ext
    ext n
    change (z.1.2 (n : G)+t.1.2 (n : G))-(z.1.2 1+t.1.2 1) =
      (z.1.2 (n : G)-z.1.2 1)+(t.1.2 (n : G)-t.1.2 1)
    abel
  map_smul' a z := by
    apply Subtype.ext
    ext n
    change a • z.1.2 (n : G)-a • z.1.2 1 =
      a • (z.1.2 (n : G)-z.1.2 1)
    exact (smul_sub _ _ _).symm

/-- The pair defines its actual H² class in the original inflation kernel. -/
def classMap : primitives β →ₗ[ZMod 2] (binaryH2Pullback β).ker where
  toFun z := ⟨groupCohomology.H2π _ z.1.1,by
    rw [binaryH2Pullback_kernel_iff]
    refine ⟨z.1.2,funext fun xy => ?_⟩
    exact z.2 xy.1 xy.2⟩
  map_add' z t := by
    apply Subtype.ext
    exact map_add (groupCohomology.H2π _).hom z.1.1 t.1.1
  map_smul' a z := by
    apply Subtype.ext
    exact map_smul (groupCohomology.H2π _).hom a z.1.1

/-- Every actual inflation-kernel class admits such a cocycle/primitive pair. -/
theorem classMap_surjective : Function.Surjective (classMap β) := by
  intro t
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective
    (groupCohomology.H2π (Rep.trivial (ZMod 2) Q (ZMod 2)))).mp inferInstance t.1
  have hk : groupCohomology.H2π _ c ∈ (binaryH2Pullback β).ker := hc.symm ▸ t.2
  obtain ⟨b,hb⟩ := (binaryH2Pullback_kernel_iff β c).mp hk
  refine ⟨⟨(c,b),?_⟩,?_⟩
  · intro x y
    exact congrFun hb (x,y)
  · exact Subtype.ext hc

/-- Zero normalized restriction makes the primitive constant on literal
fibres of β, rather than replacing the quotient by an isomorphic group. -/
theorem primitive_eq_of_restriction_zero (hz : restriction β z = 0)
    {x y : G} (hxy : β x=β y) : z.1.2 x=z.1.2 y := by
  let n : β.ker := ⟨x*y⁻¹,by simp [MonoidHom.mem_ker,hxy]⟩
  have hn := DFunLike.congr_fun (congrArg Subtype.val hz) (Additive.ofMul n)
  change z.1.2 (n : G)-z.1.2 1=0 at hn
  have hn' : z.1.2 (n : G)=z.1.2 1 := sub_eq_zero.mp hn
  have h := primitive_mul_kernel_left β z n y
  have hny : (n : G)*y=x := by dsimp [n]; group
  rw [hny,hn'] at h
  linear_combination h

/-- An onto original β allows the primitive to descend to Q. Consequently
zero relative restriction forces the actual quotient H² class to vanish. -/
theorem restriction_ker_le_classMap_ker (hβ : Function.Surjective β) :
    (restriction β).ker ≤ (classMap β).ker := by
  intro z hz
  have hz₀ : restriction β z=0 := LinearMap.mem_ker.mp hz
  let s : Q → G := Function.surjInv hβ
  have hs (q : Q) : β (s q)=q := Function.rightInverse_surjInv hβ q
  let b : Q → ZMod 2 := fun q => z.1.2 (s q)
  have hb (g : G) : b (β g)=z.1.2 g :=
    primitive_eq_of_restriction_zero β z hz₀ (hs (β g))
  have hc : groupCohomology.H2π _ z.1.1=0 := by
    rw [groupCohomology.H2π_eq_zero_iff]
    refine ⟨b,funext fun qr => ?_⟩
    rcases qr with ⟨q,r⟩
    obtain ⟨x,rfl⟩ := hβ q
    obtain ⟨y,rfl⟩ := hβ r
    change b (β y)-b (β x*β y)+b (β x)=z.1.1 (β x,β y)
    rw [← map_mul,hb,hb,hb]
    exact z.2 x y
  exact LinearMap.mem_ker.mpr (Subtype.ext hc)

end BinaryInflationKernel

/-- The actual binary H² inflation kernel is bounded by the invariant
characters of the literal kernel under the entire original source group. -/
theorem binaryH2Pullback_kernel_finrank_le_relativeHead
    {G Q : Type} [Group G] [Group Q] [Finite G]
    (β : G →* Q) (hβ : Function.Surjective β) :
    Module.finrank (ZMod 2) (binaryH2Pullback β).ker ≤
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 β.ker) := by
  letI : Finite Q := Finite.of_surjective β hβ
  have hclass := (BinaryInflationKernel.classMap β).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (BinaryInflationKernel.classMap_surjective β),
    finrank_top] at hclass
  have hrestriction := (BinaryInflationKernel.restriction β).finrank_range_add_finrank_ker
  have hker := Submodule.finrank_mono
    (BinaryInflationKernel.restriction_ker_le_classMap_ker β hβ)
  have hrange := (LinearMap.range (BinaryInflationKernel.restriction β)).finrank_le
  omega

/-- Specialization to the actual evaluation quotient A₂(T), without
identifying its kernel with any separately defined Frattini subgroup. -/
theorem terminalRestrictedInflationKernel_finrank_le_relativeHead
    (T : Type) [Group T] [Finite T] :
    Module.finrank (ZMod 2) (terminalRestrictedInflationKernel T) ≤
      Module.finrank (ZMod 2) (primeRelativeCharacters 2
        (AddMonoidHom.toMultiplicativeRight (binaryAbelianizationMap T)).ker) :=
  binaryH2Pullback_kernel_finrank_le_relativeHead _
    (binaryAbelianizationMap_surjective T)

end SymmetricSubgroupAsymptotics
