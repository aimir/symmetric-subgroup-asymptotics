import SymmetricSubgroupAsymptotics.ActualFullWreathFamily
import SymmetricSubgroupAsymptotics.FinitePermutationalWreathInstance
import SymmetricSubgroupAsymptotics.ActualWreathMapBaseKernelChart
import SymmetricSubgroupAsymptotics.FiniteExtensionFixedImageRestrictedKernelCount
import SymmetricSubgroupAsymptotics.SimplePowerRestrictedKernelExtensionCount

/-! A complete fixed-image chief-layer bound for the ACTUAL full-component
wreath family. Every support and whole lift is counted. Kernel normality is
proved from literal FullComponent, never supplied as a callback. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualFullWreathSimpleKernelFibreCount
open PermutationalWreathProduct

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

variable {R R' Q I J T : Type} [Group R] [Group R'] [Group Q] [MulAction Q I]
    [Group T] [Finite T] [IsSimpleGroup T] [Fintype J]
    (phi : R →* R') (eSoc : phi.ker ≃* (J → T)) (hZ : IsCenterless T)

def localChart : SemisimpleNormalChart phi.ker where
  ι := J
  factor := fun _ => T
  simple _ := inferInstance
  centerless _ := hZ
  equiv := eSoc

def kernelChart : (mapBase (Q := Q) (I := I) phi).ker ≃* ((I × J) → T) :=
  ActualWreathMapBaseKernelChart.chart phi (localChart phi eSoc hZ)

abbrev Fibre (hphi : Function.Surjective phi) (H : ActualFullWreathFamily.Family R' Q I) :=
  {L : ActualFullWreathFamily.Family R Q I // ActualFullWreathFamily.localImage phi hphi L=H}

/-- Forget only redundant proofs; retain the literal subgroup and its image. -/
def encode (hphi : Function.Surjective phi) (H : ActualFullWreathFamily.Family R' Q I)
    (L : Fibre phi hphi H) :
    FiniteExtensionFixedImageRestrictedKernelCount.Family (mapBase phi)
      (SimplePowerRestrictedKernelExtensionCount.KernelPredicate (mapBase phi)
        (kernelChart phi eSoc hZ)) H.val := by
  refine ⟨L.val.val,congrArg Subtype.val L.property,?_⟩
  intro p
  exact ActualWreathMapBaseKernelChart.intersection_coordinate_normal phi
    (localChart phi eSoc hZ) L.val.val L.val.property.2 p

theorem encode_injective (hphi : Function.Surjective phi)
    (H : ActualFullWreathFamily.Family R' Q I) :
    Function.Injective (encode phi eSoc hZ hphi H) := by
  intro L M h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun U : FiniteExtensionFixedImageRestrictedKernelCount.Family (mapBase phi)
    (SimplePowerRestrictedKernelExtensionCount.KernelPredicate (mapBase phi)
      (kernelChart phi eSoc hZ)) H.val => U.val) h

include eSoc hZ in
/-- Exact cardinality of the SAME ambient compression kernel. -/
theorem kernel_card [Finite I] :
    Nat.card (mapBase (Q := Q) (I := I) phi).ker=
      Nat.card T ^ (Nat.card I * Nat.card J) := by
  calc
    _=Nat.card ((I × J) → T) := Nat.card_congr (kernelChart phi eSoc hZ).toEquiv
    _=_ := by rw [Nat.card_fun,Nat.card_prod]

include eSoc hZ in
/-- No count of other quotient images or order of the permutation top is charged. -/
theorem card_fibre_le [Finite R] [Finite Q] [Finite I]
    (hphi : Function.Surjective phi) (H : ActualFullWreathFamily.Family R' Q I)
    {d : ℕ} (f : Fin d → H.val) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (Fibre phi hphi H)≤
      (2^(Nat.card I * Nat.card J) *
        (2*(1+(Nat.card I * Nat.card J)*Nat.card (T ≃* T)))^(Nat.card I * Nat.card J))*
        Nat.card T ^ ((Nat.card I * Nat.card J)*d) := by
  have hmap : Function.Surjective (mapBase (Q := Q) (I := I) phi) := by
    intro w
    choose s hs using hphi
    refine ⟨⟨fun i => s (w.left i),w.right⟩,?_⟩
    apply PermutationalWreathProduct.ext
    · funext i
      exact hs (w.left i)
    · rfl
  have hi := Nat.card_le_card_of_injective (encode phi eSoc hZ hphi H)
    (encode_injective phi eSoc hZ hphi H)
  have hb := FiniteExtensionFixedImageRestrictedKernelCount.card_family_le (mapBase phi)
    (SimplePowerRestrictedKernelExtensionCount.KernelPredicate (mapBase phi)
      (kernelChart phi eSoc hZ)) H.val hmap f hf
  have hk := SimplePowerRestrictedKernelExtensionCount.card_kernelFamily_le
    (mapBase (Q := Q) (I := I) phi) (kernelChart (Q := Q) (I := I) phi eSoc hZ) hZ
  have hh := hi.trans (hb.trans (Nat.mul_le_mul_right _ hk))
  simpa only [Nat.card_prod,kernel_card phi eSoc hZ,←pow_mul] using hh

end SymmetricSubgroupAsymptotics.ActualFullWreathSimpleKernelFibreCount
