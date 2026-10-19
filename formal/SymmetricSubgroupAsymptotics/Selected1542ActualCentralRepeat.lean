import SymmetricSubgroupAsymptotics.Selected1542CentralBinaryRows
import SymmetricSubgroupAsymptotics.Selected1542QuotientCentralImage
import SymmetricSubgroupAsymptotics.FiniteKernelTableCoordinates
import SymmetricSubgroupAsymptotics.SurjectiveCoordinateTransport
import SymmetricSubgroupAsymptotics.ActualRepeatedAlternatingCentralCoordinates

/-! Exact binary coordinates on the same original L/N yield the actual
nonsplit central cover with three central and two scalar coordinates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

private theorem centralCoordinate_one : centralCoordinate 0=1 := by
  funext k
  exact centralBinaryPilot00_identity k

private theorem centralCoordinate_mul (i j : Fin 64) :
    centralCoordinate (preimageMul i j)=centralCoordinate i*centralCoordinate j := by
  funext k
  exact centralBinary_all_mul i j k

def centralBase : originalPreimage →* (Fin 3 → Multiplicative (ZMod 2)) :=
  preimageTable.coordinateHom centralCoordinate centralCoordinate_one centralCoordinate_mul

private theorem centralCoordinate_zero (i : Fin 64) :
    centralCoordinate i=1 ↔ preimageOriginal i∈originalNormal := by
  have hc : centralCoordinate i=1 ↔ ∀ k : Fin 3, centralCoordinate i k=1 :=
    ⟨fun h k => congrFun h k,fun h => funext h⟩
  rw [hc,centralBinary_all_zero,centralBinary_all_kernel]
  constructor
  · rintro ⟨n,hn⟩
    have he : preimageOriginal i=normalOriginal n := Subtype.ext (Equiv.ext hn)
    rw [he]
    exact (normalTable.chart n).property
  · intro hi
    obtain ⟨n,hn⟩ := normalTable.chart_surjective ⟨preimageOriginal i,hi⟩
    have he : normalOriginal n=preimageOriginal i := congrArg Subtype.val hn
    exact ⟨n,fun p => (congrArg (fun g : Original => g.val p) he).symm⟩

theorem centralBase_kernel : centralBase.ker=originalNormal.subgroupOf originalPreimage :=
  preimageTable.coordinateHom_ker centralCoordinate centralCoordinate_one centralCoordinate_mul
    originalNormal centralCoordinate_zero

def centralProjection : originalPreimage →* quotientAlternating.ker where
  toFun l := ⟨QuotientGroup.mk' originalNormal (l : Original),by
    rw [quotientAlternating_kernel]
    exact ⟨l,l.property,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one (QuotientGroup.mk' originalNormal)
  map_mul' l k := by apply Subtype.ext; exact map_mul (QuotientGroup.mk' originalNormal) (l : Original) (k : Original)

theorem centralProjection_surjective : Function.Surjective centralProjection := by
  intro z
  have hz : (z : Quotient)∈originalPreimage.map (QuotientGroup.mk' originalNormal) := by
    rw [←quotientAlternating_kernel]
    exact z.property
  obtain ⟨g,hg,hgz⟩ := hz
  exact ⟨⟨g,hg⟩,Subtype.ext hgz⟩

theorem centralProjection_kernel : centralProjection.ker=originalNormal.subgroupOf originalPreimage := by
  ext l
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change QuotientGroup.mk' originalNormal (l : Original)=1 at hv
    change (l : Original)∈originalNormal
    exact (QuotientGroup.eq_one_iff (l : Original)).mp hv
  · intro h
    apply Subtype.ext
    change QuotientGroup.mk' originalNormal (l : Original)=1
    exact (QuotientGroup.eq_one_iff (l : Original)).mpr h

def actualCentralCoordinates : quotientAlternating.ker →* (Fin 3 → Multiplicative (ZMod 2)) :=
  SurjectiveCoordinateTransport.descend centralProjection centralProjection_surjective centralBase
    (centralProjection_kernel.trans centralBase_kernel.symm)

theorem actualCentralCoordinates_injective : Function.Injective actualCentralCoordinates :=
  SurjectiveCoordinateTransport.descend_injective centralProjection centralProjection_surjective centralBase
    (centralProjection_kernel.trans centralBase_kernel.symm)

/-- The actual Original/N8 quotient, retaining its original denominator. -/
def actualCentralRepeat : ScalarFourCentralTopCoordinates Quotient CyclicThree 3 2 :=
  ActualRepeatedAlternatingCentralCoordinates.coordinates quotientAlternating 0
    quotientAlternating_common quotient_top_surjective quotientAlternating_kernel_central
    actualCentralCoordinates actualCentralCoordinates_injective

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
