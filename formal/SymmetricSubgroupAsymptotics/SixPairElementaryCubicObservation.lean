import SymmetricSubgroupAsymptotics.SixPairElementaryLocalObservation
import SymmetricSubgroupAsymptotics.SixPairLocalKernelConjugation
import SymmetricSubgroupAsymptotics.ThreePointTransitiveCubicMembership

/-! The two actual local observations and their physical cubic translates
separate the SAME original coarse kernel. Original local actions may be
intransitive; only their full local range is observed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairElementaryCubicObservation
variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  [MulAction.IsPretransitive U X]
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
  (A : Rep (ZMod 2) (SixPairNestedTopFrames.nestedFrame F E).top.range)
  (D : OriginalKernelModuleChart
    (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict A)

private theorem cubic_orbit : ∀ i : Fin 3,∃ c : CyclicThree,
    (OddMarkerTernaryChart.embedding c)⁻¹ 0=i := by decide +kernel

include D in
 theorem exists_separating_observation
    (hsquare : ∀ k : (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict.ker,k^2=1) :
    ∃ q : A →ₗ[ZMod 2] (Fin 2 → ZMod 2),∀ v : A,
      (∀ c : CyclicThree,q (A.ρ
        (TwoBinaryThreePermutationCoordinates.cubicHom
          (SixPairNestedTopFrames.nestedFrame F E).top.range
          (ThreePointTransitiveCubicMembership.frame_rotation_mem
            (SixPairNestedTopFrames.nestedFrame F E)
            (fun x y => MulAction.exists_smul_eq U x y)) c) v)=0) → v=0 := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let pi := C.top.rangeRestrict
  have hk : pi.ker=C.top.ker := by
    ext g
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  let cast := MulEquiv.subgroupCongr hk
  let cubic := TwoBinaryThreePermutationCoordinates.cubicHom C.top.range
    (ThreePointTransitiveCubicMembership.frame_rotation_mem C
      (fun x y => MulAction.exists_smul_eq U x y))
  obtain ⟨q,hq⟩ := SixPairElementaryLocalObservation.exists_observation F E A D hsquare
  refine ⟨q,?_⟩
  intro v hv
  let k := D.equiv (Multiplicative.ofAdd v)
  let u := cast k
  have hu : u=1 := by
    apply C.kernelCoordinates_joint_injective
    funext i
    change C.kernelCoordinate i u=C.kernelCoordinate i 1
    rw [map_one]
    obtain ⟨c,hc⟩ := cubic_orbit i
    obtain ⟨g,hg⟩ := C.top.rangeRestrict_surjective (cubic c)
    have hg' : C.top g=OddMarkerTernaryChart.embedding c :=
      congrArg (fun t : C.top.range => (t : Equiv.Perm (Fin 3))) hg
    have hi : (C.top g)⁻¹ 0=i := by rw [hg']; exact hc
    have hcast : cast (D.equiv (Multiplicative.ofAdd (A.ρ (cubic c) v)))=
        MulAut.conjNormal g u := by
      apply Subtype.ext
      change (D.equiv (Multiplicative.ofAdd (A.ρ (cubic c) v)) : U)=
        g*(k : U)*g⁻¹
      rw [←hg]
      exact D.conjugate g v
    have hobs : C.kernelCoordinate 0 (MulAut.conjNormal g u)=1 := by
      rw [←hcast]
      exact (hq _).mp (hv c)
    rw [SixPairLocalKernelConjugation.coordinate_conjugate F E,hi] at hobs
    let l := (C.wreathEmbedding g).left 0
    apply (MulAut.conj l).injective
    rw [map_one]
    exact hobs
  have hkone : k=1 := cast.injective (hu.trans (map_one cast).symm)
  have hvone : Multiplicative.ofAdd v=1 :=
    D.equiv.injective (hkone.trans D.equiv.map_one.symm)
  exact congrArg Multiplicative.toAdd hvone

end SymmetricSubgroupAsymptotics.SixPairElementaryCubicObservation
