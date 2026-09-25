import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces

/-! A linear factorization certifies the complete fixed preimage using
only the retained bases. This replaces enumeration of all ambient vectors
by a checked sparse factor matrix, without assuming a rank or capacity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryCoordinateSpace
variable {w d : ℕ} (C : BinaryCoordinateSpace w d)

def defect : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2) :=
  LinearMap.id-C.inclusion.comp C.coordinates

theorem defect_eq_zero_iff (v : Fin w → ZMod 2) : C.defect v=0 ↔ v∈C.space := by
  change v-C.inclusion (C.coordinates v)=0 ↔ _
  rw [sub_eq_zero,C.mem_iff]
  exact eq_comm

end BinaryCoordinateSpace

variable {G ι : Type} [Group G] {w k c d : ℕ}

def binaryCoordinate_generatorDefects
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2))
    (generators : ι → G) (C : BinaryCoordinateSpace w c) :
    (Fin w → ZMod 2) →ₗ[ZMod 2] (ι → Fin w → ZMod 2) :=
  LinearMap.pi (fun j => C.defect.comp (ρ (generators j)-LinearMap.id))

theorem binaryCoordinate_generatorDefects_zero_iff
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2))
    (generators : ι → G) (C : BinaryCoordinateSpace w c) (v : Fin w → ZMod 2) :
    binaryCoordinate_generatorDefects ρ generators C v=0 ↔
      ∀j,ρ (generators j) v-v∈C.space := by
  constructor
  · intro h j
    exact (C.defect_eq_zero_iff _).mp (congrFun h j)
  · intro h
    funext j
    exact (C.defect_eq_zero_iff _).mpr (h j)

/-- Basis containment and a linear factor witness prove the full kernel
identity. In particular D is not just a chosen collection of fixed vectors. -/
theorem binaryCoordinate_kernel_of_factor {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (K : BinaryCoordinateSpace w k) (D : BinaryCoordinateSpace w d)
    (L : (Fin w → ZMod 2) →ₗ[ZMod 2] W)
    (R : W →ₗ[ZMod 2] (Fin w → ZMod 2))
    (hDK : ∀i,D.inclusion (Pi.single i 1)∈K.space)
    (hDL : ∀i,L (D.inclusion (Pi.single i 1))=0)
    (hfactor : ∀i,D.defect (K.inclusion (Pi.single i 1))=
      R (L (K.inclusion (Pi.single i 1)))) :
    ∀v,v∈D.space ↔ v∈K.space ∧ L v=0 := by
  have hdK := D.le_of_basis_mem K.space hDK
  have hdL : D.space≤L.ker := D.le_of_basis_mem L.ker hDL
  have hk : K.space≤(D.defect-R.comp L).ker := by
    apply K.le_of_basis_mem
    intro i
    change D.defect (K.inclusion (Pi.single i 1))-
      R (L (K.inclusion (Pi.single i 1)))=0
    exact sub_eq_zero.mpr (hfactor i)
  intro v
  constructor
  · intro hv
    exact ⟨hdK hv,hdL hv⟩
  · rintro ⟨hv,hl⟩
    apply (D.defect_eq_zero_iff v).mp
    have he : D.defect v-R (L v)=0 := hk hv
    simpa only [hl,map_zero,sub_zero] using he

/-- Sparse Gaussian factors checked on the original K basis certify the
complete generator-fixed predicate used by the physical cut installer. -/
theorem binaryCoordinate_fixed_of_factor
    (K : BinaryCoordinateSpace w k) (C : BinaryCoordinateSpace w c)
    (D : BinaryCoordinateSpace w d)
    (ρ : Representation (ZMod 2) G (Fin w → ZMod 2)) (generators : ι → G)
    (R : (ι → Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))
    (hDK : ∀i,D.inclusion (Pi.single i 1)∈K.space)
    (hDL : ∀i j,ρ (generators j) (D.inclusion (Pi.single i 1))-
      D.inclusion (Pi.single i 1)∈C.space)
    (hfactor : ∀i,D.defect (K.inclusion (Pi.single i 1))=
      R (binaryCoordinate_generatorDefects ρ generators C (K.inclusion (Pi.single i 1)))) :
    ∀v,v∈D.space ↔ v∈K.space ∧ ∀j,ρ (generators j) v-v∈C.space := by
  intro v
  rw [←binaryCoordinate_generatorDefects_zero_iff]
  exact binaryCoordinate_kernel_of_factor K D _ R hDK
    (fun i => (binaryCoordinate_generatorDefects_zero_iff ρ generators C _).mpr (hDL i))
    hfactor v

end SymmetricSubgroupAsymptotics
