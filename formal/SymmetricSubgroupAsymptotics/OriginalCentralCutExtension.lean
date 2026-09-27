import SymmetricSubgroupAsymptotics.BinaryPairPrefixChart
import SymmetricSubgroupAsymptotics.RepresentationFixedDisplacement

/-! Quotienting a literal original extension by a fixed central subspace.
The extension need not split, and its acting quotient need not have a
faithful permutation action. Both kernel charts retain the original maps. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalCentralCutExtension

variable {k Q B : Type} [Field k] [Group Q] [Group B]
    (π : Q →* B) (A : Rep k B) (E : OriginalKernelModuleChart π A)
    (C : {C : Submodule k A // C ≤ A.ρ.invariants})

/-- The selected vectors embedded in the original group, through its kernel chart. -/
def cutHom : Multiplicative C.1 →* Q where
  toFun c := (E.equiv (Multiplicative.ofAdd c.toAdd.val) : Q)
  map_one' := by
    change (E.equiv 1 : Q) = 1
    simp only [map_one, OneMemClass.coe_one]
  map_mul' c d := by
    change (E.equiv (Multiplicative.ofAdd (c.toAdd.val+d.toAdd.val)) : Q) = _
    exact originalKernelChart_add π A E _ _

theorem cutHom_injective : Function.Injective (cutHom π A E C) := by
  intro c d h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd (E.equiv.injective (Subtype.ext h))

def cutGroup : Subgroup Q := (cutHom π A E C).range

theorem chart_mem_cutGroup (a : Multiplicative A) :
    (E.equiv a : Q) ∈ cutGroup π A E C ↔ a.toAdd ∈ C.1 := by
  constructor
  · rintro ⟨c,hc⟩
    have he : Multiplicative.ofAdd c.toAdd.val = a :=
      E.equiv.injective (Subtype.ext hc)
    exact (congrArg Multiplicative.toAdd he) ▸ c.toAdd.property
  · intro ha
    exact ⟨Multiplicative.ofAdd ⟨a.toAdd,ha⟩,rfl⟩

theorem cutGroup_le_kernel : cutGroup π A E C ≤ π.ker := by
  rintro _ ⟨c,rfl⟩
  exact (E.equiv (Multiplicative.ofAdd c.toAdd.val)).property

theorem cutGroup_central : cutGroup π A E C ≤ Subgroup.center Q := by
  rintro _ ⟨c,rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  have he := E.conjugate q c.toAdd.val
  rw [C.2 c.toAdd.property (π q)] at he
  change q * (E.equiv (Multiplicative.ofAdd c.toAdd.val) : Q) =
    (E.equiv (Multiplicative.ofAdd c.toAdd.val) : Q) * q
  have hm := congrArg (fun z : Q => z*q) he
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm.symm

instance cutGroup_normal : (cutGroup π A E C).Normal := by
  refine ⟨fun a ha q => ?_⟩
  have hc := Subgroup.mem_center_iff.mp (cutGroup_central π A E C ha) q
  rw [hc,mul_assoc,mul_inv_cancel,mul_one]
  exact ha

def first : Q →* Q ⧸ cutGroup π A E C := QuotientGroup.mk' _

theorem first_surjective : Function.Surjective (first π A E C) :=
  QuotientGroup.mk'_surjective _

theorem first_central : FusionCentralKernel (first π A E C) :=
  fusionCentralKernel_quotient _ (cutGroup_central π A E C)

/-- The first kernel is exactly the chosen original vector space. -/
def centralEquiv : (first π A E C).ker ≃* Multiplicative C.1 :=
  (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (cutGroup π A E C))).trans
    (MonoidHom.ofInjective (cutHom_injective π A E C)).symm

def base : (Q ⧸ cutGroup π A E C) →* B :=
  QuotientGroup.lift _ π (cutGroup_le_kernel π A E C)

@[simp] theorem base_first (q : Q) : base π A E C (first π A E C q) = π q := rfl

theorem base_surjective (hπ : Function.Surjective π) :
    Function.Surjective (base π A E C) := by
  intro b
  obtain ⟨q,rfl⟩ := hπ b
  exact ⟨first π A E C q,rfl⟩

/-- The original quotient representation on precisely A/C. -/
def quotientModule : Rep k B := Rep.of (centralQuotientRepresentation A.ρ C.1 C.2)

def moduleProjection : Multiplicative A →* Multiplicative (quotientModule A C) :=
  C.1.mkQ.toAddMonoidHom.toMultiplicative

theorem moduleProjection_surjective : Function.Surjective (moduleProjection A C) := by
  intro a
  obtain ⟨v,hv⟩ := C.1.mkQ_surjective a.toAdd
  exact ⟨Multiplicative.ofAdd v,congrArg Multiplicative.ofAdd hv⟩

def kernelProjection : Multiplicative A →* (base π A E C).ker where
  toFun a := ⟨first π A E C (E.equiv a : Q), by
    change π (E.equiv a : Q) = 1
    exact (E.equiv a).property⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one,OneMemClass.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    change first π A E C (E.equiv (a*b) : Q) = _
    simp only [map_mul,Subgroup.coe_mul]

theorem kernelProjection_surjective : Function.Surjective (kernelProjection π A E C) := by
  intro r
  obtain ⟨q,hq⟩ := first_surjective π A E C r.val
  have hqK : q ∈ π.ker := by
    change π q = 1
    rw [← base_first π A E C q,hq]
    exact r.property
  refine ⟨E.equiv.symm ⟨q,hqK⟩,?_⟩
  apply Subtype.ext
  change first π A E C (E.equiv (E.equiv.symm ⟨q,hqK⟩) : Q) = r.val
  rw [MulEquiv.apply_symm_apply]
  exact hq

theorem projection_kernels_eq :
    (moduleProjection A C).ker = (kernelProjection π A E C).ker := by
  ext a
  change moduleProjection A C a = 1 ↔ kernelProjection π A E C a = 1
  rw [Subtype.ext_iff]
  change C.1.mkQ a.toAdd = 0 ↔ first π A E C (E.equiv a : Q) = 1
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact (chart_mem_cutGroup π A E C a).symm.trans
    (QuotientGroup.eq_one_iff _).symm

def kernelEquiv : Multiplicative (quotientModule A C) ≃* (base π A E C).ker :=
  binaryPair_sameKernelEquiv (moduleProjection A C) (kernelProjection π A E C)
    (moduleProjection_surjective A C) (kernelProjection_surjective π A E C)
    (projection_kernels_eq π A E C)

@[simp] theorem kernelEquiv_projection (a : Multiplicative A) :
    kernelEquiv π A E C (moduleProjection A C a) = kernelProjection π A E C a :=
  binaryPair_sameKernelEquiv_apply _ _ _ _ _ a

/-- Exact conjugation on the second kernel of the unchanged original tower. -/
def quotientChart : OriginalKernelModuleChart (base π A E C) (quotientModule A C) where
  equiv := kernelEquiv π A E C
  conjugate r a := by
    obtain ⟨q,rfl⟩ := first_surjective π A E C r
    obtain ⟨v,rfl⟩ := C.1.mkQ_surjective a
    have he (v : A) :
        (kernelEquiv π A E C (moduleProjection A C (Multiplicative.ofAdd v)) :
          Q ⧸ cutGroup π A E C) = first π A E C (E.equiv (Multiplicative.ofAdd v) : Q) :=
      congrArg Subtype.val (kernelEquiv_projection π A E C _)
    change (kernelEquiv π A E C
      (moduleProjection A C (Multiplicative.ofAdd (A.ρ (π q) v))) :
        Q ⧸ cutGroup π A E C) = _
    rw [he]
    have hv := he v
    change (kernelEquiv π A E C (Multiplicative.ofAdd (C.1.mkQ v)) :
      Q ⧸ cutGroup π A E C) = _ at hv
    rw [hv,E.conjugate,map_mul,map_mul,map_inv]

end SymmetricSubgroupAsymptotics.OriginalCentralCutExtension
