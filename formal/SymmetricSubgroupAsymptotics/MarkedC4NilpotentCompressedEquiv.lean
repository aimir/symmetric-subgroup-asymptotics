import SymmetricSubgroupAsymptotics.MarkedC4NilpotentCompressedImages
import SymmetricSubgroupAsymptotics.MarkedC4CoprimeGridEquivariance

/-! Faithfulness of the ORIGINAL action gives an actual equivalence to
the two compressed physical permutation images. No split/equivariance
or kernel-injectivity premise is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentCompressedEquiv
open NilpotentSylowFactors NilpotentPermutationGrid NilpotentCompressedImages
variable (G X : Type) [Group G] [Finite G] [Group.IsNilpotent G]
  [MulAction G X] [Finite X] [FaithfulSMul G X]

private theorem fixes_of_kernels (p : Binary G) (o : OddFactor G)
    (hp : p∈(binaryAction G X).ker) (ho : o∈(oddAction G X).ker) :
    ∀ x : X, (equiv G).symm (p,o) • x=x := by
  letI := factorAction G X
  have hpf := (binary_kernel_iff G X p).mp hp
  have hof := (odd_kernel_iff G X o).mp ho
  intro x
  let z := MulAction.selfEquivSigmaOrbits (Factors G) X x
  have hzval : (z.2 : X)=x := rfl
  have hgrid : CoprimePhysicalGrid.orbitGrid (factors_coprime G) z.1.out ((p,o) • z.2)=
      CoprimePhysicalGrid.orbitGrid (factors_coprime G) z.1.out z.2 := by
    rw [CoprimeGridEquivariance.grid_equivariant]
    apply Prod.ext
    · exact hpf z.1 _
    · exact hof z.1 _
  have hz := (CoprimePhysicalGrid.orbitGrid (factors_coprime G) z.1.out).injective hgrid
  have hv := congrArg Subtype.val hz
  change (equiv G).symm (p,o) • (z.2 : X)=(z.2 : X) at hv
  simpa only [hzval] using hv

def map : G →* BinaryImage G X × OddImage G X :=
  (((binaryAction G X).rangeRestrict).comp
    ((MonoidHom.fst _ _).comp (equiv G).toMonoidHom)).prod
  (((oddAction G X).rangeRestrict).comp
    ((MonoidHom.snd _ _).comp (equiv G).toMonoidHom))

theorem map_surjective : Function.Surjective (map G X) := by
  rintro ⟨⟨p,hp⟩,⟨o,ho⟩⟩
  obtain ⟨p',rfl⟩ := hp
  obtain ⟨o',rfl⟩ := ho
  refine ⟨(equiv G).symm (p',o'),?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change binaryAction G X ((equiv G) ((equiv G).symm (p',o'))).1=binaryAction G X p'
    rw [(equiv G).apply_symm_apply]
  · apply Subtype.ext
    change oddAction G X ((equiv G) ((equiv G).symm (p',o'))).2=oddAction G X o'
    rw [(equiv G).apply_symm_apply]

theorem map_injective : Function.Injective (map G X) := by
  apply (MonoidHom.ker_eq_bot_iff (map G X)).mp
  apply le_antisymm _ bot_le
  intro g hg
  have he := MonoidHom.mem_ker.mp hg
  have hp : (equiv G g).1∈(binaryAction G X).ker := by
    apply MonoidHom.mem_ker.mpr
    exact congrArg (fun z : BinaryImage G X × OddImage G X => (z.1 : Equiv.Perm (BinarySupport G X))) he
  have ho : (equiv G g).2∈(oddAction G X).ker := by
    apply MonoidHom.mem_ker.mpr
    exact congrArg (fun z : BinaryImage G X × OddImage G X => (z.2 : Equiv.Perm (OddSupport G X))) he
  apply Subgroup.mem_bot.mpr
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  have h := fixes_of_kernels G X (equiv G g).1 (equiv G g).2 hp ho x
  simpa only [Prod.mk.eta,MulEquiv.symm_apply_apply,one_smul] using h

/-- Concrete binary/odd physical image equivalence for this original group. -/
def groupEquiv : G ≃* BinaryImage G X × OddImage G X :=
  MulEquiv.ofBijective (map G X) ⟨map_injective G X,map_surjective G X⟩

theorem card_hom_le_binary :
    Nat.card (G →* Multiplicative (ZMod 4))≤
      Nat.card (BinaryImage G X →* Multiplicative (ZMod 4)) :=
  CoprimeProductCharacters.card_hom_le_of_split (groupEquiv G X)
    (odd_image_card_coprime_four G X)
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentCompressedEquiv
