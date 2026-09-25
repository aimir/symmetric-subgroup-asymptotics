import SymmetricSubgroupAsymptotics.BinaryPairSharedCutInstall
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard

/-! Bind reusable coordinate certificates to the literal physical action.
The shared group is identified with the actual top by one specified
isomorphism; every original normal and its full top image remain retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X H : Type} [Group H] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- A checked original permutation exhibits an actual correlated flip. -/
theorem vector_mem_kernelSpace_of_action (u : U) (v : Fin w → ZMod 2)
    (h : ∀ p : Fin w × ZMod 2,
      F.frame.symm ((u : Equiv.Perm X) (F.frame p))=(p.1,p.2+v p.1)) :
    v∈F.kernelSpace := by
  have hu : F.top u=1 := by
    apply Equiv.ext
    intro i
    have he := congrArg Prod.fst (h (i,0))
    rw [F.intertwine] at he
    exact he
  let k : F.top.ker := ⟨u,hu⟩
  refine ⟨Additive.ofMul k,?_⟩
  funext i
  have he := congrArg Prod.snd (h (i,0))
  simpa only [zero_add] using he

variable (ρ : Representation (ZMod 2) H (Fin w → ZMod 2))
    (e : H ≃* F.top.range)
    (he : ∀ g v, ρ g v=F.coordinateTopAction (e g) v)

/-- Transport preserves the literal ambient subspace. -/
def sharedSubrepresentation (S : Subrepresentation ρ) :
    Subrepresentation F.coordinateTopAction where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule t v hv := by
    rw [← e.apply_symm_apply t,← he]
    exact S.apply_mem_toSubmodule _ hv

/-- Every original normal supplies an axis in the independently complete
shared registry, including nonabelian proper subdirect lifts. -/
def sharedOriginalAxis (N : Subgroup U) [N.Normal] : Subrepresentation ρ where
  toSubmodule := F.ambientAxis N
  apply_mem_toSubmodule g v hv := by
    rw [he]
    exact (F.axisSubrepresentation N).apply_mem_toSubmodule _ hv

theorem shared_cut (K A C D : Subrepresentation ρ)
    (hK : K.toSubmodule=F.kernelSpace) (h : BinaryCoordinateCutData ρ K A C D) :
    BinaryCoordinateCutData F.coordinateTopAction F.kernelSubrepresentation
      (F.sharedSubrepresentation ρ e he A) (F.sharedSubrepresentation ρ e he C)
      (F.sharedSubrepresentation ρ e he D) where
  axis_le_cut := h.axis_le_cut
  cut_le_kernel := by
    change C.toSubmodule≤F.kernelSpace
    rw [← hK]
    exact h.cut_le_kernel
  central t v hv := by
    change F.coordinateTopAction t v-v∈A.toSubmodule
    rw [← e.apply_symm_apply t,← he]
    exact h.central _ v hv
  fixed_iff v := by
    change v∈D.toSubmodule ↔ v∈F.kernelSpace ∧
      ∀ t, F.coordinateTopAction t v-v∈C.toSubmodule
    rw [h.fixed_iff,hK]
    apply and_congr_right
    intro _
    constructor
    · intro h t
      rw [← e.apply_symm_apply t,← he]
      exact h _
    · intro h g
      rw [he]
      exact h _

/-- An axis equality in the faithful coordinates is the exact original
intersection equality needed by the local certificate installer. -/
theorem shared_axis_eq (N : Subgroup U) [N.Normal] (A : Subrepresentation ρ)
    (hA : F.sharedOriginalAxis ρ e he N=A) :
    F.top.ker⊓N=F.coordinateSubgroup A.toSubmodule := by
  have heq : F.ambientAxis N=A.toSubmodule := congrArg Subrepresentation.toSubmodule hA
  rw [← heq,F.coordinateSubgroup_ambientAxis]

end SymmetricSubgroupAsymptotics.BinaryPairFrame
