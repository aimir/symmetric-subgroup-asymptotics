import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation
import SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements

/-! A genuine orthogonal two-node orbit gives fixed root words in the
ORIGINAL generated twist graph. Commutation is on the original integral
Serre lattice; neither a natural-image lift nor derived membership is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerrePairedFixedRoots
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (perm : Fin n → Fin n) (exponent : Fin n → ℕ)

theorem paired_root_mem_fixed (neg : Bool) (i : Fin n) (hi : A i (perm i) = 0)
    (hpi : perm (perm i) = i) (t : K)
    (ht : (t ^ exponent i) ^ exponent (perm i) = t) :
    ((modelRoot A K neg i t) * (modelRoot A K neg (perm i) (t ^ exponent i))).val ∈
      fixedSubgroup A K perm exponent := by
  let u := modelRoot A K neg i t
  let v := modelRoot A K neg (perm i) (t ^ exponent i)
  have huv : (u.val, v.val) ∈ twistGraph A K perm exponent :=
    Subgroup.subset_closure ⟨neg, i, t, rfl, rfl⟩
  have hvu : (v.val, u.val) ∈ twistGraph A K perm exponent := by
    apply Subgroup.subset_closure
    refine ⟨neg, perm i, t ^ exponent i, rfl, ?_⟩
    change IsRootElement A K neg (perm (perm i)) ((t ^ exponent i) ^ exponent (perm i)) u.val
    rw [hpi, ht]
    rfl
  have hc : u.val * v.val = v.val * u.val :=
    congrArg (fun g : Model A K => g.val)
      (CFSGSerreCrossNodeCommutation.modelRoots_commute_of_cartan_zero A K neg i (perm i) hi
        t (t ^ exponent i)).eq
  refine ⟨(u * v).property, ?_⟩
  have hm := (twistGraph A K perm exponent).mul_mem huv hvu
  change (u.val * v.val, v.val * u.val) ∈ _ at hm
  change (u.val * v.val, u.val * v.val) ∈ twistGraph A K perm exponent
  rwa [← hc] at hm

def pairedFixedRoot (neg : Bool) (i : Fin n) (hi : A i (perm i) = 0)
    (hpi : perm (perm i) = i) (t : K) (ht : (t ^ exponent i) ^ exponent (perm i) = t) :
    fixedSubgroup A K perm exponent :=
  ⟨((modelRoot A K neg i t) * (modelRoot A K neg (perm i) (t ^ exponent i))).val,
    paired_root_mem_fixed A K perm exponent neg i hi hpi t ht⟩

theorem pairedFixedRoot_toModel (neg : Bool) (i : Fin n) (hi : A i (perm i) = 0)
    (hpi : perm (perm i) = i) (t : K) (ht : (t ^ exponent i) ^ exponent (perm i) = t) :
    CFSGSerreFixedRootElements.fixedToModel A K perm exponent
      (pairedFixedRoot A K perm exponent neg i hi hpi t ht) =
        modelRoot A K neg i t * modelRoot A K neg (perm i) (t ^ exponent i) := rfl

end SymmetricSubgroupAsymptotics.CFSGSerrePairedFixedRoots
