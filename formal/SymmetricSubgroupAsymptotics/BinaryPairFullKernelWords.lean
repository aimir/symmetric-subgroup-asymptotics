import SymmetricSubgroupAsymptotics.BinaryPairFullKernelGenerators

/-! Literal words in an original pair frame provide the full-kernel
sharing hypotheses. One kernel element and prescribed transitive
transports certify every individual pair flip in the original group. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Fintype I] [DecidableEq I]
  {U : Subgroup (Equiv.Perm X)}

theorem uniform_of_full_pair_kernel_words (F : BinaryPairFrame U I)
    (o : I) (k : U) (q : I → U)
    (hk : F.top k = 1)
    (hq : ∀ i, F.top (q i) o = i)
    (hbits : ∀ i x,
      (F.frame.symm (((q i * k * (q i)⁻¹ : U) : Equiv.Perm X)
        (F.frame (x, 0)))).2 = (Pi.single i 1 : I → ZMod 2) x)
    (n : ℕ)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) n) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) n := by
  let base : F.top.ker := ⟨k, hk⟩
  let flip (i : I) : F.top.ker := MulAut.conjNormal (q i) base
  have hflip (i : I) : F.bits (flip i) = Pi.single i (1 : ZMod 2) := by
    funext x
    exact hbits i x
  have htrans (i j : I) : ∃ g : U, F.top g i = j := by
    refine ⟨q j * (q i)⁻¹, ?_⟩
    rw [map_mul, map_inv]
    change F.top (q j) ((F.top (q i))⁻¹ i) = j
    have hi : (F.top (q i))⁻¹ i = o := by
      calc
        _ = (F.top (q i))⁻¹ (F.top (q i) o) :=
          congrArg (fun x ↦ (F.top (q i))⁻¹ x) (hq i).symm
        _ = o := (F.top (q i)).symm_apply_apply o
    rw [hi, hq]
  exact F.uniform_of_full_pair_kernel_coordinateTop
    (fun i ↦ ⟨flip i, hflip i⟩) htrans n hpair

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
