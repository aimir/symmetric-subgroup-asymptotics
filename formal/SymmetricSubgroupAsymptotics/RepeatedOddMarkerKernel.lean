import SymmetricSubgroupAsymptotics.OddMarkerBinaryContraction

/-!
# The actual kernel of all repeated marker signs

Every original marker and the complete exterior are retained in one map.
A full S3 projection forces a full A3 projection of its actual joint kernel.
This does not assert that the kernel contains the product of the A3 factors:
diagonal kernels across repeated signs remain possible.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerKernel

variable {ι D : Type*} [Group D]

/-- All original signs are recorded together with the unchanged exterior. -/
def contraction : ((ι → OddMarkerGroup) × D) →*
    ((ι → Multiplicative (ZMod 2)) × D) where
  toFun x := (fun i => oddMarkerSign (x.1 i),x.2)
  map_one' := by
    apply Prod.ext
    · funext i
      exact map_one oddMarkerSign
    · rfl
  map_mul' x y := by
    apply Prod.ext
    · funext i
      exact map_mul oddMarkerSign (x.1 i) (y.1 i)
    · rfl

/-- Projection to one original marker, before any collapse or relabelling. -/
def coordinate (i : ι) : ((ι → OddMarkerGroup) × D) →* OddMarkerGroup where
  toFun x := x.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

def jointKernel (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Subgroup ((ι → OddMarkerGroup) × D) := H ⊓ contraction.ker

theorem mem_jointKernel (H : Subgroup ((ι → OddMarkerGroup) × D))
    (x : (ι → OddMarkerGroup) × D) :
    x ∈ jointKernel H ↔ x ∈ H ∧ (∀ i, oddMarkerSign (x.1 i)=1) ∧ x.2=1 := by
  change (x ∈ H ∧ (fun i => oddMarkerSign (x.1 i),x.2)=(1,1)) ↔ _
  rw [Prod.mk.injEq]
  simp only [funext_iff,Pi.one_apply]

private theorem alternating_pow_four_pow (g : OddMarkerGroup)
    (hg : g ∈ oddMarkerSign.ker) (k : ℕ) : g^(4^k)=g := by
  have hg4 : g^4=g := by
    rw [show (4:ℕ)=3+1 by rfl,pow_succ,oddMarker_kernel_cube g hg,one_mul]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,pow_mul,ih,hg4]

private theorem binary_pow_four_pow_succ (z : Multiplicative (ZMod 2))
    (k : ℕ) : z^(4^(k+1))=1 := by
  rw [pow_succ,Nat.mul_comm (4^k) 4,pow_mul]
  have hz : z^4=1 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,binary_mul_pow_two]
  rw [hz,one_pow]

/-- The actual joint kernel has a full A3 image on every full S3 marker.
The exponent only uses the original exterior element; no finiteness,
independent-marker assumption, or global exponent-four condition is needed. -/
theorem jointKernel_coordinate_full (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D)) (i : ι)
    (hfull : H.map (coordinate i)=⊤) :
    (jointKernel H).map (coordinate i)=oddMarkerSign.ker := by
  apply le_antisymm
  · rintro g ⟨x,hx,rfl⟩
    exact ((mem_jointKernel H x).mp hx).2.1 i
  · intro g hg
    have hm : g ∈ H.map (coordinate i) := by rw [hfull]; trivial
    obtain ⟨x,hx,hxi⟩ := Subgroup.mem_map.mp hm
    obtain ⟨k,hk⟩ := hD x.2
    have hext : x.2^(4^k)=1 := by
      rw [show (4:ℕ)^k=2^k*2^k by simpa using (mul_pow (2:ℕ) 2 k),
        pow_mul,hk,one_pow]
    have hext' : x.2^(4^(k+1))=1 := by
      rw [pow_succ,pow_mul,hext,one_pow]
    refine Subgroup.mem_map.mpr ⟨x^(4^(k+1)),?_,?_⟩
    · apply (mem_jointKernel H _).mpr
      refine ⟨H.pow_mem hx _,?_,hext'⟩
      intro j
      change oddMarkerSign ((x.1 j)^(4^(k+1)))=1
      rw [map_pow]
      exact binary_pow_four_pow_succ _ k
    · change (x.1 i)^(4^(k+1))=g
      change x.1 i=g at hxi
      rw [hxi]
      exact alternating_pow_four_pow g hg _

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerKernel

end
