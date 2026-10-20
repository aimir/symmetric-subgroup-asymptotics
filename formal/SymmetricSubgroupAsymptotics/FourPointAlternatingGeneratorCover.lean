import SymmetricSubgroupAsymptotics.AlternatingTopImageNormalGenerators

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPointAlternatingGeneratorCover

def a : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
def b : Equiv.Perm (Fin 4) where
  toFun := ![2,0,1,3]
  invFun := ![1,2,0,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def klein : Fin 4 → Equiv.Perm (Fin 4) :=
  let d := a*b⁻¹
  ![1,d,a*d*a⁻¹,a^2*d*(a^2)⁻¹]
private theorem cover : ∀ g : Equiv.Perm (Fin 4), Equiv.Perm.sign g = 1 →
    ∃ i : Fin 4, ∃ j : Fin 3, klein i * a^j.val = g := by decide +kernel

theorem alternating_le (H : Subgroup (Equiv.Perm (Fin 4)))
    (ha : a ∈ H) (hb : b ∈ H) : alternatingGroup (Fin 4) ≤ H := by
  intro g hg
  obtain ⟨i,j,rfl⟩ := cover g hg
  apply H.mul_mem ?_ (H.pow_mem ha j.val)
  fin_cases i
  · exact H.one_mem
  · exact H.mul_mem ha (H.inv_mem hb)
  · exact H.mul_mem (H.mul_mem ha (H.mul_mem ha (H.inv_mem hb))) (H.inv_mem ha)
  · exact H.mul_mem (H.mul_mem (H.pow_mem ha 2) (H.mul_mem ha (H.inv_mem hb)))
      (H.inv_mem (H.pow_mem ha 2))

end SymmetricSubgroupAsymptotics.FourPointAlternatingGeneratorCover
