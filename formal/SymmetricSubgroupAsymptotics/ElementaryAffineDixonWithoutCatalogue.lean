import SymmetricSubgroupAsymptotics.ElementaryAffineDixonOrder
import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! Exact elementary affine orders close Dixon's bounded primitive step.
The only finite receipt is on prime fields and dimensions with degree<32;
the existing dimension-sensitive estimate handles every larger degree. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.ElementaryDixonOrderProof.WithoutCatalogue
open Non2UnipotentPrefixFiniteMenu

private theorem small_affine_cubic_receipt :
    ∀ p : Fin 32,∀ d : Fin 5,p.val.Prime → 0<d.val → p.val^d.val<32 →
      fullAffineOrder p.val d.val^3≤24^(p.val^d.val-1) := by decide +kernel

theorem affine_cubic_order
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X) : Nat.card G^3≤24^(Nat.card X-1) := by
  by_cases hn : 32≤Nat.card X
  · exact ElementaryDixonOrderProof.affine_cubic_order G X P hn
  · obtain ⟨p,d,hp,hd,hdeg,hdiv,hne⟩ :=
      P.exists_prime_dimension_order_divisor inferInstance
    have hp32 : p<32 := by
      have hppow : p≤p^d := by
        simpa only [pow_one] using
          (Nat.pow_le_pow_right hp.pos hd)
      omega
    have hd5 : d<5 := by
      by_contra h
      have h5 : 5≤d := by omega
      have h32 : 32≤p^d := calc
        32=2^5 := by decide
        _ ≤ p^5 := Nat.pow_le_pow_left hp.two_le 5
        _ ≤ p^d := Nat.pow_le_pow_right hp.pos h5
      omega
    have hsmall := small_affine_cubic_receipt ⟨p,hp32⟩ ⟨d,hd5⟩ hp hd
      (by change p^d<32; omega)
    have hbound := Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv) 3
    exact hbound.trans (by simpa only [←hdeg] using hsmall)

theorem primitive_order
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    [IsSolvable G] : Nat.card G^3≤24^(Nat.card X-1) := by
  cases Classical.choice (PrimitiveSocleRawStructure.publishedONanScottStructure G X) with
  | inr P => exact affine_cubic_order G X P
  | inl D =>
      let i : Fin D.factorCount := ⟨0,D.factorCount_pos⟩
      let f : finiteGroupSocle G →* D.Simple :=
        (Pi.evalMonoidHom (fun _ : Fin D.factorCount => D.Simple) i).comp
          D.socleEquiv.toMonoidHom
      have hf : Function.Surjective f := by
        intro s
        exact ⟨D.socleEquiv.symm (fun _ => s),by simp [f]⟩
      have hs : IsSolvable D.Simple := solvable_of_surjective hf
      exact (D.noncommutative ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩).elim

end SymmetricSubgroupAsymptotics.ElementaryDixonOrderProof.WithoutCatalogue
