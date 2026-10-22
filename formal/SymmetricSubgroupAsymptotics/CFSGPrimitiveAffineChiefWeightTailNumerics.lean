import SymmetricSubgroupAsymptotics.CFSGPrimitiveChiefWeightTailPilot
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTailNumerics

/-! The guarded composite prime-power chief-weight arithmetic after the
selected full-valuation pilot. At most32 by10 numerical parameter choices;
there is no action, complement census or composition-length input. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineChiefWeightTailNumerics

private theorem bounded_receipt : ∀ p : Fin 32, ∀ d : Fin 10,
    p.val.Prime → 2 ≤ d.val → 45 ≤ p.val^d.val → p.val^d.val < 1024 →
    10*(fullAffineOrder p.val d.val).factorization 3 ≤ 3*p.val^d.val := by
  unfold fullAffineOrder fullLinearOrder
  decide +kernel

theorem fullAffineOrder_threeTenths_tail {p d : ℕ} (hp : p.Prime)
    (hd : 2 ≤ d) (hf : 45 ≤ p^d) (hs : p^d < 1024) :
    10*(fullAffineOrder p d).factorization 3 ≤ 3*p^d := by
  obtain ⟨hp32,hd10⟩ := CFSGPrimitiveAffineTernaryTailNumerics.parameter_bounds hp hd hs
  exact bounded_receipt ⟨p,hp32⟩ ⟨d,hd10⟩ hp hd hf hs

end SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineChiefWeightTailNumerics
