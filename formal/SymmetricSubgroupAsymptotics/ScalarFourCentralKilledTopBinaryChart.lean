import SymmetricSubgroupAsymptotics.ScalarFourCentralKilledCyclicTop
import SymmetricSubgroupAsymptotics.BinaryCoordinateSurjectiveQuotient

/-! The killed cyclic-top quotient has genuine binary coordinates of rank
at most the ORIGINAL central rank; cardinality alone is not used as a proxy. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
variable {Q T H : Type} [Group Q] [Group T] [Group H] [Finite Q] [Finite H] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

theorem killed_top_binary_chart (f : Q →* H) (hf : Function.Surjective f)
    (n : Q) (hn : D.top n=D.cubic) (hfn : f n=1)
    (hcyclic : Subgroup.zpowers D.cubic=⊤) :
    ∃ r : ℕ, r≤c ∧ Nonempty (H ≃* (Fin r → Multiplicative (ZMod 2))) := by
  let q : D.active.ker →* H :=
    f.comp (D.top.ker.subtype.comp D.active.ker.subtype)
  have hq : Function.Surjective q := D.killed_top_central_surjective f hf n hn hfn hcyclic
  exact BinaryCoordinateSurjectiveQuotient.exists_chart
    D.centralCoordinates D.centralCoordinates_injective q hq

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
