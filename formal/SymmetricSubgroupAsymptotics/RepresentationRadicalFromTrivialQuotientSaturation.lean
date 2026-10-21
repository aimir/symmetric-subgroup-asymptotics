import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Lean.Elab.Tactic.Omega

/-! A fixed quotient and the sharp intrinsic head cap identify the entire
original radical. This avoids separate selected displacement witnesses
when an original-row certificate already kills a state modulo R. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {k G V : Type} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]

theorem representation_radical_eq_of_trivial_quotient_head_cap
    (rho : Representation k G V) (W : Subrepresentation rho) (R : Submodule k V)
    (hfixed : ∀ g : G, ∀ v ∈ W.toSubmodule, rho g v - v ∈ R)
    (c : ℕ) (hcap : Module.finrank k W.toRepresentation.Coinvariants ≤ c)
    (hdim : Module.finrank k W.toSubmodule = Module.finrank k R + c) :
    (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype = R := by
  let K := Representation.Coinvariants.ker W.toRepresentation
  have hle : K.map W.toSubmodule.subtype ≤ R := by
    apply Submodule.map_le_iff_le_comap.mpr
    change Submodule.span k (Set.range fun gv : G × W.toSubmodule =>
      W.toRepresentation gv.1 gv.2 - gv.2) ≤ R.comap W.toSubmodule.subtype
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change rho g (v : V) - (v : V) ∈ R
    exact hfixed g v.val v.property
  have hker := K.finrank_quotient_add_finrank
  change Module.finrank k W.toRepresentation.Coinvariants + Module.finrank k K =
    Module.finrank k W.toSubmodule at hker
  have hmap : Module.finrank k (K.map W.toSubmodule.subtype) = Module.finrank k K :=
    Submodule.finrank_map_subtype_eq W.toSubmodule K
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hmono := Submodule.finrank_mono hle
  omega

end SymmetricSubgroupAsymptotics
