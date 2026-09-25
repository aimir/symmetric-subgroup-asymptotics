import SymmetricSubgroupAsymptotics.BinaryCheckedTransport
import SymmetricSubgroupAsymptotics.BinaryExceptionalBlocks
import SymmetricSubgroupAsymptotics.BinaryExceptional16Proper
import SymmetricSubgroupAsymptotics.BinaryExceptional8T16
import SymmetricSubgroupAsymptotics.BinaryExceptional8T20
import SymmetricSubgroupAsymptotics.BinaryExceptional8T21
import SymmetricSubgroupAsymptotics.BinaryExceptional16T1086

/-!
# Certified exceptional binary carriers

Each chart uses the committed literal permutations, both exact original
kernels, and a shared literal quotient. The physical carrier degree is the
source degree, even when the auxiliary quotient uses more points. The
transport theorems apply with an arbitrary untouched exterior group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryChart8T16

/-- The literal finite chart, with its two original kernel subgroups. -/
def chart : CheckedPermutationCarrier 8 16 :=
  CheckedPermutationCarrier.ofCertificates alphaCertificate betaCertificate
    (Subgroup.closure (Set.range quotientGenerators))
    (Subgroup.closure (Set.range axisGenerators))
    (Subgroup.closure (Set.range coverKernelGenerators))
    alpha_range beta_range alpha_kernel beta_kernel

/-- Reversible transport preserves the complete exterior correlation. -/
theorem reconstruct {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 8)) ∈ chart.axis → (x,1) ∈ H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap = H :=
  chart.transport_reconstruct H haxis

/-- Full original projection gives full projection on the literal carrier. -/
theorem full_carrier {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (hfull : ∀ x : chart.source, ∃ e : E, (x,e) ∈ H) :
    ∀ y : chart.carrier, ∃ e : E, (y,e) ∈ chart.transport H :=
  chart.transport_full_carrier H hfull

end BinaryChart8T16

namespace BinaryChart8T20

/-- The literal finite chart, with its two original kernel subgroups. -/
def chart : CheckedPermutationCarrier 8 16 :=
  CheckedPermutationCarrier.ofCertificates alphaCertificate betaCertificate
    (Subgroup.closure (Set.range quotientGenerators))
    (Subgroup.closure (Set.range axisGenerators))
    (Subgroup.closure (Set.range coverKernelGenerators))
    alpha_range beta_range alpha_kernel beta_kernel

/-- Reversible transport preserves the complete exterior correlation. -/
theorem reconstruct {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 8)) ∈ chart.axis → (x,1) ∈ H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap = H :=
  chart.transport_reconstruct H haxis

/-- Full original projection gives full projection on the literal carrier. -/
theorem full_carrier {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (hfull : ∀ x : chart.source, ∃ e : E, (x,e) ∈ H) :
    ∀ y : chart.carrier, ∃ e : E, (y,e) ∈ chart.transport H :=
  chart.transport_full_carrier H hfull

end BinaryChart8T20

namespace BinaryChart8T21

/-- The literal finite chart, with its two original kernel subgroups. -/
def chart : CheckedPermutationCarrier 8 16 :=
  CheckedPermutationCarrier.ofCertificates alphaCertificate betaCertificate
    (Subgroup.closure (Set.range quotientGenerators))
    (Subgroup.closure (Set.range axisGenerators))
    (Subgroup.closure (Set.range coverKernelGenerators))
    alpha_range beta_range alpha_kernel beta_kernel

/-- Reversible transport preserves the complete exterior correlation. -/
theorem reconstruct {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 8)) ∈ chart.axis → (x,1) ∈ H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap = H :=
  chart.transport_reconstruct H haxis

/-- Full original projection gives full projection on the literal carrier. -/
theorem full_carrier {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (hfull : ∀ x : chart.source, ∃ e : E, (x,e) ∈ H) :
    ∀ y : chart.carrier, ∃ e : E, (y,e) ∈ chart.transport H :=
  chart.transport_full_carrier H hfull

end BinaryChart8T21

namespace BinaryChart16T1086

/-- The literal finite chart, with its two original kernel subgroups. -/
def chart : CheckedPermutationCarrier 16 16 :=
  CheckedPermutationCarrier.ofCertificates alphaCertificate betaCertificate
    (Subgroup.closure (Set.range quotientGenerators))
    (Subgroup.closure (Set.range axisGenerators))
    (Subgroup.closure (Set.range coverKernelGenerators))
    alpha_range beta_range alpha_kernel beta_kernel

/-- Reversible transport preserves the complete exterior correlation. -/
theorem reconstruct {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (haxis : ∀ x : chart.source,
      (x : Equiv.Perm (Fin 16)) ∈ chart.axis → (x,1) ∈ H) :
    ((chart.transport H).map chart.carrierMap).comap chart.sourceMap = H :=
  chart.transport_reconstruct H haxis

/-- Full original projection gives full projection on the literal carrier. -/
theorem full_carrier {E : Type*} [Group E] (H : Subgroup (chart.source × E))
    (hfull : ∀ x : chart.source, ∃ e : E, (x,e) ∈ H) :
    ∀ y : chart.carrier, ∃ e : E, (y,e) ∈ chart.transport H :=
  chart.transport_full_carrier H hfull

end BinaryChart16T1086

end SymmetricSubgroupAsymptotics
