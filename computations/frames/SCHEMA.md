# Exact encodings

All indices are one-based except binary bit positions. GAP permutations
act on the right. Group values in `.g` files are literal generated
permutation groups. The data files contain assignments only.

## Eight-block modules

Each of the 30 rows in `frames8.json` is

```text
[top_id, top_order, local_quotient_order, stabilizer_kernel_order,
 top_relative_binary_rank, sylow3_fixed_dimension, maximum_module_head,
 generator_matrices, invariant_module_bases]
```

The module is F2^16. Integer bit `i-1` is the coefficient of basis vector
`i`. A generator matrix is a list of 16 integers: entry `i` encodes the
image of basis vector `i`. A submodule basis is a list of such vectors;
the independent checker reduces it to a unique binary echelon basis.
The trivial and whole modules must occur, with no duplicate submodules.

`bindings8.g` defines `FrameEightTops` (24 literal groups) and
`FrameEightBindings` (30 rows aligned with the JSON). A binding row is

```text
[top_id, literal_kernel_N, generators_of_H, images_under_rho,
 right_coset_representatives, induced_group_generators,
 binary_basis_as_permutations]
```

Here `H` is the stabilizer of point 1, and `rho` maps onto the fixed C3
or S3 on `{1,2,3}`, fixing point 4. Its kernel is exactly `N`.
The induced action on 32 points is

```text
(i,k)^g = (j,k^rho(r_i*g*r_j^-1)),  H*r_i*g = H*r_j.
```

The binary basis is an independent generating sequence of the original
V4^8 translation group. The binding checker evaluates each matrix entry
as literal permutation conjugation in this basis.

## Sixteen-block witnesses

`tops16.g` defines `AffineFourDZeroClasses`, 29 actual degree-sixteen
actions, and `AffineFourDZeroRows`, their identifying construction rows.
Only the literal actions are required by the frame verifier.

`frames16.g` defines `DZeroUnpairedSixteenCertificates`, 38 records:

```text
[tag, literal_stabilizer_kernel_N, actual_odd_subgroup_A,
 binary_normalizer_element_g, numerical_row]
```

Tags 1–29 refer to the constructed tops. Tags 30–51 refer to
`PrimitiveGroup(16,tag-29)`; only nine frames in that range occur.
Distinct kernels for the same top remain separate records.

For tags 1–29, `A` is an actual Sylow three-subgroup, `g` is a binary
element of its normalizer, and the numerical row is

```text
[tag, top_order, top_relative_rank, local_quotient_order, kernel_order,
 normalizer_of_A_order, order_of_g, dim((M^A)^g), sum_bound]
```

For primitive tags the element `g` is the identity and the numerical row is

```text
[primitive_id, top_order, local_quotient_order, kernel_order,
 top_relative_rank, order_of_A, dim(M^A), sum_bound]
```

In both cases `sum_bound` is the displayed fixed dimension plus the top
relative binary rank. The checker recomputes this entire row.

`DZeroFourByFourRows` and `DZeroPrimitiveSixteenRows` repeat these numerical
tables for readability; the literal witness record is the authoritative
input. `DZeroPrimitiveEightLocalRows` has seven rows

```text
[primitive_id, group_order, orders_of_all_normal_subgroups,
 sorted_Sylow3_orbit_lengths, complete_relative_binary_rank]
```

The checker recomputes each complete normal menu, rather than treating
its length as a proof of completeness.
