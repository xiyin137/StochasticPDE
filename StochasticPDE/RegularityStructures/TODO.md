# Regularity Structures - Status and Sorry Dependency Audit

## Reconstruction Theorem Status

**`reconstruction_theorem`** (Reconstruction.lean:759) — **USES SORRY**

The theorem compiles and has a proof term, but **transitively depends on 3 sorry'd lemmas**
in the uniqueness argument. It is NOT fully proven until these are resolved.

### Blocking Sorrys (3 — directly on critical path)

1. **`pairing_eq_of_small_scale_bound`** (Reconstruction.lean:399)
   - Proposition 3.19 from Hairer 2014
   - Shows: small-scale bound O(λ^γ) with γ > 0 ⟹ pairing functions are equal
   - Requires: formal wavelet / Littlewood-Paley decomposition infrastructure
   - **Critical**: this is the mathematical heart of the uniqueness proof

2. **`pairing_eq_of_small_scale_eq`** scale > 1 case (Reconstruction.lean:427)
   - Extension of equality from scales in (0,1] to scales > 1
   - Requires: Littlewood-Paley decomposition

3. **`pairing_eq_of_small_scale_eq`** scale ≤ 0 case (Reconstruction.lean:430)
   - Extension to non-physical domain (scale ≤ 0)
   - May be resolvable by convention or domain restriction

### Dependency Chain

```
reconstruction_theorem (line 759) — proof term exists, USES SORRY
├── reconstruction_exists (line 587) — FULLY PROVEN ✓
│   └── Constructs R(f) = Π_x f(x) explicitly
└── reconstruction_unique (line 741) — USES SORRY
    └── reconstruction_pairing_unique (line 719) — USES SORRY
        └── reconstruction_pairing_unique_on_unit_interval (line 683) — USES SORRY
            └── pairing_eq_of_small_scale_eq (line 416) — USES SORRY
                ├── sorry at line 427 (scale > 1)
                ├── sorry at line 430 (scale ≤ 0)
                └── pairing_eq_of_small_scale_bound (line 381) — SORRY at line 399
```

### Non-blocking Sorrys in Reconstruction.lean (2)

4. **`reconstruction_continuous_in_model`** (line 796) — corollary, not used by main theorem
5. **`schauder_estimate`** (line 818) — application, not used by main theorem

---

## Full Sorry Count by File

### Reconstruction.lean — 5 sorrys
- `pairing_eq_of_small_scale_bound` (399) — **BLOCKS reconstruction_theorem**
- `pairing_eq_of_small_scale_eq` scale > 1 (427) — **BLOCKS reconstruction_theorem**
- `pairing_eq_of_small_scale_eq` scale ≤ 0 (430) — **BLOCKS reconstruction_theorem**
- `reconstruction_continuous_in_model` (796) — independent corollary
- `schauder_estimate` (818) — independent corollary

### BesovCharacterization.lean — 2 sorrys
- `zero_difference_at_all_scales` (167) — supports scale > 1 extension
- `scale_bounds_to_dyadic` (270) — supports scale > 1 extension

### Models/Canonical.lean — 15 sorrys
- `mollifiedNoiseCanonical.noise_pairing` (178)
- `canonical_model.Pi.noise_Xi_pairing` (218)
- `canonical_model.Pi.kernel_convolution` (228)
- `canonical_model.Pi.wick_product` (232)
- `canonical_model.Pi.noise_bound` (263)
- `canonical_model.Pi.kernel_bound` (286)
- `canonical_model.Pi.wick_bound` (289)
- `renormalized_canonical_model.analytical_bound` (336)
- `renormalized_canonical_model.consistency` (337)
- `renormalized_model_converges` (350)
- `limit_independent_of_mollification` (366)
- (+ 4 more in structure fields)

None of these block `reconstruction_theorem` (which assumes an abstract AdmissibleModel).

### Models/Admissible.lean — 0 sorrys ✓

### Trees/Basic.lean — 0 sorrys ✓
### Trees/Operations.lean — 0 sorrys ✓
### Trees/Homogeneity.lean — 0 sorrys ✓

### FixedPoint.lean — 10 sorrys
- `heatKernel.kernel_dyadic` (64)
- `heatKernel.support_bound` (70)
- `heatKernel.pointwise_bound` (74)
- `fixedPointMap.holder_regularity_noise` (202)
- `fixedPointMap.holder_regularity_integrated` (224)
- `fixedPointMap.holder_regularity` (233)
- `abstract_fixed_point` (261)
- `local_existence_uniqueness` (273)
- `solution_continuous` (295)
- `actual_solution_exists` (319)

None block `reconstruction_theorem` (FixedPoint imports Reconstruction, not vice versa).

### BPHZ.lean — 11 sorrys
- `inv.triangular` (285)
- `inv.off_diagonal` (293)
- `renormAction.mul_inv_self` (454)
- `renormAction.cocycle` (459)
- `renormAction.analytical_bound` (464)
- `renormAction.consistency` (465)
- `toGroupElement_inv_formula.lower_order_power_inv` (649)
- `toGroupElement_mul_inv_eq_id_coeff.case_eq_τ` (671)
- `toGroupElement_mul_inv_eq_id_coeff.case_ne_τ` (677)
- `bphz_renormalization` (717)
- Explicit bound (749)

None block `reconstruction_theorem` (BPHZ is downstream of Reconstruction).

### SmoothCutoff.lean — 1 sorry
- `on.annular_cutoff_radial_decreasing` (180) — utility, does not block reconstruction

---

## Total: 44 sorrys in RegularityStructures/

| Category | Count | Blocks reconstruction? |
|----------|-------|----------------------|
| Reconstruction uniqueness | 3 | **YES** |
| Reconstruction corollaries | 2 | No |
| Besov characterization | 2 | Indirectly (supports scale extension) |
| Canonical model | 15 | No |
| Fixed point solver | 10 | No |
| BPHZ renormalization | 11 | No |
| Smooth cutoff | 1 | No |

## Priority for Proving reconstruction_theorem

1. **Prove `pairing_eq_of_small_scale_bound`** (Prop 3.19) — requires Littlewood-Paley theory
2. **Prove scale > 1 extension** — requires Besov infrastructure
3. **Resolve scale ≤ 0 case** — may be trivial by domain restriction
