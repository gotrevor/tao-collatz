# Node ledger — GENERATED, do not hand-edit 🤖

Produced by `tools/blueprint_audit.py` from `blueprint/src/content.tex` (the node
registry) + a live `#print axioms` run. **Proof status exists only via the kernel.**
A hand-maintained ledger launders a worker claim into a reviewer-facing fact; this
one cannot, because nothing in it is typed by hand.

Trust base = `[propext, Classical.choice, Quot.sound]`.

| node | status | declarations |
|---|---|---|
| `S1` | 📐 definitions | `PMF.dTV`, `PMF.expect`, `PMF.cexpect`, `PMF.iid` |
| `S2` | 📐 definitions | `geomHalf`, `geomQuarter`, `pascal`, `pascalNe3` |
| `S3` | 🟢 **proved, axiom-clean** | `Gweight`, `geomHalf_local_bound`, `geomQuarter_local_bound`, `pascal_local_bound`, `geomHalf_tail_bound`, `geomQuarter_tail_bound`, `pascal_tail_bound`, `hold_local_bound`, `hold_tail_bound` |
| `S4` | 📐 definitions | `eC`, `osc` |
| `C1` | 📐 definitions + lemma, axiom-clean | `col`, `colMin`, `oddPart`, `syr`, `syrMin`, `colMin_eq_syrMin_oddPart` |
| `C2` | 🟢 **proved, axiom-clean** | `valVec`, `fnat`, `syr_iterate_key`, `valVec_unique`, `syr_iterate_odd` |
| `C3` | 📐 definitions | `logProb`, `HasLogDensity`, `AlmostAllPos`, `AlmostAllOdd` |
| `C4` | 📐 definitions + lemma, axiom-clean | `syracZ`, `syracZ_map_cast` |
| `C5` | 🟢 **proved, axiom-clean** | `valuation_dist`, `valuation_tail`, `unifOddMod`, `valVec_pos` |
| `C6` | 🟢 **proved, axiom-clean** | `tao_collatz`, `tao_collatz_quantitative` |
| `C6a` | 🟢 **proved, axiom-clean** | `tao_syracuse_quantitative_sum`, `tao_syracuse_quantitative` |
| `C6b` | 🟢 **proved, axiom-clean** | `tao_syracuse` |
| `C6c` | 🟢 **proved, axiom-clean** | `logSum_oddPart_pullback`, `almostAllPos_oddPart_of_almostAllOdd` |
| `C6s` | 🟢 **proved, axiom-clean** | `tao_collatz_spine`, `tao_collatz_quantitative_spine` |
| `C7d` | 📐 definitions | `passes`, `passTime`, `passLoc`, `logWindow`, `logUnifOdd`, `alpha` |
| `C7` | 🟢 **proved, axiom-clean** | `first_passage_nonescape` |
| `C8` | 🟢 **proved, axiom-clean** | `first_passage_approx` |
| `C9` | 🟢 **proved, axiom-clean** | `stabilization` |
| `C9B1` | 🟢 **proved, axiom-clean** | `perNHarmonic_eq_harmZfine_approx` |
| `C9B2` | 🟢 **proved, axiom-clean** | `harmZfine_to_mainZ` |
| `C9A` | 🟢 **proved, axiom-clean** | `perNTerm_harmonic_approx` |
| `C10` | 🟢 **proved, axiom-clean** | `fine_scale_mixing` |
| `X1` | 📐 definitions + lemma, axiom-clean | `fCond`, `xArg`, `cexpect_pairing` |
| `X2` | 🟢 **proved, axiom-clean** | `sfrac`, `θq`, `θq_succ_j`, `θq_pred_l`, `black`, `fCond_three_norm`, `white_cos_bound` |
| `X3` | 🟢 **proved, axiom-clean** | `triangle`, `black_structure` |
| `X4` | 🟢 **proved, axiom-clean** | `hold`, `Q_rec`, `Q_boundary`, `renewal_white_encounters` |
| `X5` | 🟢 **proved, axiom-clean** | `hold_mean_fst`, `hold_mean_snd`, `hold_aperiodic` |
| `X6` | 🟢 **proved, axiom-clean** | `fpDist`, `fpDist_location_bound` |
| `X7` | 🟢 **proved, axiom-clean** | `Qm`, `prop_7_8`, `Q_white_case1`, `Q_black_edge`, `Q_polynomial_decay` |
| `X8` | 🟢 **proved, axiom-clean** | `TriangleFamily`, `Q_black_edge_case2`, `Q_fp_endpoint_le`, `fpDist_edgeWeight_le`, `fpDist_white_exit`, `budget_le_of_mem_triangle` |
| `X9` | 🟢 **proved, axiom-clean** | `many_triangles_white`, `EncState`, `encStep`, `encVal`, `encExpect`, `encChainX`, `encounter_vertex_bound`, `fpDist_white_exit_deep` |
| `X10` | 🟢 **proved, axiom-clean** | `triangle_encounter_le`, `fpDistPlus`, `bigTriangleSet`, `TriangleFamily.not_mem_two`, `fpDistPlus_height_tail`, `fpDistPlus_col_tail`, `encounter_apex_proximity`, `encounter_separated_sum` |
| `X11` | 🟢 **proved, axiom-clean** | `charFn_decay`, `key_fourier_decay`, `Q_black_edge_case3` |
