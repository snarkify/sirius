# Report on the Implementation of CycleFold & Protogalaxy

![sirius_cyclefold_diag](img/cyclefold.png "Cyclefold+Protogalaxy in Sirius")

This report describes **how** we implemented the integrated **CycleFold + Protogalaxy** protocol for PLONKish in practice, referencing the architecture shown in the diagram above. After discussing the design decisions and code structure, we highlight off‐circuit polynomial computations, on‐circuit verifications, and how we achieve data‐parallelism with **rayon** in Rust.

---

## 1. Motivation & Overview

- **Protogalaxy**: A multi‐folding scheme that handles multiple polynomial instances efficiently. It introduces off‐circuit computations of three univariate polynomials \(\mathbf{F}, \mathbf{G}, \mathbf{K}\) (see the **Off‐Circuit Computation** box in the diagram), then folds these into a single “accumulator” instance using **PLONKish**‐style constraints.

- **CycleFold**: A protocol that *delegates* certain elliptic‐curve operations to a *small circuit on a second curve*, avoiding expensive non‐native arithmetic in the main circuit. In the diagram, these delegated checks appear as **Delegation Markers** or “SPS verify” lines. The resulting constraints are folded back in the **CycleFold‐SupportCircuit**, labeled “Provisional Verifier” or “Preliminary Verifier” in the diagram.

By combining these two, we obtain a scalable Incrementally Verifiable Computation (IVC) system that addresses both *multi‐instance polynomial folding* (Protogalaxy) and *cross‐curve scalar multiplications* (CycleFold) with minimal overhead in the main circuit—**all within a PLONKish framework**.

---

## 2. Implementation Outline

### 2.1 Off‐Circuit Polynomial Computations (Protogalaxy)

1. **Data Structures**  
   - We introduced a **new module** (`src/polynomial/univariate.rs`) to store and manipulate univariate polynomials.
   - A small struct tracks \(\beta, \delta\) (and later \(\alpha, \gamma\)) plus polynomial commitments, letting the rest of the system verify them succinctly on‐circuit.

2. **Computing \(\mathbf{F}\)**  
   - Implemented in a function `compute_F`, which evaluates gate expressions for the witness and applies `pow_i(\beta + X·\delta)`.  
   - **Parallel “tree‐reduce” approach**:  
     - We use [**rayon**](https://docs.rs/rayon/latest/rayon/), a Rust library for data‐parallelism, to split polynomial evaluations into chunks. Each chunk is processed concurrently, then merged in a binary‐tree fashion.  
     - This approach achieves near‐linear or quasilinear complexity, as suggested by Protogalaxy’s paper.

3. **Computing \(\mathbf{G}\)**  
   - Implemented in `compute_G`, which merges multiple instances (the current accumulator plus new witnesses) using Lagrange polynomials \(\{L_0, L_1, \dots\}\) and a fresh \(\alpha\).  
   - Similar to `compute_F`, we apply **rayon** to parallelize partial sums, reducing large input sets efficiently.

4. **Computing \(\mathbf{K}\)**  
   - Implemented in `compute_K`, finalizing the relation \(\mathbf{G}(X) - \mathbf{F}(\alpha)\,L_0(X) = \mathbf{K}(X)\,Z(X)\).  
   - The on‐circuit logic (in the **SupportCircuit**) checks this final quotient polynomial quickly, thanks to a compact coefficient representation.

---

### 2.2 Cross‐Curve Delegation (CycleFold)

1. **Identifying Delegated Operations**  
   - Certain scalar multiplications—e.g., \(\mathbf{C}' = \mathbf{C}_1 + \rho \cdot \mathbf{C}_2\)—would be expensive in the “wrong field” on the main curve.  
   - We thus create a small **PLONKish** circuit on the *second* curve, where these multiplications become native.

2. **Small Circuit on Second Curve**  
   - The diagram’s **Delegated** or “SPS verify” blocks show how \(\rho, \mathbf{C}_1, \mathbf{C}_2\) are inputs, and \(\mathbf{C}'\) is the output.  
   - This circuit has a compact design, focusing solely on point addition and scalar multiplication, which is efficient in the second curve’s base field.

3. **CycleFold‐SupportCircuit** for Folding**  
   - The **SupportCircuit** merges the delegated constraints from the second curve into the main PLONKish flow.  
   - By incorporating a “Provisional Verifier” step (as shown in the diagram), we end up with a single updated accumulator each time, combining both the Protogalaxy polynomial checks and the delegated checks.

---

## 3. On‐Circuit Verification

### 3.1 The CycleFold‐SupportCircuit

- **Protogalaxy Sub‐Verifier**  
  - Checks the off‐circuit polynomials \(\mathbf{F}, \mathbf{G}, \mathbf{K}\) (partial evaluations, sum‐check, or direct univariate checks).  
  - Uses “Consistency Markers” (as shown in the diagram) to ensure the new folded instance matches the old accumulators plus new polynomials.

- **Delegation Markers**  
  - Confirms the correctness of \(\mathbf{C}' = \mathbf{C}_1 + \rho \cdot \mathbf{C}_2\) via the second curve’s minimal PLONKish circuit.  
  - The “Provisional Verifier” or “Preliminary Verifier” sections in the diagram reflect these delegated checks being merged into the final output.

### 3.2 Final Folded Instance

- Once the **SupportCircuit** verifies both Protogalaxy’s polynomial constraints and the delegated scalar multiplications, it outputs a *single new instance* (labeled \(\{C_1, C_2\}\) or similar in the diagram).  
- This updated instance is then used as the accumulator for the next incremental step, ensuring we can chain these verifications indefinitely in a PLONKish setting.

---

## 4. Practical Considerations

1. **Parallelization with Rayon**  
   - [Rayon](https://docs.rs/rayon/latest/rayon/) is a data‐parallelism library for Rust, allowing us to easily spawn parallel tasks over iterators or slices.  
   - By incorporating Rayon in `compute_F` and `compute_G`, we reduce overall runtime for large polynomial evaluations, merging partial results in a balanced tree.

2. **Code Layout**  
   - **`protogalaxy/`**: Contains `compute_F`, `compute_G`, `compute_K` plus polynomial data structures.  
   - **`cyclefold/`**: Defines the second‐curve “support circuit” and the on‐circuit logic for merging delegated checks into the main PLONKish IVC flow.  
   - **`ivc/`** (or `folding/`): Manages the step‐by‐step pipeline (off‐circuit polynomial computations + on‐circuit “Provisional Verifier” calls).

3. **Security & Soundness**  
   - Protogalaxy’s multi‐folding correctness is based on its formal proof.  
   - CycleFold’s delegation approach ensures the second‐curve operations are incorporated without breaking the main curve’s constraints.  
   - The combined design in the diagram merges both seamlessly, preserving succinctness and correctness at each incremental step.

---

## 5. Conclusion & Next Steps

The **CycleFold + Protogalaxy** implementation, as depicted in the diagram, integrates:

- **Multi‐folding** from Protogalaxy (off‐circuit \(\mathbf{F}, \mathbf{G}, \mathbf{K}\) polynomials).  
- **Cross‐curve delegation** from CycleFold (the “Delegated” circuit on a second curve, folded in the **SupportCircuit**).  

This yields an IVC protocol capable of handling both high‐degree or multi‐instance gates and “wrong‐field” scalar multiplications efficiently, all in a PLONKish proof system.

---

## 6. Benchmarks

*(We will provide detailed performance metrics, circuit sizes, and timing results in the following section.)*
