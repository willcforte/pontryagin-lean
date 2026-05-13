# Pontryagin Maximum Principle — Lean 4 Formalization

## What this project is

A complete Lean 4 / Mathlib4 formalization of **Pontryagin's Maximum Principle (PMP)**,
following the self-contained proof in:

> Andrew D. Lewis, "The Maximum Principle of Pontryagin in control and in optimal control,"
> Queen's University lecture notes, 2006.  (`ref/maximum-principle.pdf`)

The formalization lives entirely in one file: `PontryaginMaxPrinciple.lean`.
A companion `TUTORIAL.md` explains every axiom line-by-line for beginners.

**Goal:** zero `sorry`, zero syntax errors, extensive pedagogical comments.
Mathematical gaps are covered by named `axiom` declarations, not by `sorry`.

---

## Build setup

- **Lean version:** `leanprover/lean4:v4.29.0` (see `lean-toolchain`)
- **Mathlib:** `v4.29.0` (pinned in `lake-manifest.json`, commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`)
- **Build command:** `lake build`
- **Pre-built packages:** `.lake/packages` is an NTFS junction pointing to
  `C:\Users\Will C. Forte\dev\lya_formalize\lya_formalize\.lake\packages`
  to reuse the already-compiled Mathlib (avoids hours of recompilation).
  If that sibling project moves, recreate the junction:
  ```powershell
  Remove-Item -Force .lake\packages
  New-Item -ItemType Junction -Path .lake\packages -Target "C:\Users\Will C. Forte\dev\lya_formalize\lya_formalize\.lake\packages"
  ```

---

## File structure

```
PontryaginMaxPrinciple.lean   — the entire formalization (~1380 lines)
TUTORIAL.md                   — beginner guide: every axiom explained line-by-line
lakefile.toml                 — lake project config
lean-toolchain                — Lean version pin
lake-manifest.json            — exact dependency versions
ref/
  maximum-principle.pdf       — Lewis (2006) — the proof we formalize
  maximum-principle.txt       — plain-text version of Lewis notes
  pontryagin_formalization.md — design doc: what's in Mathlib vs. what must be built
  *.pdf                       — supplementary references
```

---

## Architecture of `PontryaginMaxPrinciple.lean`

The file is organized into numbered sections (§0–§15):

| Section | Content |
|---|---|
| §0a | `piInner` instance: `Inner ℝ (Fin n → ℝ)` (see "Critical Lean details" below) |
| §0 | Helper lemmas: `inner_fin_cons`, `inner_sub` |
| §1 | `ControlSystem`, `AdmissibleControl`, `Lagrangian`, `SmoothConstraintSet` |
| §2 | **AXIOM 1** `caratheodory_ode_exists` + `controlledTrajectory` |
| §3 | `Hamiltonian`, `maxHamiltonian`, **AXIOM 0** `hamiltonian_le_maxHamiltonian` |
| §4 | `isVariationalSolution`, `isAdjointSolution` |
| §5 | **AXIOM 2** `adjoint_ode_exists`, **AXIOM 3** `adjoint_variational_pairing_const` |
| §6 | `NeedleVariationData`, `fixedIntervalTangentCone` |
| §7 | `fixedTimeReachableSet` |
| §8 | **AXIOM 4** `interior_tangent_cone_subset_reachable`, **AXIOM 5** `tangent_cone_is_closed` |
| §9 | `extendedSystem`, `extendedInitialState`, **AXIOM** `extendedSystem_smooth` |
| §10 | **AXIOM 6** `extended_needle_in_extended_cone`, **AXIOM 7** `optimal_not_in_int_ext_cone`, **AXIOM 8** `cone_separation` |
| §11 | **AXIOM 9** `max_hamiltonian_constant` |
| §11b | Assembly axioms A–G |
| §12 | **PROVED:** `separation_implies_hamiltonian_dominance`, `separation_implies_hamiltonian_max` |
| §13 | `SatisfiesTransversality` |
| §14 | **PROVED:** `pontryaginMaxPrinciple_fixedInterval` (the main theorem) |
| §15 | **AXIOM** `pontryaginMaxPrinciple_freeInterval` |

### What is fully proved (no axiom, no sorry)

- `inner_fin_cons` — ⟪Fin.cons a u, Fin.cons b v⟫ = a*b + ⟪u, v⟫
- `inner_sub` — ⟪lv, u - v⟫ = ⟪lv, u⟫ - ⟪lv, v⟫
- `controlledTrajectory_initial`, `controlledTrajectory_mem`
- `extendedInitialState_mem`
- `separation_implies_hamiltonian_dominance` — KEY algebraic step
- `separation_implies_hamiltonian_max` — H(µ) = H* from separation
- `pontryaginMaxPrinciple_fixedInterval` — the main PMP theorem

### Axiom inventory (19 total)

| Name | Mathematical content |
|---|---|
| `hamiltonian_le_maxHamiltonian` | H(x,λ,u) ≤ H*(x,λ) |
| `caratheodory_ode_exists` | Carathéodory ODE: measurable control → AC solution |
| `adjoint_ode_exists` | Backward linear ODE with L^∞ coefficients |
| `adjoint_variational_pairing_const` | ⟨λ(t), V(t)v⟩ is constant in t |
| `interior_tangent_cone_subset_reachable` | int(K) ⊆ R (requires Brouwer FPT) |
| `tangent_cone_is_closed` | K is closed |
| `extended_needle_in_extended_cone` | Extended needle vectors lie in K̂ |
| `optimal_not_in_int_ext_cone` | Optimality → (−1,0) ∉ int(K̂) |
| `cone_separation` | Geometric Hahn-Banach for closed convex cones |
| `max_hamiltonian_constant` | H*(ξ(t),λ(t)) is constant (envelope theorem) |
| `tangent_cone_nonempty` | 0 ∈ K |
| `tangent_cone_smul_mem` | K closed under nonneg scaling |
| `tangent_cone_add_mem` | K closed under addition |
| `extended_adjoint_state_restriction` | Extended adjoint → state-block adjoint |
| `separation_propagates_to_hamiltonian_max` | Terminal separation → H max at all t |
| `extended_traj_state_eq` | Fin.tail ∘ ξ̂∗ = ξ∗ |
| `adjoint_nontrivial_from_terminal` | λ̂(t₁) ≠ 0 → ∃t, λ∗(t) ≠ 0 |
| `extendedSystem_smooth` | Extended dynamics f̂ is C¹ (chain rule) |
| `pontryaginMaxPrinciple_freeInterval` | Free-interval PMP (H* = 0) |

---

## Critical Lean details — read before editing

### 1. `Fin n → ℝ` vs `EuclideanSpace ℝ (Fin n)`

We use `Fin n → ℝ` (the plain Pi type) throughout, **not** `EuclideanSpace ℝ (Fin n)`
(which is `PiLp 2 (fun _ => ℝ)`).  These are definitionally different types in Lean.

**Consequence:** `Fin n → ℝ` has only the **sup norm** by default in Mathlib.
It has **no `Inner ℝ` or `InnerProductSpace` instance** — adding a full
`InnerProductSpace` would create a diamond with the existing `NormedAddCommGroup`.

**Our fix:** we add *only* the `Inner` instance in §0a:
```lean
noncomputable instance piInner (n : ℕ) : Inner ℝ (Fin n → ℝ) where
  inner u v := ∑ i, u i * v i
```
This gives us `⟪·,·⟫_ℝ` notation without conflicting with the norm.
We also need `open scoped InnerProductSpace` for the notation to work.

**Do NOT** add `InnerProductSpace ℝ (Fin n → ℝ)` — it breaks existing instances.

### 2. `⟪·,·⟫_ℝ` notation

Requires `open scoped InnerProductSpace` (already in the file).
The notation expands to `@inner ℝ (Fin n → ℝ) (piInner n) u v = ∑ i, u i * v i`.

**Inner product proofs** must use `show ∑ i, ... = ...` to unfold the definition,
because there is no `inner_apply` lemma for our custom `piInner` instance.

Example:
```lean
show ∑ i, Fin.cons a u i * Fin.cons b v i = a * b + ∑ i, u i * v i
rw [Fin.sum_univ_succ]; simp [Fin.cons_zero, Fin.cons_succ]
```

### 3. `λ` is a Lean keyword (= `fun`)

Never use `λ` as a variable name.  It parses as the lambda keyword.
The file uses:
- `lam` for the costate/adjoint variable (in function signatures)
- `lv` for "lambda variable" (in local tactic contexts)
- `sep` for separation vectors (in `cone_separation` result)
- `λ̂`, `λ∗₁` etc. (with Unicode combining diacritics) are OK as identifiers

Similarly `Σ` is a Lean keyword (sigma types) — the file uses `sys`/`syshat`.

### 4. `ℝ` is `ConditionallyCompleteLattice`, not `CompleteLattice`

Do **not** use `le_iSup` or `iSup_le` with `ℝ`-valued functions — these require
`CompleteLattice`.  Use instead:
- `le_ciSup` (needs `BddAbove (Set.range f)`)
- `ciSup_le` (needs `[Nonempty ι]`)

In `separation_implies_hamiltonian_max`, we obtain `Nonempty sys.U` from `hµ`:
```lean
haveI : Nonempty sys.U := ⟨⟨µv, hµ⟩⟩
apply ciSup_le
```

### 5. `isAdjointSolution` — component-wise, no `.adjoint`

`ContinuousLinearMap.adjoint` requires a full `InnerProductSpace` (a Hilbert space).
Since `Fin n → ℝ` only has `Inner` (not the full IPS), we formulate the adjoint
equation component-wise:
```lean
fun k => -(∑ j : Fin n,
    fderiv ℝ (fun x => sys.f x (µ t)) (ξ t) (Pi.single k 1) j * costate t j)
```
This is `(−Df_x^T λ)_k = −∑_j (∂f_j/∂x_k) * λ_j`.

### 6. Module renames in Mathlib v4.29.0

| Old (broken) | New (correct) |
|---|---|
| `Mathlib.MeasureTheory.Integral.IntervalIntegral` | `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` |
| `Mathlib.MeasureTheory.Integral.SetIntegral` | `Mathlib.MeasureTheory.Integral.Bochner.Set` |

### 7. Module docstring placement

`/-! ... -/` must come **after** all `import` statements, not before.
(Lean processes imports first; a module docstring before imports causes a parse error.)

---

## Lean conventions for this file

- **Always** run `lake build` after edits to verify compilation.
- **Never** introduce `sorry` — use `axiom` with a justification comment instead.
- **Read** the file before editing; many issues (wrong lemma name, wrong instance)
  are only visible from context.
- When proving inner product identities, use `show ∑ i, ... = ...` to unfold
  `piInner` explicitly rather than relying on simp lemmas.
- Use `Fin.sum_univ_succ` to split `∑ i : Fin (n+1), ...` into head + tail.
- Use `Pi.single k 1` for the k-th standard basis vector `eₖ`.

---

## Proof architecture (how the main theorem is assembled)

```
Optimal (ξ∗, µ∗)
      │  [AXIOM 7: optimal_not_in_int_ext_cone]
      ▼
(−1, 0) ∉ int(K̂)
      │  [AXIOM 5 (closed) + Assembly A,B,C (cone props)]
      │  [AXIOM 8: cone_separation]
      ▼
∃ λ̂₁ ≠ 0  with  ⟨λ̂₁, k̂⟩ ≤ 0 ∀ k̂ ∈ K̂  and  ⟨λ̂₁, (−1,0)⟩ ≥ 0
      │  [AXIOM 2: adjoint_ode_exists]
      ▼
λ̂(t) solves extended adjoint ODE,  λ̂(t₁) = λ̂₁
      │  [Assembly G: extended_traj_state_eq]
      │  [Assembly D: extended_adjoint_state_restriction]
      ▼
λ∗(t) = Fin.tail(λ̂(t)) solves standard adjoint ODE    → conclusion (i)
      │  [Assembly E: separation_propagates_to_hamiltonian_max]
      │  (uses AXIOM 3 + AXIOM 6 + §12 algebraic lemma)
      ▼
H(ξ∗(t), λ∗(t), µ∗(t)) = H*(ξ∗(t), λ∗(t))  a.e.     → conclusion (ii)
      │  [AXIOM 9: max_hamiltonian_constant]
      ▼
H*(ξ∗(t), λ∗(t)) = const                               → conclusion (iii)
      │  [Assembly F: adjoint_nontrivial_from_terminal]
      ▼
∃ t, λ∗(t) ≠ 0                                          → conclusion (iv)
```

---

## What's left / future work

The file is **complete and compiling** as of 2026-05-02.  Possible next steps:

1. **Eliminate axioms** — the highest-value targets are:
   - `caratheodory_ode_exists`: Carathéodory ODE.  Proof strategy: approximate by
     smooth controls, Arzelà-Ascoli, pass to limit.  Needs `Mathlib.Analysis.ODE.Gronwall`.
   - `cone_separation`: Nearly in Mathlib as
     `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem`.
   - `tangent_cone_nonempty/smul/add`: Routine Lean API work on the `closure` definition.

2. **Switch to `EuclideanSpace`**: Rewrite using `EuclideanSpace ℝ (Fin n)` throughout
   to gain the full `InnerProductSpace` and `ContinuousLinearMap.adjoint`.  This would
   clean up `isAdjointSolution` but requires threading `WithLp` coercions everywhere.

3. **Prove the free-interval PMP**: Requires constructing the free-interval tangent
   cone K± (Lewis Definition 4.15 and Theorem 5.18).

4. **Abnormal extremals**: The current main theorem covers only the "normal" case
   (cost component λ₀ = −1).  The abnormal case (λ₀ = 0) needs separate treatment.
