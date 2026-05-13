# Formalizing Pontryagin's Maximum Principle in Lean 4 / Mathlib

## Overview of the Proof Architecture

The proof in Lewis's notes decomposes into six major layers, each building on the last. Below I map each layer to what exists in Mathlib (reusable), what exists partially (adaptable), and what must be built from scratch.

---

## 1. Foundational Infrastructure

### What Mathlib Already Has

**ODE existence and uniqueness (Picard–Lindelöf / Gronwall):**
- `Mathlib.Analysis.ODE.PicardLindelof` — `IsPicardLindelof` structure, local existence theorem `exists_forall_hasDerivAt_Ioo_eq_of_contDiff`
- `Mathlib.Analysis.ODE.Gronwall` — `ODE_solution_unique`, Gronwall's inequality for uniqueness
- These cover Lewis's Appendix A (ODE existence with Lipschitz conditions). However, Lewis uses *measurable* time-dependent controls (Carathéodory solutions), which are strictly more general than what Mathlib's Picard–Lindelöf provides (continuous time-dependence). **You will need to extend this.**

**Measure theory and integration:**
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — Lebesgue measure on ℝ
- `Mathlib.MeasureTheory.Integral.Bochner.Basic` — Bochner integral for Banach-valued functions
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` — interval integrals, FTC
- `Mathlib.MeasureTheory.Function.AEMeasurable` — a.e. measurability
- `Mathlib.MeasureTheory.Function.LpSpace` — L^p spaces (you need L^∞ for bounded controls)
- `Mathlib.MeasureTheory.Integral.Lebesgue.Basic` — Lebesgue integral properties
- These cover Lewis's Appendix A.1 (measure theory background).

**Absolutely continuous functions:**
- `Mathlib.MeasureTheory.Decomposition.RadonNikodym` — absolute continuity of measures
- `Mathlib.Order.Filter.Basic`, `Mathlib.Topology.ContinuousOn` — continuity notions
- Lewis's adjoint response λ is "locally absolutely continuous." Mathlib has absolute continuity of *measures* but the notion of an absolutely continuous *function* ℝ → ℝⁿ (in the real-analysis sense) is not directly bundled. **You will need to define this.**

**Linear algebra and inner products:**
- `Mathlib.Analysis.InnerProductSpace.Basic` — standard inner product ⟨·,·⟩ on ℝⁿ
- `Mathlib.Analysis.NormedSpace.Basic` — normed vector spaces
- `Mathlib.LinearAlgebra.Matrix.Exponential` — matrix exponential (for linear systems, Ch. 8)
- `Mathlib.Analysis.NormedSpace.OperatorNorm` — operator norms ‖·‖ on L(ℝᵐ; ℝⁿ)

**Differentiation:**
- `Mathlib.Analysis.Calculus.FDeriv.Basic` — Fréchet derivative (Lewis's Dφ(x))
- `Mathlib.Analysis.Calculus.ContDiff.Basic` — C^r smoothness
- `Mathlib.Analysis.Calculus.MeanValue` — mean value theorem
- `Mathlib.Analysis.Calculus.ParametricIntegral` — differentiation under integral sign

### What You Must Build

**Carathéodory ODE solutions:** Lewis requires solutions to ξ̇(t) = f(ξ(t), μ(t)) where μ is merely *measurable* (Definition 1.4). The trajectory ξ is absolutely continuous and satisfies the ODE a.e. Mathlib's Picard–Lindelöf assumes continuous time-dependence. You need:

```lean
/-- A Carathéodory solution to an ODE with measurable time-dependent RHS -/
structure CaratheodorySolution (f : ℝ → E → E) (I : Set ℝ) (ξ : ℝ → E) : Prop where
  abs_cont : AbsolutelyContinuous ξ I  -- needs AC function def
  ae_deriv : ∀ᵐ t ∂(volume.restrict I), HasDerivAt ξ (f t (ξ t)) t
```

**Absolutely continuous functions (real-analysis sense):**

```lean
/-- A function f : ℝ → E is absolutely continuous on [a,b] -/
def AbsolutelyContinuous (f : ℝ → E) (I : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (intervals : List (ℝ × ℝ)),
    Pairwise (fun p q => p.2 ≤ q.1) intervals →
    (∀ p ∈ intervals, p.1 ∈ I ∧ p.2 ∈ I) →
    (intervals.map (fun p => p.2 - p.1)).sum < δ →
    (intervals.map (fun p => ‖f p.2 - f p.1‖)).sum < ε
```

---

## 2. Control System Definitions (Lewis Ch. 1)

### Core Structures to Define

```lean
/-- A control system Σ = (X, f, U) (Definition 1.1) -/
structure ControlSystem (n m : ℕ) where
  X : Set (EuclideanSpace ℝ (Fin n))  -- open subset
  X_open : IsOpen X
  U : Set (EuclideanSpace ℝ (Fin m))
  f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)
  f_cont : Continuous (fun p : _ × _ => f p.1 p.2)  -- on X × cl(U)
  f_C1_in_x : ∀ u ∈ closure U, ContDiff ℝ 1 (fun x => f x u)

/-- Admissible control (Definition 1.4) -/
structure AdmissibleControl (Σ : ControlSystem n m) (I : Set ℝ) where
  μ : ℝ → EuclideanSpace ℝ (Fin m)
  measurable : Measurable μ
  range_in_U : ∀ t ∈ I, μ t ∈ Σ.U
  locally_integrable : ∀ x ∈ Σ.X,
    MeasureTheory.LocallyIntegrable (fun t => Σ.f x (μ t)) volume

/-- Controlled trajectory (Definition 1.4) -/
structure ControlledTrajectory (Σ : ControlSystem n m) (I : Set ℝ) extends
    AdmissibleControl Σ I where
  ξ : ℝ → EuclideanSpace ℝ (Fin n)
  traj_in_X : ∀ t ∈ I, ξ t ∈ Σ.X
  satisfies_ODE : CaratheodorySolution (fun t x => Σ.f x (toAdmissibleControl.μ t)) I ξ

/-- Lagrangian (Definition 1.6) -/
structure Lagrangian (Σ : ControlSystem n m) where
  L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ
  L_cont : Continuous (fun p : _ × _ => L p.1 p.2)
  L_C1_in_x : ∀ u ∈ closure Σ.U, ContDiff ℝ 1 (fun x => L x u)

/-- Objective function (Definition 1.6) -/
noncomputable def objectiveFunction (Σ : ControlSystem n m) (L : Lagrangian Σ)
    (ct : ControlledTrajectory Σ (Set.Icc t₀ t₁)) : ℝ :=
  ∫ t in t₀..t₁, L.L (ct.ξ t) (ct.μ t)
```

**Mathlib reuse:** `EuclideanSpace`, `IsOpen`, `Continuous`, `ContDiff`, `Measurable`, `MeasureTheory.LocallyIntegrable`, interval integrals.

---

## 3. Hamiltonians and Adjoint Response (Lewis Ch. 3)

```lean
/-- Hamiltonian H_Σ(x, p, u) = ⟨p, f(x,u)⟩ (Definition 3.1) -/
noncomputable def hamiltonian (Σ : ControlSystem n m) (x p : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  inner p (Σ.f x u)

/-- Extended Hamiltonian H_{Σ,L}(x, p, u) = ⟨p, f(x,u)⟩ + L(x,u) (Definition 3.1) -/
noncomputable def extendedHamiltonian (Σ : ControlSystem n m) (L : Lagrangian Σ)
    (x p : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  inner p (Σ.f x u) + L.L x u

/-- Maximum Hamiltonian H_Σ^max(x, p) = sup_u H_Σ(x, p, u) (Definition 3.1) -/
noncomputable def maxHamiltonian (Σ : ControlSystem n m) (x p : Fin n → ℝ) : ℝ :=
  ⨆ u ∈ Σ.U, hamiltonian Σ x p u

/-- Adjoint response (Definition 3.2): λ satisfying Hamilton's equations -/
structure AdjointResponse (Σ : ControlSystem n m) (ct : ControlledTrajectory Σ I) where
  λ : ℝ → (Fin n → ℝ)
  abs_cont : AbsolutelyContinuous λ I
  hamilton_state : ∀ᵐ t ∂(volume.restrict I),
    HasDerivAt ct.ξ (fderiv ℝ (fun p => hamiltonian Σ (ct.ξ t) p (ct.μ t)) (λ t) 1) t
  hamilton_costate : ∀ᵐ t ∂(volume.restrict I),
    HasDerivAt λ (-(fderiv ℝ (fun x => hamiltonian Σ x (λ t) (ct.μ t)) (ct.ξ t) 1)) t
```

**Mathlib reuse:** `inner` from `InnerProductSpace`, `⨆` (iSup) from `Order.ConditionallyCompleteLattice`, `fderiv` from `Analysis.Calculus.FDeriv`, `HasDerivAt`.

---

## 4. Convex Geometry and Separation (Lewis Appendix B, Ch. 5)

### What Mathlib Already Has — Heavily Reusable

**Convex sets:**
- `Mathlib.Analysis.Convex.Basic` — `Convex`, `convex_Icc`, `convex_Ioo`, etc.
- `Mathlib.Analysis.Convex.Hull` — `convexHull`, properties of convex hull
- `Mathlib.Analysis.Convex.Combination` — convex combinations

**Convex cones:**
- `Mathlib.Geometry.Convex.Cone.Basic` — `ConvexCone` structure, `smul_mem`, `add_mem`
- `Mathlib.Analysis.Convex.Cone.InnerDual` — inner dual cone, `Set.innerDualCone`
- `Mathlib.Analysis.Convex.Cone.Proper` — `ProperCone` (nonempty + closed)

**Separation theorems (the critical ingredient for Ch. 5–6):**
- `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem` — **This is the key theorem.** For a nonempty closed convex cone K in a complete real inner product space, if b ∉ K, there exists y with ⟨x, y⟩ ≥ 0 for all x ∈ K and ⟨y, b⟩ < 0. This directly formalizes the geometric core of Lemma 6.3.
- `ProperCone.hyperplane_separation` — Farkas lemma (relative version)
- `Mathlib.Analysis.Convex.Cone.Extension` — Riesz extension theorem, Hahn–Banach

**Topology of convex sets:**
- `Mathlib.Topology.Algebra.Affine` — affine subspaces
- `Mathlib.Analysis.Convex.Topology` — `interior_convexHull_nonempty`, relative interior

### What You Must Build

**Simplex cones (Lewis §B.4):** Lewis defines r-simplex cones (coned convex hull of r linearly independent vectors). These are specialized subcones used to approximate the reachable set boundary.

**Tangent cones for the reachable set (Lewis §5.2–5.3):** The fixed-interval tangent cone K(μ, x₀, t₀, t) and free-interval tangent cone K±(μ, x₀, t₀, t) are entirely new constructions specific to control theory. They are defined as closures of coned convex hulls of needle variation directions.

---

## 5. Control Variations and Needle Variations (Lewis Ch. 4)

This is **entirely new material** with no Mathlib precedent. It is the most labor-intensive part.

### Key Definitions to Formalize

**Variational equation (Definition 4.1):** The linearization of the ODE along a trajectory:
```
V̇(t) = D₁f(ξ(t), μ(t)) · V(t)
```

**State transition matrix Φ(μ, x₀, t₀, τ, t):** The fundamental matrix solution of the variational equation (Proposition 4.3). This is the linear map taking tangent vectors at time τ to tangent vectors at time t along the reference trajectory.

**Adjoint equation (Definition 4.1):**
```
λ̇(t) = -D₁f(ξ(t), μ(t))ᵀ · λ(t)
```

**Key relationship (Proposition 4.7):** λ(t) = Φ(μ, x₀, t₀, τ, t)ᵀ · λ(τ). This is the transpose duality between variational and adjoint equations.

**Needle variations (Definition 4.8, Proposition 4.9):** Given Lebesgue point τ, replacing the control on [τ-sl, τ] with ω ∈ U produces a first-order trajectory perturbation:
```
vΘ(t) = Φ(μ, x₀, t₀, τ, t) · l · [f(ξ(τ), ω) - f(ξ(τ), μ(τ))]
```

**Multi-needle variations (§4.3):** Superposition of multiple needle variations at distinct Lebesgue times.

**Free interval variations (§4.4):** Adding a time-shift δτ · f(ξ(τ), μ(τ)) component.

### Mathlib Building Blocks

- `fderiv` for D₁f — partial Fréchet derivatives
- `ContinuousLinearMap` for the state transition matrix
- `MeasureTheory.Measure.Lebesgue.ae_eq_of_ae_eq` and Lebesgue density theorem for Lebesgue points
- `Mathlib.Analysis.Calculus.FDeriv.Comp` for chain rule in variational equation derivation

### What You Must Build

Everything in this section is new. The key constructions are:

1. **State transition matrix** as a `ContinuousLinearMap`-valued solution to a matrix ODE
2. **Needle variation lemma** (Proposition 4.9): the first-order expansion of trajectory under needle perturbation
3. **Multi-needle variation lemma** (Proposition 4.12): superposition
4. **Free interval variation lemma** (Corollary 4.17): adding time-shift terms

---

## 6. Reachable Set and Proof Assembly (Lewis Ch. 5–6)

### Reachable Set (§5.1)

```lean
/-- Reachable set at fixed time t from x₀ starting at t₀ -/
def reachableSetFixedTime (Σ : ControlSystem n m) (x₀ : Fin n → ℝ) (t₀ t : ℝ) :
    Set (Fin n → ℝ) :=
  { x | ∃ μ : AdmissibleControl Σ (Set.Icc t₀ t),
    ξ(μ, x₀, t₀, t) = x }  -- where ξ is the trajectory endpoint

/-- Reachable set (free time) -/
def reachableSet (Σ : ControlSystem n m) (x₀ : Fin n → ℝ) (t₀ : ℝ) :
    Set (Fin n → ℝ) :=
  ⋃ t > t₀, reachableSetFixedTime Σ x₀ t₀ t
```

### The Proof of the Maximum Principle (Ch. 6)

The proof has four steps:

**Step 1 — Extended system (Definition 6.1):** Augment the state with cost variable x⁰. The extended system Σ̂ has state (x⁰, x) ∈ ℝ × ℝⁿ and dynamics f̂((x⁰, x), u) = (L(x, u), f(x, u)).

**Step 2 — Boundary of extended reachable set (Lemma 6.2):** An optimal trajectory (ξ*, μ*) has its extended endpoint ξ̂*(t₁) on the *boundary* of the extended reachable set R̂(ξ̂*(t₀), t₀, t₁). The proof: if it were interior, we could decrease cost, contradicting optimality.

- **Mathlib needed:** `IsOpen`, `interior`, `frontier` from `Mathlib.Topology.Basic`.

**Step 3 — Adjoint response and Hamiltonian maximization (Lemma 6.3):** Since (−1, 0) ∉ int(K̂(μ*, x̂₀, t₀, t₁)) (the tangent cone of the extended system), the **hyperplane separation theorem** gives λ̂*(t₁) separating (−1, 0) from K̂. Then:
- λ₀* ≤ 0 (normalized to {0, −1})
- λ* is the adjoint response (by evolving λ̂*(t₁) backwards via adjoint equation)
- Hamiltonian maximization follows from Lemma 5.13

**This step uses `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem` directly.** This is the single most important Mathlib theorem for the entire formalization.

**Step 4 — Transversality conditions (§6.4):** Uses edged sets (Definition 6.5), tangent half-spaces (Definition 6.6), and Lemma C.3/C.4 (topological lemmata derived from Brouwer's fixed point theorem).

### Topology Appendix (Lewis Appendix C)

Lewis uses two topological results:

- **Hairy Ball Theorem** (Theorem C.1) — not in Mathlib
- **Brouwer Fixed Point Theorem** (Theorem C.2) — **not in Mathlib for general dimension**. Mathlib has the Banach fixed point theorem for contractions (`ContractingWith.exists_fixedPoint`) but not Brouwer's theorem for continuous maps on closed balls.
- **Lemma C.3 and C.4** — derived from Brouwer, used in §5.4 and §6.4

**You will need to either formalize Brouwer's theorem or find an alternative approach** (e.g., via degree theory or the Knaster–Kuratowski–Mazurkiewicz lemma). This is a significant standalone project. Some approaches:
- Formalize via Sperner's lemma (combinatorial)
- Use a smooth approximation argument reducing to Sard's theorem (Mathlib has `Mathlib.MeasureTheory.Measure.HaarLebesgue` for measure-zero but not Sard's theorem proper)

---

## Dependency Graph: Proof Steps and Mathlib Sources

```
Layer 0: FOUNDATIONS
├── Measure theory ← Mathlib.MeasureTheory.*  [DONE]
├── Lebesgue integral ← Mathlib.MeasureTheory.Integral.*  [DONE]
├── Normed spaces, inner products ← Mathlib.Analysis.*  [DONE]
├── Fréchet derivatives, C^r ← Mathlib.Analysis.Calculus.*  [DONE]
├── ODE existence (Picard–Lindelöf) ← Mathlib.Analysis.ODE.*  [DONE]
├── Absolutely continuous functions (real-analysis) ← [BUILD]
└── Carathéodory ODE solutions ← [BUILD, extends ODE.*]

Layer 1: CONTROL SYSTEM DEFINITIONS (Ch. 1)
├── ControlSystem, AdmissibleControl ← [BUILD, uses Layer 0]
├── ControlledTrajectory, ControlledArc ← [BUILD]
├── Lagrangian, ObjectiveFunction ← [BUILD]
└── Optimal control problems P(Σ,L,S₀,S₁) ← [BUILD]

Layer 2: CALCULUS OF VARIATIONS (Ch. 2) — optional for PMP
├── Euler–Lagrange equations ← [BUILD, motivational]
├── Weierstrass excess function ← [BUILD, motivational]
└── Hamiltonian formulation ← [BUILD, leads to Ch. 3]

Layer 3: HAMILTONIANS AND ADJOINT (Ch. 3)
├── Hamiltonian, extended Hamiltonian ← [BUILD, uses inner]
├── Maximum Hamiltonian ← [BUILD, uses ⨆ (iSup)]
├── Adjoint response ← [BUILD, uses Carathéodory ODE]
├── Smooth constraint sets ← [BUILD, uses fderiv surjectivity]
└── STATEMENT of Maximum Principle (Thms 3.4, 3.5) ← [BUILD]

Layer 4: CONTROL VARIATIONS (Ch. 4)
├── Variational equation ← [BUILD, linear ODE]
├── State transition matrix Φ ← [BUILD, matrix ODE]
├── Adjoint equation, duality with Φ ← [BUILD]
├── Needle variations ← [BUILD, core novelty]
├── Multi-needle variations ← [BUILD]
└── Free interval variations ← [BUILD]

Layer 5: CONVEX GEOMETRY (Appendix B + Ch. 5)
├── Convex sets ← Mathlib.Analysis.Convex.Basic  [DONE]
├── Convex cones ← Mathlib.Geometry.Convex.Cone.*  [DONE]
├── Separation theorems ← Mathlib.Analysis.Convex.Cone.InnerDual  [DONE]
├── Simplex cones ← [BUILD]
├── Fixed-interval tangent cone K ← [BUILD]
├── Free-interval tangent cone K± ← [BUILD]
├── Tangent cone approximates reachable set (Lemmas 5.10, 5.11) ← [BUILD]
├── Hamiltonian ↔ tangent cone (Lemma 5.13) ← [BUILD]
└── Boundary characterization (Thms 5.16, 5.18) ← [BUILD]

Layer 6: PROOF OF MAXIMUM PRINCIPLE (Ch. 6)
├── Extended system Σ̂ ← [BUILD]
├── Optimal ⟹ boundary of R̂ (Lemma 6.2) ← [BUILD, uses topology]
├── Separation ⟹ adjoint + Hamiltonian (Lemma 6.3) ← [BUILD, KEY]
│   └── uses ConvexCone.hyperplane_separation_*  [MATHLIB]
├── Constancy of max Hamiltonian (Cor 6.4) ← [BUILD]
├── Transversality (§6.4) ← [BUILD]
│   ├── Edged sets, tangent half-spaces ← [BUILD]
│   └── Brouwer fixed point theorem ← [BUILD or AXIOMATIZE]
└── PROOF COMPLETE ← combines Lemmas 6.2, 6.3, Cor 6.4, §6.4
```

---

## Complete Mathlib Module Reference

| Lewis Section | Mathlib 4 Module | What It Provides |
|---|---|---|
| §A.1 Measure theory | `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | Lebesgue measure |
| §A.1 Integration | `Mathlib.MeasureTheory.Integral.Bochner.Basic` | Bochner integral |
| §A.1 Integration | `Mathlib.MeasureTheory.Integral.IntervalIntegral` | ∫ t in a..b |
| §A.1 L^p spaces | `Mathlib.MeasureTheory.Function.LpSpace` | L^∞ for bounded controls |
| §A.2 ODE existence | `Mathlib.Analysis.ODE.PicardLindelof` | Picard–Lindelöf |
| §A.2 ODE uniqueness | `Mathlib.Analysis.ODE.Gronwall` | Gronwall inequality |
| Notation ⟨·,·⟩ | `Mathlib.Analysis.InnerProductSpace.Basic` | Inner product |
| Notation ‖·‖ | `Mathlib.Analysis.NormedSpace.Basic` | Norms |
| Notation Dφ | `Mathlib.Analysis.Calculus.FDeriv.Basic` | Fréchet derivative |
| Notation C^r | `Mathlib.Analysis.Calculus.ContDiff.Basic` | Smooth functions |
| §B.1–B.2 Convex sets | `Mathlib.Analysis.Convex.Basic` | Convexity |
| §B.2 Convex hull | `Mathlib.Analysis.Convex.Hull` | `convexHull` |
| §B.3 Convex cones | `Mathlib.Geometry.Convex.Cone.Basic` | `ConvexCone` |
| §B.5 Separation | `Mathlib.Analysis.Convex.Cone.InnerDual` | Hyperplane separation |
| §B.5 Separation | `Mathlib.Analysis.Convex.Cone.Proper` | Farkas lemma |
| §B.5 Hahn–Banach | `Mathlib.Analysis.Convex.Cone.Extension` | Extension theorem |
| §C.2 Fixed points | `Mathlib.Topology.MetricSpace.Contracting` | Banach fixed point only |
| Ch. 8 Matrix exp | `Mathlib.LinearAlgebra.Matrix.Exponential` | exp(At) |
| Topology basics | `Mathlib.Topology.Basic` | `interior`, `closure`, `frontier` |
| Submanifolds | `Mathlib.Analysis.Calculus.Implicit` | Implicit function theorem |

---

## Starter Lean 4 Code

Below is a skeleton that establishes the key definitions and states the Maximum Principle. Everything marked `sorry` is what you need to prove.

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Basic

open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable section

/-! # Control Systems -/

/-- A control system Σ = (X, f, U) (Lewis Definition 1.1) -/
structure ControlSystem (n m : ℕ) where
  /-- State space (open subset of ℝⁿ) -/
  X : Set (Fin n → ℝ)
  hX_open : IsOpen X
  /-- Control set U ⊂ ℝᵐ -/
  U : Set (Fin m → ℝ)
  /-- Dynamics f : X × cl(U) → ℝⁿ -/
  f : (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ)
  /-- f is continuous -/
  hf_cont : Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) => f p.1 p.2)
  /-- f is C¹ in x for each fixed u -/
  hf_C1 : ∀ u ∈ closure U, ContDiff ℝ 1 (f · u)

/-- A Lagrangian for a control system (Lewis Definition 1.6) -/
structure Lagrangian (Σ : ControlSystem n m) where
  L : (Fin n → ℝ) → (Fin m → ℝ) → ℝ
  hL_cont : Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) => L p.1 p.2)
  hL_C1 : ∀ u ∈ closure Σ.U, ContDiff ℝ 1 (L · u)

/-- Smooth constraint set S = Φ⁻¹(0) (Lewis Definition 3.3) -/
structure SmoothConstraintSet (n k : ℕ) where
  Φ : (Fin n → ℝ) → (Fin k → ℝ)
  hΦ_C1 : ContDiff ℝ 1 Φ
  hΦ_surj : ∀ x, Φ x = 0 → Function.Surjective (fderiv ℝ Φ x)
  carrier : Set (Fin n → ℝ) := Φ ⁻¹' {0}

/-! # Hamiltonians (Lewis Definition 3.1) -/

/-- The Hamiltonian H_Σ(x, p, u) = ⟨p, f(x,u)⟩ -/
def ControlSystem.hamiltonian (Σ : ControlSystem n m)
    (x : Fin n → ℝ) (p : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  ∑ i, p i * (Σ.f x u) i

/-- The extended Hamiltonian H_{Σ,L}(x, p, u) = ⟨p, f(x,u)⟩ + L(x,u) -/
def ControlSystem.extHamiltonian (Σ : ControlSystem n m) (L : Lagrangian Σ)
    (x : Fin n → ℝ) (p : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  Σ.hamiltonian x p u + L.L x u

/-- The maximum Hamiltonian H_Σ^max(x, p) = sup_{u ∈ U} H_Σ(x, p, u) -/
def ControlSystem.maxHamiltonian (Σ : ControlSystem n m)
    (x : Fin n → ℝ) (p : Fin n → ℝ) : ℝ :=
  sSup (Σ.hamiltonian x p '' Σ.U)

/-! # Statement of the Maximum Principle (Lewis Theorem 3.5) -/

/-- The Maximum Principle for fixed interval problems.
    If (ξ*, μ*) is optimal, then there exist λ₀* ∈ {0, -1} and an
    adjoint response λ* satisfying the stated conditions. -/
theorem maximum_principle_fixed_interval
    (Σ : ControlSystem n m)
    (L : Lagrangian Σ)
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (S₀ : SmoothConstraintSet n k₀)
    (S₁ : SmoothConstraintSet n k₁)
    -- Optimal trajectory
    (ξ_star : ℝ → Fin n → ℝ)
    (μ_star : ℝ → Fin m → ℝ)
    (hξ_traj : ∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)),
      HasDerivAt ξ_star (Σ.f (ξ_star t) (μ_star t)) t)
    (hμ_admissible : ∀ t ∈ Icc t₀ t₁, μ_star t ∈ Σ.U)
    (hξ_S₀ : ξ_star t₀ ∈ S₀.carrier)
    (hξ_S₁ : ξ_star t₁ ∈ S₁.carrier)
    -- Optimality
    (h_optimal : ∀ ξ μ,
      (∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)),
        HasDerivAt ξ (Σ.f (ξ t) (μ t)) t) →
      (∀ t ∈ Icc t₀ t₁, μ t ∈ Σ.U) →
      ξ t₀ ∈ S₀.carrier → ξ t₁ ∈ S₁.carrier →
      ∫ t in t₀..t₁, L.L (ξ_star t) (μ_star t) ≤
      ∫ t in t₀..t₁, L.L (ξ t) (μ t)) :
    -- CONCLUSION: existence of adjoint
    ∃ (λ₀_star : ℝ) (λ_star : ℝ → Fin n → ℝ),
      -- (i) λ₀* ∈ {0, -1} and nontriviality
      (λ₀_star = 0 ∨ λ₀_star = -1) ∧
      (λ₀_star = -1 ∨ λ_star t₀ ≠ 0) ∧
      -- (ii) λ* is adjoint response for (Σ, λ₀*L)
      (∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)),
        HasDerivAt λ_star
          (fun i => -∑ j, (fderiv ℝ (fun x => Σ.f x (μ_star t)) (ξ_star t) (Pi.single j 1)) i
            * λ_star t j
            - λ₀_star * (fderiv ℝ (fun x => L.L x (μ_star t)) (ξ_star t) (Pi.single i 1))) t) ∧
      -- (iii) Hamiltonian maximization
      (∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)),
        ∀ u ∈ Σ.U,
          Σ.extHamiltonian L (ξ_star t) (λ_star t) u ≤
          Σ.extHamiltonian L (ξ_star t) (λ_star t) (μ_star t)) ∧
      -- (v) Transversality
      (∀ v, fderiv ℝ S₀.Φ (ξ_star t₀) v = 0 →
        ∑ i, λ_star t₀ i * v i = 0) ∧
      (∀ v, fderiv ℝ S₁.Φ (ξ_star t₁) v = 0 →
        ∑ i, λ_star t₁ i * v i = 0) := by
  sorry -- The full proof requires Layers 4-6

end
```

---

## Recommended Development Order

1. **Absolutely continuous functions + Carathéodory ODE theory** (extends `Mathlib.Analysis.ODE.*`)
2. **Control system definitions** (structures above)
3. **Variational equation and state transition matrix** (linear ODE theory)
4. **Needle variations** (the creative core — no existing formalization anywhere)
5. **Tangent cones for reachable set** (uses convex cone machinery from Mathlib)
6. **Tangent cone approximates reachable set** (Lemma 5.10 — uses Brouwer)
7. **Hamiltonian–tangent cone connection** (Lemma 5.13 — uses separation theorem)
8. **Extended system + proof assembly** (Chapter 6)
9. **Transversality** (§6.4 — uses Brouwer-derived lemmata)

## Key Risks and Mitigations

| Risk | Mitigation |
|---|---|
| Brouwer FPT not in Mathlib | Axiomatize it as `axiom brouwer_fixed_point` and prove everything else; formalize Brouwer separately via Sperner's lemma |
| Carathéodory ODE not in Mathlib | Extend Picard–Lindelöf; the core estimate (Gronwall) is already there |
| Measurable selection issues | Lewis avoids this by working with explicit needle variation constructions |
| Absolutely continuous functions | Define as a structure wrapping the ε-δ condition; prove basic properties (FTC, chain rule) |

## External Repositories

- **[mathlib4](https://github.com/leanprover-community/mathlib4)** — primary dependency
- **[SciLean](https://github.com/lecopivo/SciLean)** — scientific computing in Lean 4; has some ODE/dynamical systems infrastructure but limited formal proofs
- **[LeanCopilot](https://github.com/lean-dojo/LeanCopilot)** — AI-assisted tactic search, useful for closing routine goals
- No existing Lean formalization of PMP exists in any repository as of the knowledge cutoff.
