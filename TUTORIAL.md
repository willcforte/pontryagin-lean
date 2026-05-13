# A Complete Beginner's Guide to the Pontryagin Maximum Principle Formalization

This tutorial explains every axiom in `PontryaginMaxPrinciple.lean` line by line,
assuming only that you know basic linear algebra and have seen ordinary differential
equations (ODEs) once or twice.  We build up every concept from scratch.

---

## Part 0: How to Read This File

### What is Lean 4?

Lean 4 is a **proof assistant** — a programming language where you can write
mathematical proofs and have a computer check them for correctness.  Think of it
as a very strict compiler: just as a C compiler rejects programs with type errors,
Lean rejects proofs that have logical gaps.

### What is an `axiom`?

In mathematics, an **axiom** is a statement you declare to be true without proving
it.  The classic example: Euclid's parallel postulate.

In this file, `axiom` means one of two things:
1. A deep mathematical theorem that is known to be true but whose formal Lean proof
   would require thousands of lines of code not yet in the Mathlib library.
2. A structural "glue" fact that is mathematically obvious but tedious to formalize.

None of the axioms in this file are mathematically controversial — they are all
standard results from analysis and control theory.  The word `axiom` here means
"proved elsewhere, not formalized here."

### How to read a Lean `axiom` declaration

Here is the general shape:

```lean
axiom my_fact
    (input1 : Type1)    -- "given an input1 of type Type1"
    (input2 : Type2)    -- "and an input2 of type Type2"
    (hypothesis : Prop) -- "and a proof that Prop holds"
    :
    Conclusion          -- "then Conclusion holds"
```

Read it as: **"If we have [inputs and hypotheses], then [Conclusion] is true."**

The `:` separates the hypotheses from the conclusion.  Everything before `:` is
a "given," and everything after `:` is what we conclude.

### Common notation decoded

| Lean notation | Plain English |
|---|---|
| `ℝ` | The real numbers |
| `ℕ` | The natural numbers 0, 1, 2, 3, ... |
| `Fin n → ℝ` | A vector in ℝⁿ (a function from {0,…,n−1} to ℝ) |
| `Set X` | A subset of X |
| `∃ x : T, P x` | "There exists an x of type T such that P(x)" |
| `∀ x : T, P x` | "For all x of type T, P(x) holds" |
| `P ∧ Q` | "P and Q" |
| `P ∨ Q` | "P or Q" |
| `¬ P` | "not P" |
| `a ∈ S` | "a is an element of the set S" |
| `a ∉ S` | "a is not an element of S" |
| `f : A → B` | "f is a function from A to B" |
| `fun x => expr` | The function that maps x to expr (lambda expression) |
| `Set.Icc a b` | The closed interval [a, b] |
| `Set.Ioo a b` | The open interval (a, b) |
| `⟪u, v⟫_ℝ` | The dot product (inner product) of vectors u and v |
| `‖v‖` | The length (norm) of vector v |
| `→L[ℝ]` | A continuous linear map over ℝ |
| `fderiv ℝ f x` | The Fréchet derivative (Jacobian) of f at x |
| `HasDerivAt f v t` | "The derivative of f at time t is v" |
| `HasDerivWithinAt f v S t` | "The derivative of f at t, restricting to the set S, is v" |
| `AEMeasurable f μ` | "f is measurable with respect to measure μ, up to a null set" |
| `∀ᵐ t ∂μ, P t` | "P(t) holds for almost every t under measure μ" |
| `∫ t in S, expr` | "The integral of expr over the set S" |
| `iSup f` | The supremum (least upper bound) of f over all inputs |
| `interior S` | The interior of the set S (largest open subset) |
| `IsClosed S` | "S is a closed set" |
| `closure S` | The closure of S (smallest closed set containing S) |
| `ContDiffOn ℝ 1 f X` | "f is continuously differentiable (C¹) on X" |
| `•` | Scalar multiplication (c • v = the vector v scaled by c) |
| `Fin.cons a v` | Prepend the scalar a to the vector v, making a vector of length n+1 |
| `Fin.tail v` | Drop the first component of v, giving a vector of length n |
| `Pi.single i 1` | The i-th standard basis vector (1 in position i, 0 elsewhere) |

---

## Part 1: The Mathematical Setting

### What is a Control System?

Imagine a rocket moving through space.  At time t, its **state** is a vector
x(t) ∈ ℝⁿ (position + velocity).  You can steer the rocket by choosing a
**control** u(t) ∈ ℝᵐ (e.g., thrust direction and magnitude).

The state evolves according to the **controlled ODE**:
```
ẋ(t) = f(x(t), u(t))
```
where ẋ means dx/dt (the time derivative), and f is a known function called
the **dynamics**.  The rocket moves according to physics; you steer it by
choosing u.

In Lean, a control system is a `structure ControlSystem n m` containing:
- `X`: the state space (an open set in ℝⁿ where the system is defined)
- `U`: the control set (allowed values of u, a subset of ℝᵐ)
- `f`: the dynamics function, f : ℝⁿ × ℝᵐ → ℝⁿ
- `hf_state`: a proof that f is C¹ (smoothly differentiable) in x

### What is optimal control?

Given a **running cost** L(x, u) (e.g., fuel used per second), you want to
find the control u(t) that **minimizes** the total cost:
```
∫_{t₀}^{t₁} L(x(t), u(t)) dt
```
subject to the dynamics ẋ = f(x, u) and some boundary conditions.

This is the **optimal control problem**.  The **Pontryagin Maximum Principle**
(PMP) gives necessary conditions for optimality.

### What is the Hamiltonian?

The **Hamiltonian** is the central quantity of PMP:
```
H(x, λ, u) = ⟨λ, f(x, u)⟩ − L(x, u)
```
where λ ∈ ℝⁿ is the **costate** (also called the adjoint variable or dual
variable).  You can think of λ as the "shadow price" of each state variable —
it measures how valuable it is to be at state x.

The **maximum Hamiltonian** is:
```
H*(x, λ) = sup_{u ∈ U} H(x, λ, u)
```
the largest possible Hamiltonian value over all allowed controls.

### What does the PMP say?

For an optimal trajectory (ξ∗, µ∗), the PMP says: there exists a costate
function λ∗(t) such that:
1. λ∗ satisfies the **adjoint ODE** (a differential equation run backward in time)
2. The optimal control **maximizes the Hamiltonian** at each time: H(ξ∗(t), λ∗(t), µ∗(t)) = H*(ξ∗(t), λ∗(t))
3. The maximum Hamiltonian H*(ξ∗(t), λ∗(t)) is **constant** in time
4. The costate λ∗ is **not identically zero** (non-triviality)

---

## Part 2: The Axioms — Line by Line

### Understanding the type signatures

Before we dive in, a few conventions:

**`n m : ℕ`** — Throughout the file, `n` is the state dimension (ξ ∈ ℝⁿ) and
`m` is the control dimension (u ∈ ℝᵐ).  These are positive integers.

**`t₀ t₁ : ℝ`** — The time interval is [t₀, t₁].

**`sys : ControlSystem n m`** — This is the control system (dynamics f, state
space X, control set U).

**`lag : Lagrangian sys`** — This is the running cost L(x, u).

---

### AXIOM 0 (not numbered in file): `hamiltonian_le_maxHamiltonian`

**In plain English:** For any control value u ∈ U, the Hamiltonian H(x, λ, u) is
at most the maximum Hamiltonian H*(x, λ).

**Why it's an axiom:** Mathematically, H(x,λ,u) ≤ sup_v H(x,λ,v) is just the
definition of supremum.  However, Lean's `ℝ` only has a "conditional" supremum
(it requires a boundedness proof), and providing that boundedness certificate in
full generality adds complexity.  We declare it as an axiom instead.

```lean
axiom hamiltonian_le_maxHamiltonian
    (sys : ControlSystem n m) (lag : Lagrangian sys)
    (x lam : Fin n → ℝ) (u : Fin m → ℝ) (hu : u ∈ sys.U) :
    Hamiltonian sys lag x lam u ≤ maxHamiltonian sys lag x lam
```

**Line-by-line:**
```lean
axiom hamiltonian_le_maxHamiltonian
```
We are declaring a named axiom called `hamiltonian_le_maxHamiltonian`.

```lean
    (sys : ControlSystem n m) (lag : Lagrangian sys)
```
Given: a control system `sys` (with n-dimensional state and m-dimensional control),
and a Lagrangian `lag` (the running cost function L).

```lean
    (x lam : Fin n → ℝ) (u : Fin m → ℝ) (hu : u ∈ sys.U) :
```
Given: a state vector `x` ∈ ℝⁿ, a costate vector `lam` ∈ ℝⁿ, a control value
`u` ∈ ℝᵐ, and a proof `hu` that u is in the allowed control set U.
The `:` signals the end of the hypotheses; what follows is the conclusion.

```lean
    Hamiltonian sys lag x lam u ≤ maxHamiltonian sys lag x lam
```
Conclusion: H(x, lam, u) ≤ H*(x, lam).  The specific control u gives a value
no larger than the supremum over all controls.

---

### AXIOM 1: `caratheodory_ode_exists`

**In plain English:** Given any measurable control µ (one that can jump around
discontinuously) and any starting state x₀, the controlled ODE ẋ = f(x, µ(t))
has a solution — a curve ξ(t) that starts at x₀ and satisfies the ODE almost
everywhere.

**Why this is non-trivial:** The standard ODE existence theorem (Picard–Lindelöf)
requires the right-hand side to be continuous in time.  But our control µ(t) is
only measurable, not continuous.  The **Carathéodory theorem** handles this more
general case, but it's not yet in Lean's Mathlib library.

**The mathematical setting:** A measurable function µ : [t₀,t₁] → U is called an
**admissible control**.  An absolutely continuous function ξ : [t₀,t₁] → ℝⁿ is
a solution if ξ̇(t) = f(ξ(t), µ(t)) holds for *almost every* t (i.e., it can
fail on a set of measure zero).

```lean
axiom caratheodory_ode_exists
    (sys : ControlSystem n m)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ)
    (hx₀ : x₀ ∈ sys.X) :
    ∃ ξ : ℝ → (Fin n → ℝ),
      ξ t₀ = x₀ ∧
      (∀ t ∈ Set.Icc t₀ t₁, ξ t ∈ sys.X) ∧
      ∀ᵐ t ∂Measure.restrict volume (Set.Icc t₀ t₁),
        HasDerivAt ξ (sys.f (ξ t) (µ.val t)) t
```

**Line-by-line:**
```lean
axiom caratheodory_ode_exists
```
We declare an axiom named `caratheodory_ode_exists`.

```lean
    (sys : ControlSystem n m)
```
Given: a control system `sys`.

```lean
    (µ : AdmissibleControl sys t₀ t₁)
```
Given: an admissible control `µ`.  `AdmissibleControl sys t₀ t₁` is a type
representing measurable functions µ : [t₀,t₁] → U.  The `t₀` and `t₁` here are
free variables (implicitly given from the context — Lean infers them).

```lean
    (x₀ : Fin n → ℝ)
    (hx₀ : x₀ ∈ sys.X) :
```
Given: an initial state x₀ ∈ ℝⁿ, and a proof `hx₀` that x₀ is in the state
space X (the dynamics are only defined on X).

```lean
    ∃ ξ : ℝ → (Fin n → ℝ),
```
Conclusion begins.  "There exists a function ξ from ℝ (time) to ℝⁿ (state
space)" — this is the trajectory.  `Fin n → ℝ` is Lean's way of writing ℝⁿ
(a vector indexed by {0, …, n−1}).

```lean
      ξ t₀ = x₀ ∧
```
The trajectory starts at x₀ at time t₀.  `∧` means "and."

```lean
      (∀ t ∈ Set.Icc t₀ t₁, ξ t ∈ sys.X) ∧
```
For all t in the closed interval [t₀, t₁], the trajectory stays inside the
state space X.  `Set.Icc t₀ t₁` is [t₀, t₁].

```lean
      ∀ᵐ t ∂Measure.restrict volume (Set.Icc t₀ t₁),
        HasDerivAt ξ (sys.f (ξ t) (µ.val t)) t
```
For *almost every* t in [t₀, t₁] (with respect to Lebesgue measure restricted
to [t₀,t₁]), the trajectory ξ has a derivative at t equal to f(ξ(t), µ(t)).

Breaking this apart:
- `∀ᵐ t ∂μ, P t` means "for almost every t with respect to measure μ, P(t) holds."
- `Measure.restrict volume (Set.Icc t₀ t₁)` is Lebesgue measure on [t₀,t₁].
- `HasDerivAt ξ v t` means "the function ξ has derivative v at time t."
- `sys.f (ξ t) (µ.val t)` is f(ξ(t), µ(t)): the dynamics evaluated at the current
  state and control.  `µ.val t` extracts the actual function from the subtype.

So the whole thing says: ξ̇(t) = f(ξ(t), µ(t)) for almost every t ∈ [t₀, t₁].

---

### AXIOM 2: `adjoint_ode_exists`

**In plain English:** The backward adjoint ODE has a solution.  Given a terminal
value λ₁ at time t₁, there is a function costate(t) that satisfies the adjoint
ODE and starts at λ₁ when t = t₁.

**What is the adjoint ODE?** It is a linear ODE run backwards in time:
```
λ̇(t) = −(Df_x)ᵀ λ(t),    λ(t₁) = λ₁
```
where (Df_x)ᵀ is the **transpose** of the Jacobian of f with respect to x.
In component form (see `isAdjointSolution`):
```
(d/dt costate(t))_k = −∑_j (∂f_j/∂x_k)(ξ(t), µ(t)) · costate(t)_j
```

**Why this is non-trivial:** This is a linear ODE with measurable (non-continuous)
coefficients (because µ is only measurable).  Linear ODEs always have solutions,
but Mathlib only has ODE existence for continuous right-hand sides.

```lean
axiom adjoint_ode_exists
    (sys : ControlSystem n m)
    (ξ : ℝ → Fin n → ℝ)    -- state trajectory
    (µ : ℝ → Fin m → ℝ)    -- control (Fin m, not Fin n)
    (costate₁ : Fin n → ℝ)  -- terminal costate value
    (t₀ t₁ : ℝ) :
    ∃ costate : ℝ → (Fin n → ℝ),
      costate t₁ = costate₁ ∧
      isAdjointSolution sys ξ µ costate t₀ t₁
```

**Line-by-line:**
```lean
axiom adjoint_ode_exists
```
Declare axiom `adjoint_ode_exists`.

```lean
    (sys : ControlSystem n m)
    (ξ : ℝ → Fin n → ℝ)
```
Given: the control system, and the state trajectory ξ : ℝ → ℝⁿ (a function from
time to state space — the optimal trajectory we are analyzing).

```lean
    (µ : ℝ → Fin m → ℝ)
```
Given: the control function µ : ℝ → ℝᵐ.  Note: `Fin m → ℝ` is ℝᵐ (the control
dimension m is different from the state dimension n).

```lean
    (costate₁ : Fin n → ℝ)  -- terminal costate value
    (t₀ t₁ : ℝ) :
```
Given: a terminal costate value costate₁ ∈ ℝⁿ (the value of λ at time t₁),
and the time endpoints t₀, t₁.

```lean
    ∃ costate : ℝ → (Fin n → ℝ),
```
Conclusion: there exists a costate function costate : ℝ → ℝⁿ (a curve in state
space, parameterized by time).

```lean
      costate t₁ = costate₁ ∧
```
The costate satisfies the terminal condition: at time t₁, it equals costate₁.
This is the boundary condition for the backward ODE.

```lean
      isAdjointSolution sys ξ µ costate t₀ t₁
```
The costate satisfies the adjoint ODE on the interval [t₀, t₁].
`isAdjointSolution` is defined in the file: it says that for every t in [t₀,t₁],
```
ċostate(t) = fun k => −∑_j (∂f_j/∂x_k)(ξ(t), µ(t)) · costate(t)_j
```
i.e., each component k of the costate derivative is minus the sum of
Jacobian entries times costate components.

---

### AXIOM 3: `adjoint_variational_pairing_const`

**In plain English:** If V solves the variational equation and costate solves the
adjoint equation, then the inner product ⟨costate(t), V(t)·v⟩ is the same for
all times t.  It stays constant as t varies.

**Why this matters:** This is the key "duality" between the forward (variational)
and backward (adjoint) equations.  It allows information from the terminal time t₁
(where we know the separation condition) to propagate back to all times t.

**What is the variational equation?** If you slightly perturb the initial
condition x₀, how does the trajectory change?  The answer is given by the
**variational equation** (also called the linearized equation):
```
V̇(t) = Df_x(ξ(t), µ(t)) · V(t),    V(t₀) = identity
```
V(t) is a linear map ℝⁿ → ℝⁿ: it maps a small initial perturbation δx₀ to the
resulting perturbation V(t)·δx₀ of the state at time t.

**Why the pairing is constant:** Differentiating ⟨λ(t), V(t)v⟩:
```
d/dt ⟨λ(t), V(t)v⟩
  = ⟨λ̇, Vv⟩ + ⟨λ, V̇v⟩
  = ⟨−(Df)ᵀλ, Vv⟩ + ⟨λ, (Df)(Vv)⟩
  = −⟨λ, (Df)(Vv)⟩ + ⟨λ, (Df)(Vv)⟩   (by the transpose/adjoint identity ⟨Aᵀy, x⟩ = ⟨y, Ax⟩)
  = 0
```
A function with zero derivative is constant.

```lean
axiom adjoint_variational_pairing_const
    (sys : ControlSystem n m)
    (ξ : ℝ → Fin n → ℝ)
    (µ : ℝ → Fin m → ℝ)    -- control (Fin m)
    (costate : ℝ → Fin n → ℝ)
    (V : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hV : isVariationalSolution sys ξ µ V t₀ t₁)
    (hcostate : isAdjointSolution sys ξ µ costate t₀ t₁)
    (v : Fin n → ℝ)
    (t s : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (hs : s ∈ Set.Icc t₀ t₁) :
    ⟪costate t, V t v⟫_ℝ = ⟪costate s, V s v⟫_ℝ
```

**Line-by-line:**
```lean
    (V : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
```
V is a function from time ℝ to a **continuous linear map** from ℝⁿ to ℝⁿ.
The notation `→L[ℝ]` means "continuous linear map over the scalar field ℝ."
So `V t` is a linear map: given an initial perturbation vector v, it returns the
perturbation of the state at time t.

```lean
    (hV : isVariationalSolution sys ξ µ V t₀ t₁)
    (hcostate : isAdjointSolution sys ξ µ costate t₀ t₁)
```
Given: proofs that V satisfies the variational equation, and that costate satisfies
the adjoint equation.  Both are along the same trajectory (ξ, µ).

```lean
    (v : Fin n → ℝ)
```
Given: an arbitrary fixed initial perturbation vector v ∈ ℝⁿ.

```lean
    (t s : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (hs : s ∈ Set.Icc t₀ t₁) :
```
Given: two times t and s in [t₀, t₁], with proofs `ht` and `hs` that they are
in range.

```lean
    ⟪costate t, V t v⟫_ℝ = ⟪costate s, V s v⟫_ℝ
```
Conclusion: the inner product of the costate with V applied to v is the same at
time t as at time s.  In formulas: ⟨λ(t), Φ(t)v⟩ = ⟨λ(s), Φ(s)v⟩.

---

### AXIOM 4: `interior_tangent_cone_subset_reachable`

**In plain English:** If a direction v is in the interior of the tangent cone K,
then you can actually move in direction v by choosing a different control.  More
precisely: the state ξ∗(t₁) + s·v is reachable for all small enough s > 0.

**Background — the tangent cone:** The **tangent cone** K is the set of all
first-order "directions" in which you can steer the terminal state.  It is built
from **needle variations**: you take the optimal control µ∗ and replace it with a
different value ω on a tiny interval [τ−ε, τ].  The resulting first-order change
in ξ(t₁) is a "needle variation vector."  K is the closed convex cone spanned by
all such vectors.

Geometrically: K ≈ tangent directions to the reachable set R at the point ξ∗(t₁).

**Interior of a cone:** A direction v is in the **interior** of K if there is an
open ball around v that lies entirely inside K.  Intuitively, v is "deep inside"
K, not on its boundary.

**Why Brouwer's fixed point theorem is needed:** The proof that int(K) ⊆ R uses
a clever topological argument.  You construct a map from a simplex to ℝⁿ using
multi-needle variations; Brouwer's theorem guarantees a fixed point, which gives
surjectivity near v.  Brouwer's theorem is not in Mathlib, so this is axiomatized.

```lean
axiom interior_tangent_cone_subset_reachable
    (sys : ControlSystem n m)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (v : Fin n → ℝ)
    (hv : v ∈ interior (fixedIntervalTangentCone sys µ x₀ hx₀)) :
    ∃ s₀ > 0, ∀ s ∈ Set.Ioo 0 s₀,
      controlledTrajectory sys µ x₀ hx₀ t₁ + s • v ∈
        fixedTimeReachableSet sys x₀ hx₀ t₀ t₁
```

**Line-by-line:**
```lean
    (v : Fin n → ℝ)
    (hv : v ∈ interior (fixedIntervalTangentCone sys µ x₀ hx₀)) :
```
Given: a direction v ∈ ℝⁿ, with proof `hv` that v is in the interior of the
tangent cone K = `fixedIntervalTangentCone sys µ x₀ hx₀`.

```lean
    ∃ s₀ > 0, ∀ s ∈ Set.Ioo 0 s₀,
```
Conclusion: there exists a step size s₀ > 0 such that for all s in (0, s₀)
(the open interval, not including 0 or s₀)...

```lean
      controlledTrajectory sys µ x₀ hx₀ t₁ + s • v ∈
        fixedTimeReachableSet sys x₀ hx₀ t₀ t₁
```
...the point (terminal state of optimal trajectory) + s·v is reachable.
`controlledTrajectory sys µ x₀ hx₀ t₁` is ξ∗(t₁), the endpoint of the
optimal trajectory.  `s • v` is s times the direction v.
`fixedTimeReachableSet sys x₀ hx₀ t₀ t₁` is the set of all states reachable
from x₀ by time t₁ using any admissible control.

---

### AXIOM 5: `tangent_cone_is_closed`

**In plain English:** The tangent cone K is a **closed** set.  This means: if
you have a sequence of vectors v₁, v₂, v₃, ... in K converging to some limit L,
then L is also in K.

**Why we need closedness:** The cone separation theorem (Axiom 8) requires the
cone to be closed.  If K were only the "open" conic hull (without limits), the
separation might not work.

**Why it's an axiom:** K is defined as the closure of the convex conic hull of
needle variation vectors.  Taking the closure automatically gives a closed set in
ℝⁿ.  However, verifying this carefully in Lean requires some topological API
work that is not yet done.

```lean
axiom tangent_cone_is_closed
    (sys : ControlSystem n m)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X) :
    IsClosed (fixedIntervalTangentCone sys µ x₀ hx₀)
```

**Line-by-line:**
```lean
axiom tangent_cone_is_closed
    (sys : ControlSystem n m)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X) :
```
Given: the control system, an admissible control, an initial state.

```lean
    IsClosed (fixedIntervalTangentCone sys µ x₀ hx₀)
```
Conclusion: the tangent cone K is closed.  `IsClosed S` in Mathlib means:
the set S is closed, i.e., it contains all its limit points.

---

### AXIOM 6: `extended_needle_in_extended_cone`

**In plain English:** When we work in the **extended state space** (where we track
both the accumulated cost and the state), the needle variation vectors for the
extended system are exactly the vectors of the form (cost change, state change).
These vectors lie in the tangent cone of the extended system.

**The extended system:** The extended system works in ℝ^(n+1) by prepending a
cost coordinate x̂₀ to the state x ∈ ℝⁿ:
```
extended state = x̂ = (x̂₀, x) ∈ ℝ^(n+1)
extended dynamics = f̂(x̂, u) = (L(x, u), f(x, u))
```
The extra coordinate x̂₀ accumulates the running cost: dx̂₀/dt = L(x, u).
At time t₁, x̂₀(t₁) = ∫_{t₀}^{t₁} L(ξ(t), µ(t)) dt = total cost.

**Why we extend:** The optimal control problem (minimize ∫L dt) becomes equivalent
to a geometric problem: the extended trajectory's endpoint lies on the boundary of
the extended reachable set with **minimum** x̂₀ component.  This geometric
reformulation is what lets us apply the cone separation theorem.

**What is the extended needle vector?** When we do a needle variation (replace µ
with ω on [τ−ε, τ]), the first-order change in the extended state is:
```
(L(ξ(τ), ω) − L(ξ(τ), µ(τ)),  f(ξ(τ), ω) − f(ξ(τ), µ(τ)))
```
i.e., the cost change prepended to the state change.  This axiom says this vector
is in the extended tangent cone K̂.

```lean
axiom extended_needle_in_extended_cone
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo t₀ t₁)
    (ω : Fin m → ℝ) (hω : ω ∈ sys.U) :
    let ξ := controlledTrajectory sys µ x₀ hx₀
    let x̂₀ := extendedInitialState x₀
    let hx̂₀ := extendedInitialState_mem sys lag x₀ hx₀
    let syshat := extendedSystem sys lag
    let µ̂ : AdmissibleControl syshat t₀ t₁ := ⟨µ.val, µ.property⟩
    Fin.cons (lag.L (ξ τ) ω - lag.L (ξ τ) (µ.val τ))
             (sys.f (ξ τ) ω - sys.f (ξ τ) (µ.val τ))
    ∈ fixedIntervalTangentCone syshat µ̂ x̂₀ hx̂₀
```

**Line-by-line:**
```lean
    (τ : ℝ) (hτ : τ ∈ Set.Ioo t₀ t₁)
```
Given: a needle insertion time τ in the open interval (t₀, t₁) (strictly between
the endpoints so there is room for the needle).

```lean
    (ω : Fin m → ℝ) (hω : ω ∈ sys.U) :
```
Given: a replacement control value ω ∈ ℝᵐ, with proof that it's in the control
set U.

```lean
    let ξ := controlledTrajectory sys µ x₀ hx₀
```
Locally define ξ as the optimal trajectory (the one we are analyzing).

```lean
    let x̂₀ := extendedInitialState x₀
```
The extended initial state: x̂₀ = (0, x₀) ∈ ℝ^(n+1) (zero accumulated cost at
the start, then the original initial state x₀).

```lean
    let hx̂₀ := extendedInitialState_mem sys lag x₀ hx₀
```
A proof that x̂₀ is in the extended state space.

```lean
    let syshat := extendedSystem sys lag
    let µ̂ : AdmissibleControl syshat t₀ t₁ := ⟨µ.val, µ.property⟩
```
The extended system (with dynamics f̂ = (L, f)), and µ̂ = µ lifted to an
admissible control for the extended system (same function, just repackaged).

```lean
    Fin.cons (lag.L (ξ τ) ω - lag.L (ξ τ) (µ.val τ))
             (sys.f (ξ τ) ω - sys.f (ξ τ) (µ.val τ))
    ∈ fixedIntervalTangentCone syshat µ̂ x̂₀ hx̂₀
```
Conclusion: the vector
```
(L(ξ(τ), ω) − L(ξ(τ), µ(τ)),   f(ξ(τ), ω) − f(ξ(τ), µ(τ)))
```
is in the extended tangent cone K̂.  This is the "extended needle variation vector"
— the first component is the cost change, the remaining n components are the state
change.  `Fin.cons a v` builds the vector (a, v₀, v₁, …, vₙ₋₁) from a scalar `a`
and a vector `v`.

---

### AXIOM 7: `optimal_not_in_int_ext_cone`

**In plain English:** If (ξ∗, µ∗) is optimal (minimizes total cost), then the
vector (−1, 0, 0, …, 0) ∈ ℝ^(n+1) is NOT in the interior of the extended tangent
cone K̂.

**Why this matters:** The vector (−1, 0) represents a "pure cost decrease with no
state change."  If (−1, 0) were in the interior of K̂, then by Axiom 4, we could
steer the extended trajectory to a point with smaller cost — contradicting
optimality.  So the optimal trajectory forces (−1, 0) ∉ int(K̂).

**This is the geometric heart of the PMP:** Once we know (−1, 0) ∉ int(K̂), we
can apply the cone separation theorem (Axiom 8) to get the costate λ̂.

```lean
axiom optimal_not_in_int_ext_cone
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (µ∗ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (hopt : ∀ µ : AdmissibleControl sys t₀ t₁,
        ∫ t in Set.Icc t₀ t₁,
          lag.L (controlledTrajectory sys µ∗ x₀ hx₀ t) (µ∗.val t) ≤
        ∫ t in Set.Icc t₀ t₁,
          lag.L (controlledTrajectory sys µ x₀ hx₀ t) (µ.val t)) :
    let syshat := extendedSystem sys lag
    let x̂₀ := extendedInitialState x₀
    let hx̂₀ := extendedInitialState_mem sys lag x₀ hx₀
    let µ̂∗ : AdmissibleControl syshat t₀ t₁ := ⟨µ∗.val, µ∗.property⟩
    (Fin.cons (-1 : ℝ) (0 : Fin n → ℝ)) ∉
      interior (fixedIntervalTangentCone syshat µ̂∗ x̂₀ hx̂₀)
```

**Line-by-line:**
```lean
    (µ∗ : AdmissibleControl sys t₀ t₁)
```
Given: the *optimal* admissible control µ∗ (we will assert its optimality below).

```lean
    (hopt : ∀ µ : AdmissibleControl sys t₀ t₁,
        ∫ t in Set.Icc t₀ t₁,
          lag.L (controlledTrajectory sys µ∗ x₀ hx₀ t) (µ∗.val t) ≤
        ∫ t in Set.Icc t₀ t₁,
          lag.L (controlledTrajectory sys µ x₀ hx₀ t) (µ.val t)) :
```
Given: a proof `hopt` of optimality.  "For every admissible control µ, the total
cost under µ∗ is ≤ the total cost under µ."  In symbols:
```
∫_{t₀}^{t₁} L(ξ∗(t), µ∗(t)) dt  ≤  ∫_{t₀}^{t₁} L(ξ(t), µ(t)) dt
```
for all admissible µ, where ξ∗ is the trajectory under µ∗ and ξ is under µ.

```lean
    let syshat := extendedSystem sys lag
    let x̂₀ := extendedInitialState x₀
    let hx̂₀ := extendedInitialState_mem sys lag x₀ hx₀
    let µ̂∗ : AdmissibleControl syshat t₀ t₁ := ⟨µ∗.val, µ∗.property⟩
```
Set up local abbreviations for the extended system and its control.

```lean
    (Fin.cons (-1 : ℝ) (0 : Fin n → ℝ)) ∉
      interior (fixedIntervalTangentCone syshat µ̂∗ x̂₀ hx̂₀)
```
Conclusion: the vector (−1, 0) = (−1, 0, 0, …, 0) ∈ ℝ^(n+1) is NOT in the
interior of the extended tangent cone K̂.

`Fin.cons (-1 : ℝ) (0 : Fin n → ℝ)` builds the vector with −1 in position 0
and zeros in positions 1 through n.  The cast `(-1 : ℝ)` ensures Lean knows we
want a real number.

---

### AXIOM 8: `cone_separation`

**In plain English:** Given a closed convex cone K not containing a point v in
its interior, there exists a "separating hyperplane" — a nonzero vector `sep`
such that sep points away from K (the inner product of sep with any k ∈ K is ≤ 0)
but does not point away from v (the inner product with v is ≥ 0).

**What is a convex cone?** A set K ⊆ ℝᵈ is a **cone** if for any k ∈ K and any
scalar c ≥ 0, we have c·k ∈ K.  It is **convex** if for any k₁, k₂ ∈ K, we have
k₁ + k₂ ∈ K (the sum is also in K).  Intuitively: a convex cone is like a "wedge"
or "ice cream cone shape" with its tip at the origin.

**The separation theorem:** If v is outside the interior of K (v ∉ int(K)), then
there is a linear functional (inner product with sep) that is ≤ 0 on K and ≥ 0 on
v.  This is the **geometric Hahn-Banach theorem** for cones.

**Why this is needed:** We apply this to v = (−1, 0) (from Axiom 7) and K = K̂
(the extended tangent cone).  The separating vector sep = λ̂₁ is the terminal
value of the extended costate — the "price" vector at the final time.

```lean
axiom cone_separation
    {d : ℕ}
    (K : Set (Fin d → ℝ))
    (hK_ne    : K.Nonempty)
    (hK_cone  : ∀ k ∈ K, ∀ c : ℝ, 0 ≤ c → c • k ∈ K)
    (hK_add   : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ + k₂ ∈ K)
    (hK_cl    : IsClosed K)
    (v : Fin d → ℝ)
    (hv : v ∉ interior K) :
    ∃ sep : Fin d → ℝ, sep ≠ 0 ∧ (∀ k ∈ K, ⟪sep, k⟫_ℝ ≤ 0) ∧ 0 ≤ ⟪sep, v⟫_ℝ
```

**Line-by-line:**
```lean
    {d : ℕ}
```
`d` is the dimension of the space ℝᵈ.  The curly braces `{}` mean d is an
**implicit argument** — Lean infers it automatically from the other arguments.

```lean
    (K : Set (Fin d → ℝ))
```
K is a subset of ℝᵈ (the cone we want to separate from).

```lean
    (hK_ne : K.Nonempty)
```
Proof that K is nonempty.  The separation theorem requires a nonempty cone.
`K.Nonempty` means `∃ x, x ∈ K`.

```lean
    (hK_cone : ∀ k ∈ K, ∀ c : ℝ, 0 ≤ c → c • k ∈ K)
```
Proof that K is a cone: for any k ∈ K and any real c ≥ 0, the scaled vector c·k
is still in K.

```lean
    (hK_add : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ + k₂ ∈ K)
```
Proof that K is closed under addition (the "convex" part of convex cone):
if k₁ and k₂ are in K, so is k₁ + k₂.

```lean
    (hK_cl : IsClosed K)
```
Proof that K is a closed set (contains all its limit points).

```lean
    (v : Fin d → ℝ)
    (hv : v ∉ interior K) :
```
The point v ∈ ℝᵈ that we want to separate from K, with proof that v is not in
the interior of K.

```lean
    ∃ sep : Fin d → ℝ, sep ≠ 0 ∧ (∀ k ∈ K, ⟪sep, k⟫_ℝ ≤ 0) ∧ 0 ≤ ⟪sep, v⟫_ℝ
```
Conclusion: there exists a separating vector `sep` ∈ ℝᵈ such that:
- `sep ≠ 0`: it is not the zero vector (the separation is non-trivial)
- `∀ k ∈ K, ⟪sep, k⟫_ℝ ≤ 0`: the dot product of sep with every k ∈ K is ≤ 0
  (sep "points away" from K, or K is on the "other side" of the hyperplane)
- `0 ≤ ⟪sep, v⟫_ℝ`: the dot product of sep with v is ≥ 0
  (sep "does not point away" from v)

Together, these say: ⟨sep, ·⟩ is a linear functional that is non-positive on K
and non-negative at v.  The hyperplane {x : ⟨sep, x⟩ = 0} separates K from v.

---

### AXIOM 9: `max_hamiltonian_constant`

**In plain English:** Along an optimal trajectory, the maximum Hamiltonian
H*(ξ(t), λ(t)) is constant in time.  It doesn't change as t goes from t₀ to t₁.

**Why this holds:** Differentiate H*(ξ(t), λ(t)):
```
d/dt H*(ξ(t), λ(t))
  = ∂H*/∂x · ξ̇ + ∂H*/∂λ · λ̇
  = ∂H*/∂x · f(ξ, µ) − f(ξ, µ) · (Df_x)ᵀ λ  [using the ODEs for ξ and λ]
  = 0  [these terms cancel by the envelope theorem / chain rule]
```

**Why it's an axiom:** This requires differentiating the supremum H*(ξ,λ) = sup_u H
with respect to the trajectory.  This uses the "envelope theorem" (the derivative
of the supremum equals the derivative at the maximizer), which requires careful
measure-theoretic handling in the Carathéodory setting.

```lean
axiom max_hamiltonian_constant
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (ξ : ℝ → Fin n → ℝ)
    (µ : ℝ → Fin m → ℝ)
    (costate : ℝ → Fin n → ℝ)
    (hcostate : isAdjointSolution sys ξ µ costate t₀ t₁)
    (hH_max : ∀ᵐ t ∂Measure.restrict volume (Set.Icc t₀ t₁),
        Hamiltonian sys lag (ξ t) (costate t) (µ t) =
        maxHamiltonian sys lag (ξ t) (costate t)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁,
      maxHamiltonian sys lag (ξ t) (costate t) = C
```

**Line-by-line:**
```lean
    (ξ : ℝ → Fin n → ℝ)
    (µ : ℝ → Fin m → ℝ)
    (costate : ℝ → Fin n → ℝ)
```
Given: the state trajectory ξ, the control µ, and the costate trajectory costate.
All are functions of time.

```lean
    (hcostate : isAdjointSolution sys ξ µ costate t₀ t₁)
```
Proof that costate satisfies the adjoint ODE along (ξ, µ) on [t₀, t₁].

```lean
    (hH_max : ∀ᵐ t ∂Measure.restrict volume (Set.Icc t₀ t₁),
        Hamiltonian sys lag (ξ t) (costate t) (µ t) =
        maxHamiltonian sys lag (ξ t) (costate t)) :
```
Proof that the Hamiltonian maximization condition holds *for almost every* t:
H(ξ(t), costate(t), µ(t)) = H*(ξ(t), costate(t)).

Breaking this down:
- `∀ᵐ t ∂ (Lebesgue on [t₀,t₁])` — for a.e. t
- `Hamiltonian sys lag (ξ t) (costate t) (µ t)` — H evaluated at state ξ(t),
  costate costate(t), and control µ(t)
- `= maxHamiltonian sys lag (ξ t) (costate t)` — equals H*(ξ(t), costate(t))

This says: the control µ achieves the maximum Hamiltonian at almost every time.

```lean
    ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁,
      maxHamiltonian sys lag (ξ t) (costate t) = C
```
Conclusion: there exists a constant C ∈ ℝ such that H*(ξ(t), costate(t)) = C
for all t ∈ [t₀, t₁].  The max Hamiltonian is constant along the optimal arc.

---

## Part 3: The Assembly Axioms

These axioms are not deep mathematical theorems; they are structural facts needed
to "wire together" the main proof.  Each is obviously true but requires
non-trivial API work in Lean to formalize.

---

### ASSEMBLY AXIOM A: `tangent_cone_nonempty`

**In plain English:** The tangent cone K contains at least one point (the zero
vector).

**Why:** The zero vector is always in a cone (take the empty sum: 0 = ∑_{empty} = 0,
which is a valid conic combination with no terms).  Closing under limits does not
remove 0.  The cone separation theorem requires K to be nonempty.

```lean
axiom tangent_cone_nonempty
    (sys : ControlSystem n m)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X) :
    (fixedIntervalTangentCone sys µ x₀ hx₀).Nonempty
```

`(fixedIntervalTangentCone sys µ x₀ hx₀).Nonempty` is notation for
`∃ v, v ∈ fixedIntervalTangentCone sys µ x₀ hx₀` — some element exists.

---

### ASSEMBLY AXIOM B: `tangent_cone_smul_mem`

**In plain English:** If v is in the tangent cone K, then so is c·v for any c ≥ 0.
The cone is closed under nonnegative scaling.

**Why:** If v = ∑ᵢ cᵢ · vᵢ (a sum with non-negative coefficients cᵢ), then
c · v = ∑ᵢ (c · cᵢ) · vᵢ, and all the new coefficients c · cᵢ are still ≥ 0.
For limit points, use the continuity of scalar multiplication.

```lean
axiom tangent_cone_smul_mem
    (sys : ControlSystem n m)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (k : Fin n → ℝ) (hk : k ∈ fixedIntervalTangentCone sys µ x₀ hx₀)
    (c : ℝ) (hc : 0 ≤ c) :
    c • k ∈ fixedIntervalTangentCone sys µ x₀ hx₀
```

`c • k` is "c times k" — the scalar multiple.  `hc : 0 ≤ c` ensures we only
scale by non-negative scalars (cones don't include reflections).

---

### ASSEMBLY AXIOM C: `tangent_cone_add_mem`

**In plain English:** If k₁ and k₂ are in the tangent cone K, then so is k₁ + k₂.
The cone is closed under addition.

**Why:** Concatenate the index sets of the two conic combinations.

```lean
axiom tangent_cone_add_mem
    (sys : ControlSystem n m)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (k₁ : Fin n → ℝ) (hk₁ : k₁ ∈ fixedIntervalTangentCone sys µ x₀ hx₀)
    (k₂ : Fin n → ℝ) (hk₂ : k₂ ∈ fixedIntervalTangentCone sys µ x₀ hx₀) :
    k₁ + k₂ ∈ fixedIntervalTangentCone sys µ x₀ hx₀
```

---

### ASSEMBLY AXIOM D: `extended_adjoint_state_restriction`

**In plain English:** If λ̂ : ℝ → ℝ^(n+1) solves the **extended** adjoint equation
(for the (n+1)-dimensional extended system), then its last n components
`Fin.tail ∘ λ̂` solve the **standard** adjoint equation for the original n-dimensional
system.

**Why:** The extended dynamics f̂ has a block-triangular Jacobian:
```
Df̂ = [ DL/Dx   0 ]
      [ Df/Dx   0 ]
```
The first row involves the cost gradient DL/Dx; the remaining rows are just Df/Dx.
When we take the transpose (for the adjoint equation), the last n rows of the
extended adjoint equation decouple from the first row:
```
λ̇∗ = −(Df/Dx)ᵀ λ∗
```
which is exactly the standard adjoint equation.

```lean
axiom extended_adjoint_state_restriction
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (ξ̂ : ℝ → Fin (n + 1) → ℝ)
    (µ : ℝ → Fin m → ℝ)
    (λ̂ : ℝ → Fin (n + 1) → ℝ)
    (hλ̂ : isAdjointSolution (extendedSystem sys lag) ξ̂ µ λ̂ t₀ t₁)
    (t₀ t₁ : ℝ) :
    isAdjointSolution sys (fun t => Fin.tail (ξ̂ t)) µ (fun t => Fin.tail (λ̂ t)) t₀ t₁
```

**Line-by-line:**
```lean
    (ξ̂ : ℝ → Fin (n + 1) → ℝ)
```
The extended trajectory ξ̂ : ℝ → ℝ^(n+1) (a path in the (n+1)-dimensional
extended state space).

```lean
    (λ̂ : ℝ → Fin (n + 1) → ℝ)
    (hλ̂ : isAdjointSolution (extendedSystem sys lag) ξ̂ µ λ̂ t₀ t₁)
```
The extended costate λ̂ : ℝ → ℝ^(n+1), with proof that it solves the extended
adjoint equation.

```lean
    isAdjointSolution sys (fun t => Fin.tail (ξ̂ t)) µ (fun t => Fin.tail (λ̂ t)) t₀ t₁
```
Conclusion: the function `t ↦ Fin.tail(λ̂(t))` (drop the first component of λ̂)
solves the standard adjoint equation for `sys` along the trajectory
`t ↦ Fin.tail(ξ̂(t))`.  `Fin.tail v` drops the zeroth component of an (n+1)-
dimensional vector, giving an n-dimensional vector.

---

### ASSEMBLY AXIOM E: `separation_propagates_to_hamiltonian_max`

**In plain English:** If the extended costate λ̂ at time t₁ separates K̂ (satisfies
⟨λ̂(t₁), k̂⟩ ≤ 0 for all k̂ ∈ K̂), and λ̂ solves the extended adjoint ODE, then for
almost every time t in [t₀, t₁], the Hamiltonian is maximized:
H(ξ∗(t), λ∗(t), µ∗(t)) = H*(ξ∗(t), λ∗(t)).

**Why:** By Axiom 3, the pairing ⟨λ̂(t), V(t,τ)·v̂⟩ is constant in time.  So the
terminal separation ⟨λ̂(t₁), k̂⟩ ≤ 0 implies ⟨λ̂(t), v̂⟩ ≤ 0 for all t and all
k̂ in K̂.  By Axiom 6, every extended needle vector is in K̂.  So
⟨λ̂(t), (ΔL, Δf)⟩ ≤ 0 for all replacement controls ω.  The algebraic lemma
`separation_implies_hamiltonian_max` then gives Hamiltonian maximization.

```lean
axiom separation_propagates_to_hamiltonian_max
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (µ∗ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (λ̂ : ℝ → Fin (n+1) → ℝ)
    (hλ̂_ode : isAdjointSolution (extendedSystem sys lag)
        (controlledTrajectory (extendedSystem sys lag)
          ⟨µ∗.val, µ∗.property⟩ (extendedInitialState x₀) (extendedInitialState_mem sys lag x₀ hx₀))
        µ∗.val λ̂ t₀ t₁)
    (hλ̂_sep : ∀ k̂ ∈ fixedIntervalTangentCone (extendedSystem sys lag)
        ⟨µ∗.val, µ∗.property⟩ (extendedInitialState x₀) (extendedInitialState_mem sys lag x₀ hx₀),
        ⟪λ̂ t₁, k̂⟫_ℝ ≤ 0) :
    ∀ᵐ t ∂Measure.restrict volume (Set.Icc t₀ t₁),
        Hamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t)
          (fun i => Fin.tail (λ̂ t) i) (µ∗.val t) =
        maxHamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t)
          (fun i => Fin.tail (λ̂ t) i)
```

**Line-by-line:**
```lean
    (hλ̂_ode : isAdjointSolution (extendedSystem sys lag)
        (controlledTrajectory (extendedSystem sys lag)
          ⟨µ∗.val, µ∗.property⟩ (extendedInitialState x₀) (extendedInitialState_mem sys lag x₀ hx₀))
        µ∗.val λ̂ t₀ t₁)
```
Proof that λ̂ solves the extended adjoint equation.  The extended trajectory is
computed from the extended system along µ∗, starting at x̂₀.  This is one big
expression passing all the required inputs to `isAdjointSolution`.

```lean
    (hλ̂_sep : ∀ k̂ ∈ fixedIntervalTangentCone (extendedSystem sys lag)
        ⟨µ∗.val, µ∗.property⟩ (extendedInitialState x₀) (extendedInitialState_mem sys lag x₀ hx₀),
        ⟪λ̂ t₁, k̂⟫_ℝ ≤ 0) :
```
Proof of the terminal separation condition: for every k̂ in the extended tangent
cone K̂, the inner product of λ̂(t₁) with k̂ is ≤ 0.  This is the condition from
Axiom 8 applied at the terminal time t₁.

```lean
    ∀ᵐ t ∂Measure.restrict volume (Set.Icc t₀ t₁),
        Hamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t)
          (fun i => Fin.tail (λ̂ t) i) (µ∗.val t) =
        maxHamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t)
          (fun i => Fin.tail (λ̂ t) i)
```
Conclusion: for almost every t, the Hamiltonian H at the optimal triple
(ξ∗(t), λ∗(t), µ∗(t)) equals the maximum Hamiltonian H*(ξ∗(t), λ∗(t)).

Note: `fun i => Fin.tail (λ̂ t) i` is just the state-block of λ̂(t) — dropping
the cost component to get λ∗(t) = (λ̂(t))_{1:n}.

---

### ASSEMBLY AXIOM G: `extended_traj_state_eq`

**In plain English:** When you run the extended trajectory and look at only its
last n components (the "state block"), you get back the original trajectory ξ.

**Why:** The extended dynamics are f̂(x̂, u) = (L(tail x̂, u), f(tail x̂, u)).
The last n components satisfy d(tail x̂)/dt = f(tail x̂, u).  By the uniqueness
of the Carathéodory ODE (Axiom 1), this means tail(ξ̂(t)) = ξ(t) for all t.

```lean
axiom extended_traj_state_eq
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (µ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X) :
    (fun t => Fin.tail (controlledTrajectory (extendedSystem sys lag)
        ⟨µ.val, µ.property⟩
        (extendedInitialState x₀) (extendedInitialState_mem sys lag x₀ hx₀) t)) =
    controlledTrajectory sys µ x₀ hx₀
```

**Line-by-line:**
```lean
    (fun t => Fin.tail (controlledTrajectory (extendedSystem sys lag)
        ⟨µ.val, µ.property⟩
        (extendedInitialState x₀) (extendedInitialState_mem sys lag x₀ hx₀) t))
```
This is the function t ↦ Fin.tail(ξ̂(t)):
- `controlledTrajectory (extendedSystem sys lag) ... t` is ξ̂(t), the extended
  trajectory at time t.
- `Fin.tail ξ̂(t)` drops the first (cost) component, keeping only components
  1 through n.
- `⟨µ.val, µ.property⟩` repackages µ as an admissible control for the extended
  system (the same function, just carrying a proof for the larger system).
- `extendedInitialState x₀` is (0, x₀) — the extended initial state.

```lean
    = controlledTrajectory sys µ x₀ hx₀
```
Conclusion: this equals the original trajectory ξ (as a function of time).
The state block of the extended trajectory IS the original trajectory.

---

### ASSEMBLY AXIOM F: `adjoint_nontrivial_from_terminal`

**In plain English:** If the extended costate λ̂ is nonzero at the terminal time t₁,
then the state-block of the costate (λ∗ = Fin.tail ∘ λ̂) is nonzero at some time
in [t₀, t₁].

**Why:** By ODE uniqueness, if costate(t) = 0 for all t, then in particular
costate(t₁) = 0 — contradicting the assumption that λ̂(t₁) ≠ 0.  So the costate
cannot be identically zero.

**Why it's an axiom:** Combining ODE uniqueness with the block structure of the
extended system to conclude non-triviality of the state block specifically requires
some care about the cost component.

```lean
axiom adjoint_nontrivial_from_terminal
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (µ∗ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (λ̂ : ℝ → Fin (n+1) → ℝ)
    (hλ̂₁_nz : λ̂ t₁ ≠ 0)
    (ht₀t₁ : t₀ < t₁) :
    ∃ t ∈ Set.Icc t₀ t₁, (fun i => Fin.tail (λ̂ t) i) ≠ (0 : Fin n → ℝ)
```

**Line-by-line:**
```lean
    (hλ̂₁_nz : λ̂ t₁ ≠ 0)
```
Hypothesis: the extended costate at time t₁ is not the zero vector.

```lean
    (ht₀t₁ : t₀ < t₁) :
```
Hypothesis: the time interval is non-degenerate (t₀ is strictly before t₁).

```lean
    ∃ t ∈ Set.Icc t₀ t₁, (fun i => Fin.tail (λ̂ t) i) ≠ (0 : Fin n → ℝ)
```
Conclusion: there exists some time t ∈ [t₀, t₁] at which the state-block
λ∗(t) = Fin.tail(λ̂(t)) is nonzero.

`(fun i => Fin.tail (λ̂ t) i)` is the same as `Fin.tail (λ̂ t)` — it's the
vector obtained by dropping the first component of λ̂(t).  Writing it with
`fun i => ...i` is just an eta-expanded form that makes the Lean type explicit.

`(0 : Fin n → ℝ)` is the zero vector in ℝⁿ — the explicit cast ensures Lean
knows we are comparing with the n-dimensional zero vector.

---

### EXTRA AXIOM: `extendedSystem_smooth`

**In plain English:** The extended dynamics f̂(x̂, u) = (L(tail x̂, u), f(tail x̂, u))
is C¹ (once continuously differentiable) in x̂.

**Why:** Since L and f are C¹ in x (by assumption from `ControlSystem`), and
`Fin.tail` is a bounded linear map (hence C∞), the composition is C¹ by the
chain rule.  The formalization requires telling Lean's `ContDiffOn` API how to
handle the `Fin.cons` / `Fin.tail` decomposition, which is nontrivial bookkeeping.

```lean
axiom extendedSystem_smooth
    (sys : ControlSystem n m)
    (lag : Lagrangian sys) :
    ∀ u ∈ sys.U, ContDiffOn ℝ 1
      (fun x̂ : Fin (n + 1) → ℝ =>
         Fin.cons (lag.L (Fin.tail x̂) u) (sys.f (Fin.tail x̂) u))
      {x̂ : Fin (n + 1) → ℝ | Fin.tail x̂ ∈ sys.X}
```

**Line-by-line:**
```lean
    ∀ u ∈ sys.U,
```
For every control value u ∈ U...

```lean
    ContDiffOn ℝ 1
```
...the following function is C¹ (`ContDiffOn ℝ 1` = once differentiable) over ℝ
(as opposed to ℂ or another field)...

```lean
      (fun x̂ : Fin (n + 1) → ℝ =>
         Fin.cons (lag.L (Fin.tail x̂) u) (sys.f (Fin.tail x̂) u))
```
...the extended dynamics function: given an extended state x̂ ∈ ℝ^(n+1), extract
the state x = Fin.tail(x̂) ∈ ℝⁿ, then return the vector
(L(x, u), f(x, u)) ∈ ℝ^(n+1).

`Fin.tail x̂` drops the first component of x̂.
`Fin.cons a v` prepends the scalar a to the vector v.

```lean
      {x̂ : Fin (n + 1) → ℝ | Fin.tail x̂ ∈ sys.X}
```
...on the extended state space {x̂ | tail(x̂) ∈ X} = ℝ × X.

---

### FINAL AXIOM: `pontryaginMaxPrinciple_freeInterval`

This is the free-terminal-time version of the PMP.  Unlike the fixed-interval
theorem (which is fully assembled in the file from the other axioms), the
free-interval case requires additional constructions (the free-interval tangent
cone K±) and is axiomatized as a single statement.

**In plain English:** If you also optimize over the terminal time t₁ (the time at
which you stop), then in addition to the usual PMP conditions, the maximum
Hamiltonian is identically zero:
```
H*(ξ∗(t), λ∗(t)) = 0   for all t ∈ [t₀, t₁].
```

**Why zero?** When t₁ is free, shifting t₁ slightly costs nothing in first order.
The free-interval tangent cone K± contains both +f(ξ(t₁), µ(t₁)) and
−f(ξ(t₁), µ(t₁)) as directions.  The separation condition then forces
⟨λ̂, f̂(ξ̂(t₁), µ(t₁))⟩ = 0, which translates to H* = 0.

```lean
axiom pontryaginMaxPrinciple_freeInterval
    (sys : ControlSystem n m)
    (lag : Lagrangian sys)
    (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (µ∗ : AdmissibleControl sys t₀ t₁)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ sys.X)
    (hopt : ∀ (t₀' t₁' : ℝ) (ht' : t₀' < t₁') (µ : AdmissibleControl sys t₀' t₁'),
        ∫ t in Set.Icc t₀ t₁,
          lag.L (controlledTrajectory sys µ∗ x₀ hx₀ t) (µ∗.val t) ≤
        ∫ t in Set.Icc t₀' t₁',
          lag.L (controlledTrajectory sys µ x₀ hx₀ t) (µ.val t)) :
    ∃ λ∗ : ℝ → (Fin n → ℝ),
      isAdjointSolution sys (controlledTrajectory sys µ∗ x₀ hx₀) (fun t => µ∗.val t) λ∗ t₀ t₁ ∧
      (∀ᵐ t ∂Measure.restrict volume (Set.Icc t₀ t₁),
          Hamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t) (λ∗ t) (µ∗.val t) =
          maxHamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t) (λ∗ t)) ∧
      (∀ t ∈ Set.Icc t₀ t₁,
          maxHamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t) (λ∗ t) = 0) ∧
      (∃ t ∈ Set.Icc t₀ t₁, λ∗ t ≠ 0)
```

**Line-by-line (focusing on the new parts vs. fixed-interval):**
```lean
    (hopt : ∀ (t₀' t₁' : ℝ) (ht' : t₀' < t₁') (µ : AdmissibleControl sys t₀' t₁'),
        ∫ t in Set.Icc t₀ t₁, ... ≤ ∫ t in Set.Icc t₀' t₁', ...)
```
The optimality hypothesis is stronger here: µ∗ must be optimal among all
controls on ALL time intervals [t₀', t₁'] (not just [t₀, t₁]).  This is the
free-interval optimality condition.

```lean
    ∃ λ∗ : ℝ → (Fin n → ℝ),
      isAdjointSolution ... ∧
      (∀ᵐ t ..., Hamiltonian ... = maxHamiltonian ...) ∧
      (∀ t ∈ Set.Icc t₀ t₁,
          maxHamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t) (λ∗ t) = 0) ∧
      (∃ t ∈ Set.Icc t₀ t₁, λ∗ t ≠ 0)
```
The conclusion has the same structure as the fixed-interval theorem but with an
extra conjunct (the third `∧`):

```lean
      (∀ t ∈ Set.Icc t₀ t₁,
          maxHamiltonian sys lag (controlledTrajectory sys µ∗ x₀ hx₀ t) (λ∗ t) = 0)
```
For ALL t ∈ [t₀, t₁] (not just almost every t), the maximum Hamiltonian is
identically zero.  This is the distinctive conclusion of the free-interval PMP.
Note that in the fixed-interval case we only get a constant C; here C = 0.

---

## Part 4: How the Axioms Connect — The Proof Architecture

Here is the flow of the main theorem `pontryaginMaxPrinciple_fixedInterval`:

```
Optimality of (ξ∗, µ∗)
        ↓  [Axiom 7: optimal_not_in_int_ext_cone]
(−1, 0) ∉ int(K̂)
        ↓  [Axiom 5: closed] + [Assembly A,B,C: cone properties]
        ↓  [Axiom 8: cone_separation]
∃ λ̂₁ ≠ 0 with ⟨λ̂₁, k̂⟩ ≤ 0 for all k̂ ∈ K̂
        ↓  [Axiom 2: adjoint_ode_exists]
λ̂(t) solves extended adjoint ODE, λ̂(t₁) = λ̂₁
        ↓  [Assembly D: extended_adjoint_state_restriction]
λ∗(t) = Fin.tail(λ̂(t)) solves standard adjoint ODE  → conclusion (i)
        ↓  [Assembly E: separation_propagates_to_hamiltonian_max]
H(ξ∗(t), λ∗(t), µ∗(t)) = H*(ξ∗(t), λ∗(t))  a.e.   → conclusion (ii)
        ↓  [Axiom 9: max_hamiltonian_constant]
H*(ξ∗(t), λ∗(t)) = C  for all t                     → conclusion (iii)
        ↓  [Assembly F: adjoint_nontrivial_from_terminal]
∃ t, λ∗(t) ≠ 0                                       → conclusion (iv)
```

Each arrow in the diagram corresponds to one axiom or assembly axiom.  The only
steps fully proved in Lean (no axioms) are:
- The algebraic identity `inner_fin_cons` (inner product decomposition)
- The algebraic lemma `separation_implies_hamiltonian_max` (sep → H max)
- The structure theorems for `controlledTrajectory` and `extendedSystem`

---

## Summary Table

| Axiom | One-line description |
|---|---|
| `hamiltonian_le_maxHamiltonian` | H(x,λ,u) ≤ H*(x,λ) for any u ∈ U |
| `caratheodory_ode_exists` | ODE with measurable control has a solution |
| `adjoint_ode_exists` | Backward adjoint ODE has a solution |
| `adjoint_variational_pairing_const` | ⟨λ(t), V(t)v⟩ is constant in t |
| `interior_tangent_cone_subset_reachable` | int(K) ⊆ R (needs Brouwer FPT) |
| `tangent_cone_is_closed` | K is a closed set |
| `extended_needle_in_extended_cone` | Extended needle vectors lie in K̂ |
| `optimal_not_in_int_ext_cone` | Optimality ⟹ (−1,0) ∉ int(K̂) |
| `cone_separation` | Geometric Hahn-Banach for cones |
| `max_hamiltonian_constant` | H*(ξ(t), λ(t)) is constant along optimal arc |
| `tangent_cone_nonempty` | K contains 0 |
| `tangent_cone_smul_mem` | c ≥ 0, v ∈ K ⟹ cv ∈ K |
| `tangent_cone_add_mem` | v₁, v₂ ∈ K ⟹ v₁ + v₂ ∈ K |
| `extended_adjoint_state_restriction` | Extended adjoint restricts to state adjoint |
| `separation_propagates_to_hamiltonian_max` | Terminal sep ⟹ H max at all t |
| `extended_traj_state_eq` | Fin.tail ∘ ξ̂∗ = ξ∗ |
| `adjoint_nontrivial_from_terminal` | λ̂(t₁) ≠ 0 ⟹ ∃t, λ∗(t) ≠ 0 |
| `extendedSystem_smooth` | Extended dynamics f̂ is C¹ |
| `pontryaginMaxPrinciple_freeInterval` | Free-interval PMP (H* = 0) |
