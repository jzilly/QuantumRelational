import Lake
open Lake DSL

package QuantumRelational where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib QuantumRelational where
  srcDir := "."
  roots := #[
    `QuantumRelational.Axioms,
    `QuantumRelational.Basic,
    `QuantumRelational.ClassicalImports,
    `QuantumRelational.Parsimony,
    `QuantumRelational.SwapMatrix,
    `QuantumRelational.CyclicEigen,
    `QuantumRelational.Frobenius,
    `QuantumRelational.Fourier,
    `QuantumRelational.InnerProduct,
    `QuantumRelational.FubiniStudy,
    `QuantumRelational.MetricBridge,
    `QuantumRelational.BornRule,
    `QuantumRelational.BornRuleN2,
    `QuantumRelational.CapacityHalting,
    `QuantumRelational.Schrodinger,
    `QuantumRelational.Composite,
    `QuantumRelational.Scaling,
    `QuantumRelational.Main,
    `QuantumRelational.AxiomCheck,
    -- Paper 2: Spatial Structure (graph delta)
    `QuantumRelational.Paper2.Sparsity,
    `QuantumRelational.Paper2.CayleyGraph,
    `QuantumRelational.Paper2.IntegerDimension,
    `QuantumRelational.Paper2.EuclideanMetric,
    `QuantumRelational.Paper2.DimensionThree
  ]
