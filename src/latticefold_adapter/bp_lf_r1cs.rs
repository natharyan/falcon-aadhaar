//! Extract matrices A,B,C and vector z from Bellpepper circuit; Convert Bellpepper LinearCombination over StarkFq (derives ff:Primefield) to Latticefold R1CS over StarkRingNTT

use bellpepper_core::{
    Comparable,
    Constraint,
    ConstraintSystem,
    Index,
    // LinearCombination aliased as BpLC to avoid shadowing LinearCombination from latticefold
    LinearCombination as BpLC,
    SynthesisError,
    Variable,
};
use cyclotomic_rings::rings::StarkRingNTT;
use latticefold::arith::{error::CSError, r1cs::R1CS};
use stark_rings_linalg::SparseMatrix;

use super::stark_field;
use super::stark_field::StarkFq;

// record constraints

/// following compute_path from bellpepper-core's `util_cs/test_cs.rs`
fn compute_path(ns: &[String], this: &str) -> String {
    assert!(
        !this.chars().any(|a| a == '/'),
        "'/' is not allowed in names"
    );

    if ns.is_empty() {
        return this.to_string();
    }

    format!("{}/{}", ns.join("/"), this)
}

pub struct ShapeCS {
    num_inputs: usize,
    num_aux: usize,

    constraints: Vec<Constraint<StarkFq>>,

    // namespace stack. mirrors `TestConstraintSystem::current_namespace`.
    current_namespace: Vec<String>,

    // variable paths, indexed by `Index::Aux(i)` / `Index::Input(i)`.
    aux_names: Vec<String>,
    input_names: Vec<String>,
}

impl Default for ShapeCS {
    fn default() -> Self {
        Self::new()
    }
}

impl ShapeCS {
    pub fn new() -> Self {
        Self {
            // bellpepper reserves input index 0 for the implicit constant `1`.
            // number of public inputs is num_inputs - 1
            num_inputs: 1,
            num_aux: 0,
            constraints: Vec::new(),
            current_namespace: Vec::new(),
            aux_names: Vec::new(),
            // following `bellpepper::TestConstraintSystem` keeping index 0 for constant 1.
            input_names: vec!["ONE".to_string()],
        }
    }

    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }
    pub fn num_inputs(&self) -> usize {
        self.num_inputs
    }
    pub fn num_aux(&self) -> usize {
        self.num_aux
    }

    pub fn constraints(&self) -> &[Constraint<StarkFq>] {
        &self.constraints
    }

    /// path of the constraint at row, what check_relation
    /// reports in CSError::NotSatisfied(row).
    pub fn constraint_name(&self, row: usize) -> Option<&str> {
        self.constraints
            .get(row)
            .map(|(_, _, _, path)| path.as_str())
    }

    /// path of a bellpepper variable, for debugging unsatisfied constraints
    pub fn variable_name(&self, idx: Index) -> Option<&str> {
        match idx {
            Index::Input(i) => self.input_names.get(i).map(|s| s.as_str()),
            Index::Aux(i) => self.aux_names.get(i).map(|s| s.as_str()),
        }
    }

    /// renders one constraint as path: (A) * (B) = (C) with variables named.
    /// following `TestShapeCS::pretty_print`, which prints each row as
    /// `{name}: (..) * (..) = (..)`; that version falls back to `I{i}` / `A{i}`
    /// for variables, we substitute the recorded paths.
    pub fn pretty_print_constraint(&self, row: usize) -> Option<String> {
        let (a, b, c, path) = self.constraints.get(row)?;
        let render = |lc: &BpLC<StarkFq>| -> String {
            let terms: Vec<String> = lc
                .iter()
                .map(|(v, _)| {
                    self.variable_name(v.get_unchecked())
                        .unwrap_or("<unnamed>")
                        .to_string()
                })
                .collect();
            if terms.is_empty() {
                "0".to_string()
            } else {
                terms.join(" + ")
            }
        };
        Some(format!(
            "{path}: ({}) * ({}) = ({})",
            render(a),
            render(b),
            render(c)
        ))
    }
}

/// Lets `ShapeCS` be diffed against any other bellpepper constraint system via `Comparable::delta`.
impl Comparable<StarkFq> for ShapeCS {
    fn num_inputs(&self) -> usize {
        self.num_inputs
    }

    fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    fn inputs(&self) -> Vec<String> {
        self.input_names.clone()
    }

    fn aux(&self) -> Vec<String> {
        self.aux_names.clone()
    }

    fn constraints(&self) -> &[Constraint<StarkFq>] {
        &self.constraints
    }
}

impl ConstraintSystem<StarkFq> for ShapeCS {
    type Root = Self;

    // Witness variable.
    fn alloc<F, A, AR>(&mut self, annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<StarkFq, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let path = compute_path(&self.current_namespace, &annotation().into());
        self.aux_names.push(path);
        self.num_aux += 1;
        Ok(Variable::new_unchecked(Index::Aux(self.num_aux - 1)))
    }

    // Public input.
    fn alloc_input<F, A, AR>(&mut self, annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<StarkFq, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let path = compute_path(&self.current_namespace, &annotation().into());
        self.input_names.push(path);
        self.num_inputs += 1;
        Ok(Variable::new_unchecked(Index::Input(self.num_inputs - 1)))
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(BpLC<StarkFq>) -> BpLC<StarkFq>,
        LB: FnOnce(BpLC<StarkFq>) -> BpLC<StarkFq>,
        LC: FnOnce(BpLC<StarkFq>) -> BpLC<StarkFq>,
    {
        let path = compute_path(&self.current_namespace, &annotation().into());
        self.constraints
            .push((a(BpLC::zero()), b(BpLC::zero()), c(BpLC::zero()), path));
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        self.current_namespace.push(name_fn().into());
    }

    fn pop_namespace(&mut self) {
        assert!(self.current_namespace.pop().is_some());
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

/// matrices derived from Bellpepper's linear combinations for R1CS over StarkFq.
/// matrix rows are represented by (coefficient, column) following stark_rings_linalg::SparseMatrix.
pub type BpMatrix = Vec<Vec<(StarkFq, usize)>>;

/// permute bellpepper matrices A,B,C and vector z indices to follow latticefold's `z` vector order.
/// bellpepper follows z = (1,x,w), latticefold follows z = (x,1,w).
pub fn permute_index(idx: Index, x_len: usize) -> usize {
    match idx {
        Index::Input(0) => x_len,
        Index::Input(k) => k - 1,
        Index::Aux(j) => x_len + 1 + j,
    }
}

/// compute the permuted matrices A, B, C from a bellpepper `ShapeCS`
pub fn get_matrices(cs: &ShapeCS) -> (BpMatrix, BpMatrix, BpMatrix) {
    let x_len = cs.num_inputs() - 1;

    let row_of = |lc: &BpLC<StarkFq>| -> Vec<(StarkFq, usize)> {
        // `iter()` yields (Variable, &Scalar). Bellpepper already merges repeated
        // terms on the same variable, so no dedup pass is needed here.
        lc.iter()
            .map(|(v, coeff)| (*coeff, permute_index(v.get_unchecked(), x_len)))
            .collect()
    };

    let mut a: BpMatrix = Vec::with_capacity(cs.num_constraints());
    let mut b: BpMatrix = Vec::with_capacity(cs.num_constraints());
    let mut c: BpMatrix = Vec::with_capacity(cs.num_constraints());

    for (a_lc, b_lc, c_lc, _path) in cs.constraints() {
        a.push(row_of(a_lc));
        b.push(row_of(b_lc));
        c.push(row_of(c_lc));
    }

    (a, b, c)
}

// test gadget which uses the same starkfield element (coeff) across all NTT slots and does NTT^{-1} on [v;D] where D=16 to produce a ring element in StarkRingNTT.
pub fn to_sparse_matrix(rows: &BpMatrix, ncols: usize) -> SparseMatrix<StarkRingNTT> {
    SparseMatrix {
        nrows: rows.len(),
        ncols,
        coeffs: rows
            .iter()
            .map(|row| {
                row.iter()
                    // to_ark_fq: our StarkFq (ff::PrimeField, used in Bellpepper) -> stark_rings' Fq (ark_ff::PrimeField, what the ring needs).
                    // both using same modulus.
                    .map(|(coeff, col)| (StarkRingNTT::from(stark_field::to_ark_fq(coeff)), *col))
                    .collect()
            })
            .collect(),
    }
}

// derive latticefold::arith::r1cs::R1CS from our ShapeCS.
pub struct LatticefoldR1CS {
    /// used by CCS::from_r1cs_padded.
    pub r1cs: R1CS<StarkRingNTT>,
    /// row index -> path.
    constraint_names: Vec<String>,
    /// pretty-printed rows of the R1CS, including their namespaces.
    rendered: Vec<String>,
}

impl LatticefoldR1CS {
    /// the path of the first unsatisfied constraint, or `None` if all are satisfied.
    pub fn which_is_unsatisfied(&self, z: &[StarkRingNTT]) -> Option<&str> {
        match self.r1cs.check_relation(z) {
            Ok(()) => None,
            Err(CSError::NotSatisfied(row)) => Some(
                self.constraint_names
                    .get(row)
                    .map(|s| s.as_str())
                    .unwrap_or("<row out of range>"),
            ),
            // for errors such as dimension mismatch.
            // check_relation below reports them properly.
            Err(_) => Some("<check failed for a reason other than an unsatisfied constraint>"),
        }
    }

    /// true if satisfied; prints the unsatisfied constraint if not.
    pub fn is_satisfied(&self, z: &[StarkRingNTT]) -> bool {
        match self.check_relation(z) {
            Ok(()) => true,
            Err(msg) => {
                println!("fail: {msg}");
                // returning false so that an assert!(x.is_satisfied(&z)) is still compatible.
                false
            }
        }
    }

    /// report failing constraint/implementation error along with an error description.
    pub fn check_relation(&self, z: &[StarkRingNTT]) -> Result<(), String> {
        match self.r1cs.check_relation(z) {
            Ok(()) => Ok(()),
            Err(CSError::NotSatisfied(row)) => Err(match self.rendered.get(row) {
                Some(r) => format!("constraint {row} unsatisfied: {r}"),
                None => format!(
                    "constraint {row} unsatisfied, but only {} rows were recorded \
                     (was this z checked against a padded CCS?)",
                    self.rendered.len()
                ),
            }),
            Err(e) => Err(e.to_string()),
        }
    }

    /// path of the constraint at row, invoked using CSError::NotSatisfied(row).
    pub fn constraint_name(&self, row: usize) -> Option<&str> {
        self.constraint_names.get(row).map(|s| s.as_str())
    }
}

pub fn build_r1cs(cs: &ShapeCS) -> LatticefoldR1CS {
    let x_len = cs.num_inputs() - 1;
    let ncols = x_len + 1 + cs.num_aux();

    let (a, b, c) = get_matrices(cs);

    LatticefoldR1CS {
        r1cs: R1CS {
            l: x_len,
            A: to_sparse_matrix(&a, ncols),
            B: to_sparse_matrix(&b, ncols),
            C: to_sparse_matrix(&c, ncols),
        },
        constraint_names: cs
            .constraints()
            .iter()
            .map(|(_, _, _, path)| path.clone())
            .collect(),
        rendered: (0..cs.num_constraints())
            .map(|r| cs.pretty_print_constraint(r).unwrap_or_default())
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::{num::AllocatedNum, test_cs::TestConstraintSystem, Delta};
    use stark_rings::Ring;

    struct CubicCircuit;

    impl CubicCircuit {
        fn synthesize<CS: ConstraintSystem<StarkFq>>(
            &self,
            cs: &mut CS,
            z: &[AllocatedNum<StarkFq>],
        ) -> Result<Vec<AllocatedNum<StarkFq>>, SynthesisError> {
            let x = &z[0];
            let x_sq = x.square(cs.namespace(|| "x_sq"))?;
            let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), x)?;
            let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
                let xv = x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                Ok(xv * xv * xv + xv + StarkFq::from(5u64))
            })?;
            cs.enforce(
                || "y = x^3 + x + 5",
                |lc| lc + x_cu.get_variable() + x.get_variable() + (StarkFq::from(5u64), CS::one()),
                |lc| lc + CS::one(),
                |lc| lc + y.get_variable(),
            );
            Ok(vec![y])
        }
    }

    fn synthesize_test_circuit() -> ShapeCS {
        let mut cs = ShapeCS::new();
        let x =
            AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(StarkFq::from(5u64))).expect("alloc x");
        x.inputize(cs.namespace(|| "x is constrained to a public variable"))
            .expect("inputize x");
        CubicCircuit.synthesize(&mut cs, &[x]).expect("synthesize");
        cs
    }

    fn good_z() -> Vec<StarkRingNTT> {
        // z = (x || 1 || w), witness in allocation order: x, x^2, x^3, y.
        [5u64, 1, 5, 25, 125, 135]
            .into_iter()
            .map(StarkRingNTT::from)
            .collect()
    }

    /// synthesize the same circuit into `ShapeCS` and into
    /// bellpepper's own `TestConstraintSystem`, then diff them with `delta`.
    /// Delta::Equal means the two agree on input count, constraint count,
    /// input names, and every constraint (LinearCombination's). Anything else prints which row diverged.
    #[test]
    fn test_matches_test_constraint_system() {
        let our_shapecs = synthesize_test_circuit();

        let mut bellpepper_cs = TestConstraintSystem::<StarkFq>::new();
        let x = AllocatedNum::alloc(bellpepper_cs.namespace(|| "x"), || Ok(StarkFq::from(5u64)))
            .expect("alloc x");
        // following the test case in Nova for ShapeCS
        x.inputize(bellpepper_cs.namespace(|| "x is constrained to a public variable"))
            .expect("inputize x");
        CubicCircuit
            .synthesize(&mut bellpepper_cs, &[x])
            .expect("synthesize");

        assert!(
            bellpepper_cs.is_satisfied(),
            "reference circuit is itself unsatisfied"
        );

        match our_shapecs.delta(&bellpepper_cs, false) {
            Delta::Equal => {}
            Delta::ConstraintMismatch(row, a, b) => panic!(
                "row {row} differs.\n  ours:   path={:?}\n  theirs: path={:?}",
                a.3, b.3
            ),
            other => panic!("ShapeCS diverges from TestConstraintSystem: {other:?}"),
        }
    }

    // checks our indexing against latticefold's test_r1cs_example_from_constraint_system
    #[test]
    fn test_permute_matches_latticefold_example() {
        let x_len = 1;
        assert_eq!(
            permute_index(Index::Input(1), x_len),
            0,
            "public input -> io block"
        );
        assert_eq!(permute_index(Index::Input(0), x_len), 1, "constant -> z[l]");
        assert_eq!(
            permute_index(Index::Aux(0), x_len),
            2,
            "first witness after (x,1)"
        );
        assert_eq!(
            permute_index(Index::Aux(3), x_len),
            5,
            "witness order preserved"
        );
    }

    #[test]
    fn test_shape_counts() {
        let cs = synthesize_test_circuit();
        assert_eq!(cs.num_inputs(), 2); // constant + x
        assert_eq!(cs.num_aux(), 4); // x (from alloc), x_sq, x_cu, y
        assert_eq!(cs.num_constraints(), 4); // inputize equality, x_sq, x_cu, final
    }

    #[test]
    fn test_compute_path_matches_bellpepper() {
        assert_eq!(
            compute_path(
                &[
                    "hello".to_string(),
                    "world".to_string(),
                    "things".to_string()
                ],
                "thing"
            ),
            "hello/world/things/thing"
        );
        assert_eq!(compute_path(&[], "solo"), "solo");
    }

    #[test]
    #[should_panic(expected = "'/' is not allowed in names")]
    fn test_compute_path_rejects_slash() {
        compute_path(&[], "a/b");
    }

    /// every row must carry a path and the final constraint is must be at top level of the namespace stack,
    /// so it must have no prefix.
    #[test]
    fn test_paths_nest_and_unwind() {
        let cs = synthesize_test_circuit();

        let names: Vec<&str> = (0..cs.num_constraints())
            .map(|r| cs.constraint_name(r).expect("every row is named"))
            .collect();

        assert!(
            names.iter().any(|n| n.starts_with("x_sq/")),
            "nothing recorded under the x_sq namespace: {names:?}"
        );
        assert_eq!(
            *names.last().unwrap(),
            "y = x^3 + x + 5",
            "namespace stack did not unwind -- pop_namespace is not firing"
        );
    }

    #[test]
    fn test_variable_names() {
        let cs = synthesize_test_circuit();
        assert_eq!(cs.variable_name(Index::Input(0)), Some("ONE"));
        assert_eq!(cs.variable_name(Index::Aux(0)), Some("x/num"));
        assert!(cs
            .variable_name(Index::Aux(1))
            .unwrap()
            .starts_with("x_sq/"));
        assert!(cs
            .variable_name(Index::Input(1))
            .unwrap()
            .starts_with("x is constrained to a public variable/"));
    }

    #[test]
    fn test_extracted_r1cs_is_satisfied() {
        let cs = synthesize_test_circuit();
        let extracted = build_r1cs(&cs);

        assert_eq!(extracted.r1cs.l, 1, "one public input");
        assert_eq!(extracted.r1cs.A.nrows, 4);
        assert_eq!(extracted.r1cs.A.ncols, 6, "x_len(1) + constant(1) + aux(4)");

        assert!(extracted.is_satisfied(&good_z()));
        assert_eq!(extracted.which_is_unsatisfied(&good_z()), None);
    }

    #[test]
    fn test_wrong_witness_is_rejected_and_named() {
        let cs = synthesize_test_circuit();
        let extracted = build_r1cs(&cs);

        // y off by one: 136 instead of 135.
        let bad: Vec<StarkRingNTT> = [5u64, 1, 5, 25, 125, 136]
            .into_iter()
            .map(StarkRingNTT::from)
            .collect();

        let err = extracted.check_relation(&bad).expect_err(
            "a wrong witness was accepted -- the extraction is not constraining anything; \
             check permute_index and that enforce() stores all three LCs",
        );

        // the failure must name the constraint, not just its index.
        assert!(
            err.contains("y = x^3 + x + 5"),
            "failure was not named: {err}"
        );
        // ...and render it in the circuit's own variable names.
        assert!(
            err.contains("ONE"),
            "failure was not rendered with variable names: {err}"
        );

        assert_eq!(
            extracted.which_is_unsatisfied(&bad),
            Some("y = x^3 + x + 5")
        );
        // println!("wrong witness error: {err}");
    }
}
