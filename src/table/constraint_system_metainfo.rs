use ff::PrimeField;
use halo2_proofs::plonk::ConstraintSystem;

use crate::{
    concat_vec, plonk,
    polynomial::{Expression, MultiPolynomial},
};

pub(crate) struct ConstraintSystemMetainfo<F: PrimeField> {
    pub num_challenges: usize,
    pub round_sizes: Vec<usize>,
    pub folding_degree: usize,
    pub poly: MultiPolynomial<F>,
    pub custom_gates_lookup_compressed: Expression<F>,
}

impl<F: PrimeField> ConstraintSystemMetainfo<F> {
    /// The separation of this function from circuit_info is to remove dependency on [`PlonkStructure`]
    /// it is used to kickstart the Folding Circuit initialization
    pub(crate) fn build(
        k_table_size: usize,
        cs: &ConstraintSystem<F>,
    ) -> ConstraintSystemMetainfo<F> {
        let num_gates: usize = cs.gates().iter().map(|gate| gate.polynomials().len()).sum();

        let lookup_arguments = plonk::lookup::Arguments::compress_from(cs);
        let (num_lookups, has_vector_lookup, lookup_exprs) = lookup_arguments
            .as_ref()
            .map(|arg| {
                (
                    arg.lookup_polys.len(),
                    arg.has_vector_lookup,
                    concat_vec!(
                        &arg.vanishing_lookup_polys(cs),
                        &arg.log_derivative_lhs_and_rhs(cs)
                    ),
                )
            })
            .unwrap_or((0, false, vec![]));

        let exprs = cs
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter())
            .map(|expr| {
                Expression::from_halo2_expr(expr, cs.num_selectors(), cs.num_fixed_columns())
            })
            .chain(lookup_exprs)
            .collect::<Vec<_>>();

        let num_challenges = if has_vector_lookup {
            3
        } else if num_lookups > 0 {
            2
        } else if num_gates > 1 {
            1
        } else {
            0
        };

        // we have at most 3 prover rounds
        let nrow = 1 << k_table_size;

        let mut round_sizes = Vec::new();

        if has_vector_lookup {
            round_sizes.extend([
                // advice columns
                cs.num_advice_columns() * nrow,
                // (l_i, t_i, m_i), see [`lookup.rs::Arguments::log_derivative_expr`]
                3 * num_lookups * nrow,
                // (h_i, g_i), see [`lookup.rs::Arguments::log_derivative_expr`]
                2 * num_lookups * nrow,
            ]);
        } else if num_lookups > 0 {
            round_sizes.extend([
                // advice columns || (l_i, t_i, m_i)
                (cs.num_advice_columns() + 3 * num_lookups) * nrow,
                // (h_i, g_i)
                2 * num_lookups * nrow,
            ]);
        } else {
            // advice columns
            round_sizes.push(cs.num_advice_columns() * nrow);
        };

        // we use r3 to combine all custom gates and lookup expressions
        // find the challenge index of r3
        let challenge_index = if num_challenges > 0 {
            num_challenges - 1
        } else {
            0
        };

        let custom_gates_lookup_compressed =
            plonk::util::compress_expression(&exprs, challenge_index);
        let poly = custom_gates_lookup_compressed.expand();

        let folding_degree = poly.degree_for_folding(cs.num_fixed_columns() + cs.num_selectors());

        ConstraintSystemMetainfo {
            num_challenges,
            round_sizes,
            folding_degree,
            poly,
            custom_gates_lookup_compressed,
        }
    }
}
