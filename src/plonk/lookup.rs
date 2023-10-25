use crate::polynomial::{Expression, MultiPolynomial, Query};
use ff::PrimeField;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Expression as PE;
use halo2_proofs::poly::Rotation;

/// starting from vector lookup: {(a1,a2,...,ak)} \subset {(t1,t2,...,tk)}
/// where {ai} are expressions over columns (x1,...xa)
/// {ti} are expressions over columns (y1,...,yb)
/// compress them into one multi-polynomial:
/// lookup_poly = L(x1,...,xa) = a1+a2*r+a3*r^2+...
/// table_poly = T(y1,...,yb) = t1+t2*r+t3*r^2+...
/// with corresponding evaluations of L and T over rows: \vec{l} and \vec{T}
#[derive(Clone, PartialEq)]
pub struct Argument<F: PrimeField> {
    lookup_poly: MultiPolynomial<F>,
    table_poly: MultiPolynomial<F>,
    lookup_vec: Vec<F>,
    table_vec: Vec<F>,
}

impl<F: PrimeField> Argument<F> {
    /// retrieve and compress vector of Lookup Arguments from constraint system
    /// TODO: halo2 assumes lookup relation to be true over all rows, in reality we may only
    /// lookup a few items. need find a way to remove padded rows for lookup_vec
    pub fn new(cs: &ConstraintSystem<F>) -> Vec<Self> {
        // we use the same challenge y for combining custom gates and multiple lookup arguments
        // need first commit all witness before generating y
        let y = Expression::Polynomial(Query {
            index: cs.num_selectors() + cs.num_fixed_columns() + cs.num_advice_columns(),
            rotation: Rotation(0),
        });
        // suppose we have n polynomial expression: p_1,p_2,...,p_n
        // we combined them together as one: combined_poly = p_1*y^{n-1}+p_2*y^{n-2}+...+p_n
        let compress_expression = |exprs: &[PE<F>]| -> MultiPolynomial<F> {
            exprs
                .iter()
                .map(|expr| {
                    Expression::from_halo2_expr(expr, cs.num_selectors(), cs.num_fixed_columns())
                })
                .fold(Expression::Constant(F::ZERO), |acc, expr| {
                    Expression::Sum(
                        Box::new(expr),
                        Box::new(Expression::Product(Box::new(acc), Box::new(y.clone()))),
                    )
                })
                .expand()
        };
        let input_polys = cs
            .lookups()
            .iter()
            .map(|arg| compress_expression(arg.input_expressions()))
            .collect::<Vec<_>>();
        let table_polys = cs
            .lookups()
            .iter()
            .map(|arg| compress_expression(arg.table_expressions()))
            .collect::<Vec<_>>();

        input_polys
            .into_iter()
            .zip(table_polys)
            .map(|(lookup_poly, table_poly)| Self {
                lookup_poly,
                table_poly,
                lookup_vec: vec![],
                table_vec: vec![],
            })
            .collect::<Vec<_>>()
    }
}
