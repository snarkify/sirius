use halo2_proofs::plonk::Expression as PE;

use crate::{ff::PrimeField, polynomial::Expression};

/// compress a vector of halo2 expressions into one by random linear combine a challenge
pub(crate) fn compress_halo2_expression<F: PrimeField>(
    exprs: &[PE<F>],
    num_selectors: usize,
    num_fixed: usize,
    challenge_index: usize,
) -> Expression<F> {
    let y = Expression::Challenge(challenge_index);
    if exprs.len() > 1 {
        exprs
            .iter()
            .map(|expr| Expression::from_halo2_expr(expr, num_selectors, num_fixed))
            .fold(Expression::Constant(F::ZERO), |acc, expr| {
                Expression::Sum(
                    Box::new(expr),
                    Box::new(Expression::Product(Box::new(acc), Box::new(y.clone()))),
                )
            })
    } else {
        Expression::from_halo2_expr(&exprs[0], num_selectors, num_fixed)
    }
}

/// compress a vector of [`Expression`] into one by random linear combine a challenge
pub(crate) fn compress_expression<F: PrimeField>(
    exprs: &[Expression<F>],
    challenge_index: usize,
) -> Expression<F> {
    let y = Expression::Challenge(challenge_index);
    if exprs.len() > 1 {
        exprs
            .iter()
            .fold(Expression::Constant(F::ZERO), |acc, expr| {
                Expression::Sum(
                    Box::new(expr.clone()),
                    Box::new(Expression::Product(Box::new(acc), Box::new(y.clone()))),
                )
            })
    } else {
        exprs
            .first()
            .cloned()
            .unwrap_or(Expression::Constant(F::ZERO))
    }
}
