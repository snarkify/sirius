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
#[derive(Clone, PartialEq)]
pub struct Argument<F: PrimeField> {
    lookup_poly: MultiPolynomial<F>,
    table_poly: MultiPolynomial<F>,
}

/// the evaluation of lookup arguments, i.e.:
/// lookup_vec = \vec{l} = \{l_i\} with l_i = L(x1[i],...,xa[i])
/// table_vec = \vec{t} = \{t_i\} with t_i = L(y1[i],...,yb[i])
/// multiplicity_vec = \vec{m_i}
#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    l: Vec<F>,
    t: Vec<F>,
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
            })
            .collect::<Vec<_>>()
    }
}

impl<F: PrimeField> Witness<F> {
    pub fn new(&self, l: Vec<F>, t: Vec<F>) -> Self {
        Self { l, t }
    }

    /// calculate the coefficients {m_i} in the log derivative formula
    /// m_i = sum_j \xi(w_j=t_i) assuming {t_i} have no duplicates
    pub fn log_derivative_coeffs(&self) -> Vec<F> {
        let mut m: Vec<F> = Vec::new();
        let mut processed_t = Vec::new();
        for t_i in &self.t {
            if processed_t.contains(&t_i) {
                // If the current t_i has already been processed, push 0 to m
                m.push(F::ZERO);
            } else {
                let m_i = self.l.iter().filter(|l_j| *l_j == t_i).count() as u128;
                m.push(F::from_u128(m_i));
                processed_t.push(t_i);
            }
        }
        m
    }

    /// calculate the inverse in log derivative formula
    /// h_i := \frac{1}{l_i+r}
    /// g_i := \frac{m_i}{t_i+r}
    pub fn calc_inverse_terms(&self, r: F, m: &[F]) -> (Vec<F>, Vec<F>) {
        let h = self
            .l
            .iter()
            .map(|&l_i| Option::from((l_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        let g = self
            .t
            .iter()
            .zip(m)
            .map(|(t_i, m_i)| *m_i * Option::from((*t_i + r).invert()).unwrap_or(F::ZERO))
            .collect::<Vec<F>>();
        (h, g)
    }

    /// check whether the lookup argument is satisfied
    /// the remaining check L(x1,...,xa)=l and T(y1,...,ya)=t
    /// are carried in upper level check
    pub fn is_sat(&self, r: F) -> Result<(), String> {
        let m = self.log_derivative_coeffs();
        let (h, g) = self.calc_inverse_terms(r, &m);
        // check hi(li+r)-1=0 or check (li+r)*(hi(li+r)-1)=0 for perfect completeness
        let c1 = self
            .l
            .iter()
            .zip(h.iter())
            .map(|(li, hi)| *hi * (*li + r) - F::ONE)
            .filter(|d| F::ZERO.ne(d))
            .count();

        // check gi(ti+r)-mi=0 or check (ti+r)*(gi(ti+r)-mi)=0 for perfect completeness
        let c2 = self
            .t
            .iter()
            .zip(g.iter())
            .zip(m)
            .map(|((ti, gi), mi)| *gi * (*ti + r) - mi)
            .filter(|d| F::ZERO.ne(d))
            .count();

        // check sum_i h_i = sum_i g_i
        let sum = h
            .into_iter()
            .zip(g)
            .map(|(hi, gi)| hi - gi)
            .fold(F::ZERO, |acc, d| acc + d);
        let c3 = F::ZERO.ne(&sum);
        match (c1 == 0, c2 == 0, c3) {
            (true, true, true) => Ok(()),
            (false, _, _) => Err(format!("hi(li+r)-1=0 not satisfied on {} rows", c1,).to_string()),
            (true, false, _) => {
                Err(format!("gi(ti+r)-mi=0 not satisfied on {} rows", c2,).to_string())
            }
            (true, true, false) => Err("sum hi = sum gi not satisfied".to_string()),
        }
    }
}
