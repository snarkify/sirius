pub mod expression;
pub mod graph_evaluator;
pub mod grouped_poly;
pub mod sparse;
pub mod univariate;

pub use expression::{ColumnIndex, Expression, Query, QueryType};

pub mod lagrange;
