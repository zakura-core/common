//! Straight-line field-arithmetic emission over the fused gate fold's query
//! frame, shared by the weighted-lowering macros.

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use sensei_shared::{
    expressions::Expression,
    queries::{GATE_QUERY_DESCRIPTORS, QueryKind},
};
use syn::{Error, Result};

/// Emits straight-line field arithmetic over the invoking module's `Fp`
/// query frame `q`, binding every repeated subtree once.
#[derive(Default)]
pub(crate) struct Emitter {
    pub(crate) statements: Vec<TokenStream>,
    values: Vec<(Expression, TokenStream)>,
}

impl Emitter {
    pub(crate) fn value(&mut self, tree: &Expression) -> Result<TokenStream> {
        if let Some((_, tokens)) = self.values.iter().find(|(known, _)| known == tree) {
            return Ok(tokens.clone());
        }
        let tokens = match tree {
            Expression::Advice(index) => frame_slot(QueryKind::Advice, usize::from(*index))?,
            Expression::Fixed(index) => frame_slot(QueryKind::Fixed, usize::from(*index))?,
            Expression::Instance(_) => {
                return Err(Error::new(
                    Span::call_site(),
                    "the gate query frame has no instance queries",
                ));
            }
            Expression::Constant(index) => {
                let index = usize::from(*index);
                quote!(constant(#index))
            }
            Expression::Sum(left, right) => {
                let left = self.value(left)?;
                let expression = match right.as_ref() {
                    Expression::Negated(subtrahend) => {
                        let subtrahend = self.value(subtrahend)?;
                        quote!(#left.sub(&#subtrahend))
                    }
                    addend => {
                        let addend = self.value(addend)?;
                        quote!(#left.add(&#addend))
                    }
                };
                self.bind(expression)
            }
            Expression::Product(left, right) => {
                let expression = if left == right {
                    let base = self.value(left)?;
                    quote!(#base.square())
                } else {
                    let left = self.value(left)?;
                    let right = self.value(right)?;
                    quote!(#left.mul(&#right))
                };
                self.bind(expression)
            }
            Expression::Negated(inner) => {
                let inner = self.value(inner)?;
                self.bind(quote!(#inner.neg()))
            }
            Expression::ConstantScaled(inner, index) => {
                let inner = self.value(inner)?;
                let index = usize::from(*index);
                self.bind(quote!(scale(&#inner, #index)))
            }
        };
        self.values.push((tree.clone(), tokens.clone()));
        Ok(tokens)
    }

    fn bind(&mut self, expression: TokenStream) -> TokenStream {
        let name = format_ident!("v{}", self.statements.len());
        self.statements.push(quote!(let #name = #expression;));
        quote!(#name)
    }
}

/// The frame slot the fused fold reads a query at, as `q[slot]`.
pub(crate) fn frame_slot(kind: QueryKind, index: usize) -> Result<TokenStream> {
    let slot = GATE_QUERY_DESCRIPTORS
        .iter()
        .position(|descriptor| *descriptor == (kind, index))
        .ok_or_else(|| {
            Error::new(
                Span::call_site(),
                format!("{kind:?} query {index} is not in the gate query frame"),
            )
        })?;
    Ok(quote!(q[#slot]))
}

/// The dynamic bodies of `trees` under one shared fixed root factor.
pub(crate) fn shared_selector_bodies<'a>(trees: &[&'a Expression]) -> Result<Vec<&'a Expression>> {
    let error = |message: &str| Error::new(Span::call_site(), message);
    let mut bodies = Vec::with_capacity(trees.len());
    let mut selector = None;
    for tree in trees {
        let (factor, body) = tree
            .fixed_root_split()
            .ok_or_else(|| error("every lowered constraint needs a fixed root factor"))?;
        match selector {
            None => selector = Some(factor),
            Some(selector) if selector == factor => {}
            Some(_) => return Err(error("lowered constraints must share one selector")),
        }
        bodies.push(body);
    }
    Ok(bodies)
}
