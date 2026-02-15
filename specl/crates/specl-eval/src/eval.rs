//! Expression evaluator for Specl.

use crate::value::Value;
use crate::value::VK;
use specl_ir::{BinOp, CompiledExpr, UnaryOp};
use std::sync::Arc;
use thiserror::Error;

/// Evaluation error.
#[derive(Debug, Error)]
pub enum EvalError {
    #[error("type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("index out of bounds: index {index}, length {length}")]
    IndexOutOfBounds { index: i64, length: usize },

    #[error("key not found: {0}")]
    KeyNotFound(String),

    #[error("division by zero")]
    DivisionByZero,

    #[error("no satisfying value for choose")]
    ChooseFailed,

    #[error("undefined variable at index {0}")]
    UndefinedVariable(usize),

    #[error("undefined constant at index {0}")]
    UndefinedConstant(usize),

    #[error("internal error: {0}")]
    Internal(String),
}

pub type EvalResult<T> = Result<T, EvalError>;

/// Evaluation context providing access to state and constants.
pub struct EvalContext<'a> {
    /// Current state variable values (indexed by variable index).
    pub vars: &'a [Value],
    /// Next state variable values (indexed by variable index).
    pub next_vars: &'a [Value],
    /// Constant values (indexed by constant index).
    pub consts: &'a [Value],
    /// Action parameters (indexed by parameter index).
    pub params: &'a [Value],
    /// Local variable stack (de Bruijn indexed from end).
    pub locals: Vec<Value>,
}

impl<'a> EvalContext<'a> {
    /// Create a new evaluation context.
    pub fn new(
        vars: &'a [Value],
        next_vars: &'a [Value],
        consts: &'a [Value],
        params: &'a [Value],
    ) -> Self {
        Self {
            vars,
            next_vars,
            consts,
            params,
            locals: Vec::new(),
        }
    }

    /// Push a local variable onto the stack.
    pub fn push_local(&mut self, value: Value) {
        self.locals.push(value);
    }

    /// Pop a local variable from the stack.
    pub fn pop_local(&mut self) -> Option<Value> {
        self.locals.pop()
    }

    /// Get a local variable by de Bruijn index (0 = innermost).
    pub fn get_local(&self, index: usize) -> Option<&Value> {
        let stack_index = self.locals.len().checked_sub(1 + index)?;
        self.locals.get(stack_index)
    }
}

/// Evaluate a compiled expression.
pub fn eval(expr: &CompiledExpr, ctx: &mut EvalContext) -> EvalResult<Value> {
    match expr {
        CompiledExpr::Bool(b) => Ok(Value::bool(*b)),
        CompiledExpr::Int(n) => Ok(Value::int(*n)),
        CompiledExpr::String(s) => Ok(Value::string(s.clone())),

        CompiledExpr::Var(idx) => ctx
            .vars
            .get(*idx)
            .cloned()
            .ok_or(EvalError::UndefinedVariable(*idx)),

        CompiledExpr::PrimedVar(idx) => ctx
            .next_vars
            .get(*idx)
            .cloned()
            .ok_or(EvalError::UndefinedVariable(*idx)),

        CompiledExpr::Const(idx) => ctx
            .consts
            .get(*idx)
            .cloned()
            .ok_or(EvalError::UndefinedConstant(*idx)),

        CompiledExpr::Local(idx) => ctx
            .get_local(*idx)
            .cloned()
            .ok_or_else(|| EvalError::Internal(format!("local {} not found", idx))),

        CompiledExpr::Param(idx) => ctx
            .params
            .get(*idx)
            .cloned()
            .ok_or_else(|| EvalError::Internal(format!("param {} not found", idx))),

        CompiledExpr::Binary { op, left, right } => eval_binary(*op, left, right, ctx),

        CompiledExpr::Unary { op, operand } => eval_unary(*op, operand, ctx),

        CompiledExpr::SetLit(elements) => {
            let mut set = Vec::new();
            for elem in elements {
                Value::set_insert(&mut set, eval(elem, ctx)?);
            }
            Ok(Value::set(Arc::new(set)))
        }

        CompiledExpr::SeqLit(elements) => {
            let seq: Vec<_> = elements
                .iter()
                .map(|e| eval(e, ctx))
                .collect::<EvalResult<_>>()?;
            Ok(Value::seq(seq))
        }

        CompiledExpr::TupleLit(elements) => {
            let tuple: Vec<_> = elements
                .iter()
                .map(|e| eval(e, ctx))
                .collect::<EvalResult<_>>()?;
            Ok(Value::tuple(tuple))
        }

        CompiledExpr::DictLit(entries) => {
            let mut dict = Vec::new();
            for (key, value) in entries {
                let k = eval(key, ctx)?;
                let v = eval(value, ctx)?;
                Value::fn_insert(&mut dict, k, v);
            }
            Ok(Value::func(Arc::new(dict)))
        }

        CompiledExpr::FnLit { domain, body } => {
            // Fast path: Range domain avoids materializing the set
            if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                let lo_val = expect_int(&eval(lo, ctx)?)?;
                let hi_val = expect_int(&eval(hi, ctx)?)?;
                let mut map = Vec::with_capacity((hi_val - lo_val + 1).max(0) as usize);
                for i in lo_val..=hi_val {
                    ctx.push_local(Value::int(i));
                    let value = eval(body, ctx)?;
                    ctx.pop_local();
                    map.push((Value::int(i), value));
                }
                // Produce IntMap if keys start at 0 (dense 0..N dict)
                if lo_val == 0 {
                    let arr: Vec<Value> = map.into_iter().map(|(_, v)| v).collect();
                    return Ok(Value::intmap(Arc::new(arr)));
                }
                return Ok(Value::func(Arc::new(map)));
            }

            let domain_val = eval(domain, ctx)?;
            let domain_elems = extract_domain_elements(&domain_val)?;
            let mut map = Vec::with_capacity(domain_elems.len());
            for key in &domain_elems {
                ctx.push_local(key.clone());
                let value = eval(body, ctx)?;
                ctx.pop_local();
                map.push((key.clone(), value));
            }
            // domain_set is already sorted, so map is sorted by key
            Ok(Value::func(Arc::new(map)))
        }

        CompiledExpr::Index { base, index } => {
            let base_val = eval(base, ctx)?;
            let index_val = eval(index, ctx)?;

            match base_val.kind() {
                VK::Seq(seq) => {
                    let idx = expect_int(&index_val)?;
                    if idx < 0 || idx as usize >= seq.len() {
                        return Err(EvalError::IndexOutOfBounds {
                            index: idx,
                            length: seq.len(),
                        });
                    }
                    Ok(seq[idx as usize].clone())
                }
                VK::IntMap(arr) => {
                    let k = expect_int(&index_val)? as usize;
                    Ok(arr[k].clone())
                }
                VK::Fn(map) => Value::fn_get(map, &index_val)
                    .cloned()
                    .ok_or_else(|| EvalError::KeyNotFound(index_val.to_string())),
                _ => Err(type_mismatch("Seq or Fn", &base_val)),
            }
        }

        CompiledExpr::Slice { base, lo, hi } => {
            let base_val = eval(base, ctx)?;
            let lo_val = expect_int(&eval(lo, ctx)?)?;
            let hi_val = expect_int(&eval(hi, ctx)?)?;

            match base_val.kind() {
                VK::Seq(seq) => {
                    let start = lo_val.max(0) as usize;
                    let end = if hi_val < 0 {
                        0
                    } else {
                        (hi_val as usize).min(seq.len())
                    };
                    if start >= end {
                        Ok(Value::seq(Vec::new()))
                    } else {
                        Ok(Value::seq(seq[start..end].to_vec()))
                    }
                }
                _ => Err(type_mismatch("Seq", &base_val)),
            }
        }

        CompiledExpr::Field { base, field } => {
            let base_val = eval(base, ctx)?;
            match base_val.kind() {
                VK::Record(r) => r
                    .get(field)
                    .cloned()
                    .ok_or_else(|| EvalError::KeyNotFound(field.clone())),
                _ => Err(type_mismatch("Record", &base_val)),
            }
        }

        CompiledExpr::Call { func, args } => {
            let func_val = eval(func, ctx)?;
            match func_val.kind() {
                VK::IntMap(arr) => {
                    if args.len() != 1 {
                        return Err(EvalError::Internal(
                            "function call with wrong arity".to_string(),
                        ));
                    }
                    let arg = eval(&args[0], ctx)?;
                    let k = expect_int(&arg)? as usize;
                    Ok(arr[k].clone())
                }
                VK::Fn(map) => {
                    if args.len() != 1 {
                        return Err(EvalError::Internal(
                            "function call with wrong arity".to_string(),
                        ));
                    }
                    let arg = eval(&args[0], ctx)?;
                    Value::fn_get(map, &arg)
                        .cloned()
                        .ok_or_else(|| EvalError::KeyNotFound(arg.to_string()))
                }
                _ => Err(type_mismatch("Fn", &func_val)),
            }
        }

        CompiledExpr::ActionCall { .. } => {
            // Action calls are handled specially by the model checker
            Err(EvalError::Internal(
                "action calls should be handled by model checker".to_string(),
            ))
        }

        CompiledExpr::RecordUpdate { base, updates } => {
            let base_val = eval(base, ctx)?;
            if !base_val.is_record() {
                return Err(type_mismatch("Record", &base_val));
            }
            let mut record = base_val.into_record_arc();
            let r = Arc::make_mut(&mut record);
            for (name, value) in updates {
                r.insert(name.clone(), eval(value, ctx)?);
            }
            Ok(Value::from_record_arc(record))
        }

        CompiledExpr::FnUpdate { base, key, value } => {
            let base_val = eval(base, ctx)?;
            let key_val = eval(key, ctx)?;
            let value_val = eval(value, ctx)?;
            if base_val.is_intmap() {
                let mut arr = base_val.into_intmap_arc();
                let k = expect_int(&key_val)? as usize;
                Arc::make_mut(&mut arr)[k] = value_val;
                Ok(Value::from_intmap_arc(arr))
            } else if base_val.is_fn() {
                let mut map = base_val.into_fn_arc();
                Value::fn_insert(Arc::make_mut(&mut map), key_val, value_val);
                Ok(Value::from_fn_arc(map))
            } else {
                Err(type_mismatch("Fn", &base_val))
            }
        }

        CompiledExpr::SetComprehension {
            element,
            domain,
            filter,
        } => {
            let mut result = Vec::new();

            // Fast path: Range domain avoids materializing the set
            if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                let lo_val = expect_int(&eval(lo, ctx)?)?;
                let hi_val = expect_int(&eval(hi, ctx)?)?;
                for i in lo_val..=hi_val {
                    ctx.push_local(Value::int(i));
                    let include = if let Some(f) = filter {
                        expect_bool(&eval(f, ctx)?)?
                    } else {
                        true
                    };
                    if include {
                        let elem = eval(element, ctx)?;
                        Value::set_insert(&mut result, elem);
                    }
                    ctx.pop_local();
                }
                return Ok(Value::set(Arc::new(result)));
            }

            let domain_val = eval(domain, ctx)?;
            let domain_elems = extract_domain_elements(&domain_val)?;

            for item in &domain_elems {
                ctx.push_local(item.clone());

                let include = if let Some(f) = filter {
                    expect_bool(&eval(f, ctx)?)?
                } else {
                    true
                };

                if include {
                    let elem = eval(element, ctx)?;
                    Value::set_insert(&mut result, elem);
                }

                ctx.pop_local();
            }

            Ok(Value::set(Arc::new(result)))
        }

        CompiledExpr::Forall { domain, body } => {
            // Fast path: Range domain avoids materializing the set
            if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                let lo_val = expect_int(&eval(lo, ctx)?)?;
                let hi_val = expect_int(&eval(hi, ctx)?)?;
                for i in lo_val..=hi_val {
                    ctx.push_local(Value::int(i));
                    let result = expect_bool(&eval(body, ctx)?)?;
                    ctx.pop_local();
                    if !result {
                        return Ok(Value::bool(false));
                    }
                }
                return Ok(Value::bool(true));
            }

            // Fast path: Forall over Powerset
            if let CompiledExpr::Powerset(inner_domain) = domain.as_ref() {
                return Ok(Value::bool(forall_over_powerset_bool(
                    inner_domain,
                    body,
                    ctx,
                )?));
            }

            let domain_val = eval(domain, ctx)?;
            let domain_elems = extract_domain_elements(&domain_val)?;

            for item in &domain_elems {
                ctx.push_local(item.clone());
                let result = expect_bool(&eval(body, ctx)?)?;
                ctx.pop_local();
                if !result {
                    return Ok(Value::bool(false));
                }
            }

            Ok(Value::bool(true))
        }

        CompiledExpr::Exists { domain, body } => {
            // Fast path: Range domain avoids materializing the set
            if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                let lo_val = expect_int(&eval(lo, ctx)?)?;
                let hi_val = expect_int(&eval(hi, ctx)?)?;
                for i in lo_val..=hi_val {
                    ctx.push_local(Value::int(i));
                    let result = expect_bool(&eval(body, ctx)?)?;
                    ctx.pop_local();
                    if result {
                        return Ok(Value::bool(true));
                    }
                }
                return Ok(Value::bool(false));
            }

            // Fast path: Exists over Powerset
            if let CompiledExpr::Powerset(inner_domain) = domain.as_ref() {
                return Ok(Value::bool(exists_over_powerset_bool(
                    inner_domain,
                    body,
                    ctx,
                )?));
            }

            let domain_val = eval(domain, ctx)?;
            let domain_elems = extract_domain_elements(&domain_val)?;

            for item in &domain_elems {
                ctx.push_local(item.clone());
                let result = expect_bool(&eval(body, ctx)?)?;
                ctx.pop_local();
                if result {
                    return Ok(Value::bool(true));
                }
            }

            Ok(Value::bool(false))
        }

        CompiledExpr::Choose { domain, predicate } => {
            let domain_val = eval(domain, ctx)?;
            let domain_elems = extract_domain_elements(&domain_val)?;

            // Find the first satisfying element (deterministic due to sorted ordering)
            for item in &domain_elems {
                ctx.push_local(item.clone());
                let result = expect_bool(&eval(predicate, ctx)?)?;
                ctx.pop_local();
                if result {
                    return Ok(item.clone());
                }
            }

            Err(EvalError::ChooseFailed)
        }

        CompiledExpr::Fix { predicate: _ } => {
            // Fix without domain cannot be evaluated directly -
            // the spec needs to be rewritten with an explicit domain
            Err(EvalError::ChooseFailed)
        }

        CompiledExpr::Let { value, body } => {
            let val = eval(value, ctx)?;
            ctx.push_local(val);
            let result = eval(body, ctx)?;
            ctx.pop_local();
            Ok(result)
        }

        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond_val = expect_bool(&eval(cond, ctx)?)?;
            if cond_val {
                eval(then_branch, ctx)
            } else {
                eval(else_branch, ctx)
            }
        }

        CompiledExpr::Changes(_) => {
            // Changes is used during frame analysis, not runtime evaluation
            // At runtime, we just return true (the change is allowed)
            Ok(Value::bool(true))
        }

        CompiledExpr::Unchanged(idx) => {
            // Check that var' == var
            let current = ctx
                .vars
                .get(*idx)
                .ok_or(EvalError::UndefinedVariable(*idx))?;
            let next = ctx
                .next_vars
                .get(*idx)
                .ok_or(EvalError::UndefinedVariable(*idx))?;
            Ok(Value::bool(current == next))
        }

        CompiledExpr::Enabled(_) => {
            // Enabled is evaluated by the model checker
            Err(EvalError::Internal(
                "enabled should be handled by model checker".to_string(),
            ))
        }

        CompiledExpr::Range { lo, hi } => {
            let lo_val = expect_int(&eval(lo, ctx)?)?;
            let hi_val = expect_int(&eval(hi, ctx)?)?;
            Ok(Value::range(lo_val, hi_val))
        }

        CompiledExpr::SeqHead(seq) => {
            let seq_val = eval(seq, ctx)?;
            match seq_val.kind() {
                VK::Seq(s) if !s.is_empty() => Ok(s[0].clone()),
                VK::Seq(_) => Err(EvalError::IndexOutOfBounds {
                    index: 0,
                    length: 0,
                }),
                _ => Err(type_mismatch("Seq", &seq_val)),
            }
        }

        CompiledExpr::SeqTail(seq) => {
            let seq_val = eval(seq, ctx)?;
            match seq_val.kind() {
                VK::Seq(s) if !s.is_empty() => Ok(Value::seq(s[1..].to_vec())),
                VK::Seq(_) => Ok(Value::seq(vec![])),
                _ => Err(type_mismatch("Seq", &seq_val)),
            }
        }

        CompiledExpr::Len(expr) => {
            // Fast path: len({x in D if pred}) -> count without materializing set
            if let CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } = expr.as_ref()
            {
                if matches!(element.as_ref(), CompiledExpr::Local(0)) {
                    if let Some(filter) = filter {
                        return Ok(Value::int(count_filtered(domain, filter, ctx)?));
                    }
                }
            }
            let val = eval(expr, ctx)?;
            match val.kind() {
                VK::Seq(s) => Ok(Value::int(s.len() as i64)),
                VK::Set(s) => Ok(Value::int(s.len() as i64)),
                VK::Fn(m) => Ok(Value::int(m.len() as i64)),
                VK::IntMap(arr) => Ok(Value::int(arr.len() as i64)),
                _ => Err(type_mismatch("Seq, Set, or Fn", &val)),
            }
        }

        CompiledExpr::Keys(expr) => {
            let val = eval(expr, ctx)?;
            match val.kind() {
                // Keys of sorted fn vec are already sorted
                VK::IntMap(arr) => Ok(Value::set(Arc::new(
                    (0..arr.len() as i64).map(Value::int).collect(),
                ))),
                VK::Fn(m) => Ok(Value::set(Arc::new(
                    m.iter().map(|(k, _)| k.clone()).collect(),
                ))),
                // For sequences, DOMAIN returns 1..Len(seq) -- already sorted
                VK::Seq(s) => Ok(Value::set(Arc::new(
                    (1..=s.len() as i64).map(Value::int).collect(),
                ))),
                _ => Err(type_mismatch("Fn or Seq", &val)),
            }
        }

        CompiledExpr::Values(expr) => {
            let val = eval(expr, ctx)?;
            match val.kind() {
                VK::IntMap(arr) => {
                    let mut vals: Vec<Value> = arr.to_vec();
                    vals.sort();
                    vals.dedup();
                    Ok(Value::set(Arc::new(vals)))
                }
                VK::Fn(m) => {
                    let mut vals: Vec<Value> = m.iter().map(|(_, v)| v.clone()).collect();
                    vals.sort();
                    vals.dedup();
                    Ok(Value::set(Arc::new(vals)))
                }
                _ => Err(type_mismatch("Fn", &val)),
            }
        }

        CompiledExpr::BigUnion(expr) => {
            let val = eval(expr, ctx)?;
            let outer_set = expect_set(&val)?;
            let mut result = Vec::new();
            for inner in outer_set {
                let inner_set = expect_set(inner)?;
                for elem in inner_set {
                    Value::set_insert(&mut result, elem.clone());
                }
            }
            Ok(Value::set(Arc::new(result)))
        }

        CompiledExpr::Powerset(expr) => {
            let val = eval(expr, ctx)?;
            let input_set = expect_set(&val)?;
            let n = input_set.len();
            let mut result = Vec::new();
            for mask in 0..(1usize << n) {
                let mut subset = Vec::new();
                for (i, elem) in input_set.iter().enumerate() {
                    if mask & (1 << i) != 0 {
                        subset.push(elem.clone());
                    }
                }
                // subset is already sorted (input_set is sorted, we iterate in order)
                Value::set_insert(&mut result, Value::set(Arc::new(subset)));
            }
            Ok(Value::set(Arc::new(result)))
        }
    }
}

/// Fast path for evaluating boolean expressions.
/// Avoids wrapping intermediate results in Value for common patterns.
pub fn eval_bool(expr: &CompiledExpr, ctx: &mut EvalContext) -> EvalResult<bool> {
    match expr {
        CompiledExpr::Bool(b) => Ok(*b),

        CompiledExpr::Binary { op, left, right } => match op {
            BinOp::And => {
                if !eval_bool(left, ctx)? {
                    return Ok(false);
                }
                eval_bool(right, ctx)
            }
            BinOp::Or => {
                if eval_bool(left, ctx)? {
                    return Ok(true);
                }
                eval_bool(right, ctx)
            }
            BinOp::Implies => {
                if !eval_bool(left, ctx)? {
                    return Ok(true);
                }
                eval_bool(right, ctx)
            }
            BinOp::Iff => Ok(eval_bool(left, ctx)? == eval_bool(right, ctx)?),
            BinOp::Eq => {
                // Fast path: if either side is statically Int, use eval_int
                if is_int_expr(left) || is_int_expr(right) {
                    Ok(eval_int(left, ctx)? == eval_int(right, ctx)?)
                } else {
                    Ok(eval(left, ctx)? == eval(right, ctx)?)
                }
            }
            BinOp::Ne => {
                // Fast path: if either side is statically Int, use eval_int
                if is_int_expr(left) || is_int_expr(right) {
                    Ok(eval_int(left, ctx)? != eval_int(right, ctx)?)
                } else {
                    Ok(eval(left, ctx)? != eval(right, ctx)?)
                }
            }
            BinOp::Lt => Ok(eval_int(left, ctx)? < eval_int(right, ctx)?),
            BinOp::Le => Ok(eval_int(left, ctx)? <= eval_int(right, ctx)?),
            BinOp::Gt => Ok(eval_int(left, ctx)? > eval_int(right, ctx)?),
            BinOp::Ge => Ok(eval_int(left, ctx)? >= eval_int(right, ctx)?),
            BinOp::In => {
                let left_val = eval(left, ctx)?;
                let right_val = eval(right, ctx)?;
                match right_val.kind() {
                    VK::Set(s) => Ok(Value::set_contains(s, &left_val)),
                    VK::Fn(f) => Ok(Value::fn_get(f, &left_val).is_some()),
                    _ => Err(type_mismatch("Set or Dict", &right_val)),
                }
            }
            BinOp::NotIn => {
                let left_val = eval(left, ctx)?;
                let right_val = eval(right, ctx)?;
                match right_val.kind() {
                    VK::Set(s) => Ok(!Value::set_contains(s, &left_val)),
                    VK::Fn(f) => Ok(Value::fn_get(f, &left_val).is_none()),
                    _ => Err(type_mismatch("Set or Dict", &right_val)),
                }
            }
            BinOp::SubsetOf => {
                let left_val = eval(left, ctx)?;
                let right_val = eval(right, ctx)?;
                let a = expect_set(&left_val)?;
                let b = expect_set(&right_val)?;
                Ok(sorted_vec_is_subset(a, b))
            }
            _ => expect_bool(&eval(expr, ctx)?),
        },

        CompiledExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } => Ok(!eval_bool(operand, ctx)?),

        CompiledExpr::Forall { domain, body } => {
            if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                let lo_val = expect_int(&eval(lo, ctx)?)?;
                let hi_val = expect_int(&eval(hi, ctx)?)?;
                for i in lo_val..=hi_val {
                    ctx.push_local(Value::int(i));
                    let result = eval_bool(body, ctx)?;
                    ctx.pop_local();
                    if !result {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }

            // Fast path: Forall over Powerset -- iterate bitmasks without
            // materializing all 2^n subsets upfront
            if let CompiledExpr::Powerset(inner_domain) = domain.as_ref() {
                return forall_over_powerset_bool(inner_domain, body, ctx);
            }

            let domain_val = eval(domain, ctx)?;
            let domain_elems = extract_domain_elements(&domain_val)?;
            for item in &domain_elems {
                ctx.push_local(item.clone());
                let result = eval_bool(body, ctx)?;
                ctx.pop_local();
                if !result {
                    return Ok(false);
                }
            }
            Ok(true)
        }

        CompiledExpr::Exists { domain, body } => {
            if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                let lo_val = expect_int(&eval(lo, ctx)?)?;
                let hi_val = expect_int(&eval(hi, ctx)?)?;
                for i in lo_val..=hi_val {
                    ctx.push_local(Value::int(i));
                    let result = eval_bool(body, ctx)?;
                    ctx.pop_local();
                    if result {
                        return Ok(true);
                    }
                }
                return Ok(false);
            }

            // Fast path: Exists over Powerset -- iterate bitmasks without
            // materializing all 2^n subsets upfront
            if let CompiledExpr::Powerset(inner_domain) = domain.as_ref() {
                return exists_over_powerset_bool(inner_domain, body, ctx);
            }

            let domain_val = eval(domain, ctx)?;
            let domain_elems = extract_domain_elements(&domain_val)?;
            for item in &domain_elems {
                ctx.push_local(item.clone());
                let result = eval_bool(body, ctx)?;
                ctx.pop_local();
                if result {
                    return Ok(true);
                }
            }
            Ok(false)
        }

        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            if eval_bool(cond, ctx)? {
                eval_bool(then_branch, ctx)
            } else {
                eval_bool(else_branch, ctx)
            }
        }

        CompiledExpr::Let { value, body } => {
            let val = eval(value, ctx)?;
            ctx.push_local(val);
            let result = eval_bool(body, ctx)?;
            ctx.pop_local();
            Ok(result)
        }

        _ => expect_bool(&eval(expr, ctx)?),
    }
}

/// Fast path for evaluating integer expressions.
/// Avoids wrapping intermediate results in Value for common patterns.
pub fn eval_int(expr: &CompiledExpr, ctx: &mut EvalContext) -> EvalResult<i64> {
    match expr {
        CompiledExpr::Int(n) => Ok(*n),

        CompiledExpr::Var(idx) => match ctx.vars.get(*idx) {
            Some(v) => v.as_int().ok_or_else(|| type_mismatch("Int", v)),
            None => Err(EvalError::UndefinedVariable(*idx)),
        },

        CompiledExpr::Const(idx) => match ctx.consts.get(*idx) {
            Some(v) => v.as_int().ok_or_else(|| type_mismatch("Int", v)),
            None => Err(EvalError::UndefinedConstant(*idx)),
        },

        CompiledExpr::Local(idx) => match ctx.get_local(*idx) {
            Some(v) => v.as_int().ok_or_else(|| type_mismatch("Int", v)),
            None => Err(EvalError::Internal(format!("local {} not found", idx))),
        },

        CompiledExpr::Param(idx) => match ctx.params.get(*idx) {
            Some(v) => v.as_int().ok_or_else(|| type_mismatch("Int", v)),
            None => Err(EvalError::Internal(format!("param {} not found", idx))),
        },

        CompiledExpr::Binary { op, left, right } => match op {
            BinOp::Add => Ok(eval_int(left, ctx)? + eval_int(right, ctx)?),
            BinOp::Sub => Ok(eval_int(left, ctx)? - eval_int(right, ctx)?),
            BinOp::Mul => Ok(eval_int(left, ctx)? * eval_int(right, ctx)?),
            BinOp::Div => {
                let a = eval_int(left, ctx)?;
                let b = eval_int(right, ctx)?;
                if b == 0 {
                    return Err(EvalError::DivisionByZero);
                }
                Ok(a / b)
            }
            BinOp::Mod => {
                let a = eval_int(left, ctx)?;
                let b = eval_int(right, ctx)?;
                if b == 0 {
                    return Err(EvalError::DivisionByZero);
                }
                Ok(a % b)
            }
            _ => expect_int(&eval(expr, ctx)?),
        },

        CompiledExpr::Index { base, index } => {
            let base_val = eval(base, ctx)?;
            let index_val = eval(index, ctx)?;
            match base_val.kind() {
                VK::IntMap(arr) => {
                    let k = expect_int(&index_val)? as usize;
                    arr[k].as_int().ok_or_else(|| type_mismatch("Int", &arr[k]))
                }
                VK::Fn(map) => match Value::fn_get(map, &index_val) {
                    Some(v) => v.as_int().ok_or_else(|| type_mismatch("Int", v)),
                    None => Err(EvalError::KeyNotFound(index_val.to_string())),
                },
                VK::Seq(seq) => {
                    let idx = expect_int(&index_val)?;
                    match seq.get(idx as usize) {
                        Some(v) => v.as_int().ok_or_else(|| type_mismatch("Int", v)),
                        None => Err(EvalError::IndexOutOfBounds {
                            index: idx,
                            length: seq.len(),
                        }),
                    }
                }
                _ => expect_int(&eval(expr, ctx)?),
            }
        }

        CompiledExpr::Len(inner) => {
            // Fast path: len({x in D if pred}) -> count without materializing set
            if let CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } = inner.as_ref()
            {
                if matches!(element.as_ref(), CompiledExpr::Local(0)) {
                    if let Some(filter) = filter {
                        return count_filtered(domain, filter, ctx);
                    }
                }
            }
            let val = eval(inner, ctx)?;
            match val.kind() {
                VK::Set(s) => Ok(s.len() as i64),
                VK::Seq(s) => Ok(s.len() as i64),
                VK::Fn(f) => Ok(f.len() as i64),
                VK::IntMap(arr) => Ok(arr.len() as i64),
                _ => Err(type_mismatch("Set, Seq, or Fn", &val)),
            }
        }

        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            if eval_bool(cond, ctx)? {
                eval_int(then_branch, ctx)
            } else {
                eval_int(else_branch, ctx)
            }
        }

        CompiledExpr::Let { value, body } => {
            let val = eval(value, ctx)?;
            ctx.push_local(val);
            let result = eval_int(body, ctx)?;
            ctx.pop_local();
            Ok(result)
        }

        _ => expect_int(&eval(expr, ctx)?),
    }
}

/// Check if an expression is statically known to produce an Int.
#[inline]
fn is_int_expr(expr: &CompiledExpr) -> bool {
    matches!(
        expr,
        CompiledExpr::Int(_)
            | CompiledExpr::Len(_)
            | CompiledExpr::Binary {
                op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod,
                ..
            }
    )
}

/// Exists over powerset: iterate bitmasks without materializing all 2^n subsets.
fn exists_over_powerset_bool(
    domain_expr: &CompiledExpr,
    body: &CompiledExpr,
    ctx: &mut EvalContext,
) -> EvalResult<bool> {
    let base = eval_set_domain(domain_expr, ctx)?;
    let n = base.len();
    let mut subset_buf = Vec::with_capacity(n);
    for mask in 0..(1usize << n) {
        subset_buf.clear();
        for (i, elem) in base.iter().enumerate() {
            if mask & (1 << i) != 0 {
                subset_buf.push(elem.clone());
            }
        }
        ctx.push_local(Value::set(Arc::new(subset_buf.clone())));
        let result = eval_bool(body, ctx)?;
        ctx.pop_local();
        if result {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Forall over powerset: iterate bitmasks without materializing all 2^n subsets.
fn forall_over_powerset_bool(
    domain_expr: &CompiledExpr,
    body: &CompiledExpr,
    ctx: &mut EvalContext,
) -> EvalResult<bool> {
    let base = eval_set_domain(domain_expr, ctx)?;
    let n = base.len();
    let mut subset_buf = Vec::with_capacity(n);
    for mask in 0..(1usize << n) {
        subset_buf.clear();
        for (i, elem) in base.iter().enumerate() {
            if mask & (1 << i) != 0 {
                subset_buf.push(elem.clone());
            }
        }
        ctx.push_local(Value::set(Arc::new(subset_buf.clone())));
        let result = eval_bool(body, ctx)?;
        ctx.pop_local();
        if !result {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Evaluate a domain expression and return the elements as a Vec.
/// Handles Range fast path and general set expressions.
fn eval_set_domain(domain_expr: &CompiledExpr, ctx: &mut EvalContext) -> EvalResult<Vec<Value>> {
    if let CompiledExpr::Range { lo, hi } = domain_expr {
        let lo_val = expect_int(&eval(lo, ctx)?)?;
        let hi_val = expect_int(&eval(hi, ctx)?)?;
        return Ok((lo_val..=hi_val).map(Value::int).collect());
    }
    let domain_val = eval(domain_expr, ctx)?;
    extract_domain_elements(&domain_val)
}

/// Count items in a domain that satisfy a filter, without materializing a Set.
/// Used as fast path for `len({x in D if pred})`.
fn count_filtered(
    domain: &CompiledExpr,
    filter: &CompiledExpr,
    ctx: &mut EvalContext,
) -> EvalResult<i64> {
    let mut count = 0i64;
    if let CompiledExpr::Range { lo, hi } = domain {
        let lo_val = expect_int(&eval(lo, ctx)?)?;
        let hi_val = expect_int(&eval(hi, ctx)?)?;
        for i in lo_val..=hi_val {
            ctx.push_local(Value::int(i));
            if eval_bool(filter, ctx)? {
                count += 1;
            }
            ctx.pop_local();
        }
    } else {
        let domain_val = eval(domain, ctx)?;
        let domain_elems = extract_domain_elements(&domain_val)?;
        for item in &domain_elems {
            ctx.push_local(item.clone());
            if eval_bool(filter, ctx)? {
                count += 1;
            }
            ctx.pop_local();
        }
    }
    Ok(count)
}

fn eval_binary(
    op: BinOp,
    left: &CompiledExpr,
    right: &CompiledExpr,
    ctx: &mut EvalContext,
) -> EvalResult<Value> {
    // Short-circuit evaluation for logical operators
    match op {
        BinOp::And => {
            let left_val = expect_bool(&eval(left, ctx)?)?;
            if !left_val {
                return Ok(Value::bool(false));
            }
            return Ok(Value::bool(expect_bool(&eval(right, ctx)?)?));
        }
        BinOp::Or => {
            let left_val = expect_bool(&eval(left, ctx)?)?;
            if left_val {
                return Ok(Value::bool(true));
            }
            return Ok(Value::bool(expect_bool(&eval(right, ctx)?)?));
        }
        BinOp::Implies => {
            let left_val = expect_bool(&eval(left, ctx)?)?;
            if !left_val {
                return Ok(Value::bool(true));
            }
            return Ok(Value::bool(expect_bool(&eval(right, ctx)?)?));
        }
        _ => {}
    }

    let left_val = eval(left, ctx)?;
    let right_val = eval(right, ctx)?;

    match op {
        BinOp::And | BinOp::Or | BinOp::Implies => unreachable!("handled above"),

        BinOp::Iff => {
            let a = expect_bool(&left_val)?;
            let b = expect_bool(&right_val)?;
            Ok(Value::bool(a == b))
        }

        BinOp::Eq => Ok(Value::bool(left_val == right_val)),
        BinOp::Ne => Ok(Value::bool(left_val != right_val)),

        BinOp::Lt => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            Ok(Value::bool(a < b))
        }
        BinOp::Le => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            Ok(Value::bool(a <= b))
        }
        BinOp::Gt => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            Ok(Value::bool(a > b))
        }
        BinOp::Ge => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            Ok(Value::bool(a >= b))
        }

        BinOp::Add => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            Ok(Value::int(a + b))
        }
        BinOp::Sub => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            Ok(Value::int(a - b))
        }
        BinOp::Mul => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            Ok(Value::int(a * b))
        }
        BinOp::Div => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            if b == 0 {
                return Err(EvalError::DivisionByZero);
            }
            Ok(Value::int(a / b))
        }
        BinOp::Mod => {
            let a = expect_int(&left_val)?;
            let b = expect_int(&right_val)?;
            if b == 0 {
                return Err(EvalError::DivisionByZero);
            }
            Ok(Value::int(a % b))
        }

        BinOp::In => match right_val.kind() {
            VK::Set(s) => Ok(Value::bool(Value::set_contains(s, &left_val))),
            VK::Fn(f) => Ok(Value::bool(Value::fn_get(f, &left_val).is_some())),
            _ => Err(type_mismatch("Set or Dict", &right_val)),
        },
        BinOp::NotIn => match right_val.kind() {
            VK::Set(s) => Ok(Value::bool(!Value::set_contains(s, &left_val))),
            VK::Fn(f) => Ok(Value::bool(Value::fn_get(f, &left_val).is_none())),
            _ => Err(type_mismatch("Set or Dict", &right_val)),
        },

        BinOp::Union => {
            if left_val.is_set_v() && right_val.is_set_v() {
                let a = left_val.into_set_arc();
                let b = right_val.into_set_arc();
                if b.len() <= 4 {
                    // Small right side: insert into left via CoW
                    let mut result = a;
                    let inner = Arc::make_mut(&mut result);
                    for v in b.iter() {
                        Value::set_insert(inner, v.clone());
                    }
                    Ok(Value::from_set_arc(result))
                } else if a.len() <= 4 {
                    let mut result = b;
                    let inner = Arc::make_mut(&mut result);
                    for v in a.iter() {
                        Value::set_insert(inner, v.clone());
                    }
                    Ok(Value::from_set_arc(result))
                } else {
                    Ok(Value::set(Arc::new(sorted_vec_union(&a, &b))))
                }
            } else if left_val.is_intmap() && right_val.is_intmap() {
                let mut a = left_val.into_intmap_arc();
                let b = right_val.into_intmap_arc();
                // Right overrides left for IntMap union
                let arr = Arc::make_mut(&mut a);
                for (i, v) in b.iter().enumerate() {
                    if i < arr.len() {
                        arr[i] = v.clone();
                    }
                }
                Ok(Value::from_intmap_arc(a))
            } else if left_val.is_intmap() && right_val.is_fn() {
                let a = left_val.into_intmap_arc();
                let b = right_val.into_fn_arc();
                let mut fn_vec = Value::intmap_to_fn_vec(&a);
                for (key, value) in b.iter() {
                    Value::fn_insert(&mut fn_vec, key.clone(), value.clone());
                }
                Ok(Value::func(Arc::new(fn_vec)))
            } else if left_val.is_fn() && right_val.is_intmap() {
                let mut fn_a = left_val.into_fn_arc();
                let b = right_val.into_intmap_arc();
                let inner = Arc::make_mut(&mut fn_a);
                for (i, v) in b.iter().enumerate() {
                    Value::fn_insert(inner, Value::int(i as i64), v.clone());
                }
                Ok(Value::from_fn_arc(fn_a))
            } else if left_val.is_fn() && right_val.is_fn() {
                let mut a = left_val.into_fn_arc();
                let b = right_val.into_fn_arc();
                // Insert right entries into left via CoW
                let inner = Arc::make_mut(&mut a);
                for (key, value) in b.iter() {
                    Value::fn_insert(inner, key.clone(), value.clone());
                }
                Ok(Value::from_fn_arc(a))
            } else {
                let a = expect_set(&left_val)?;
                let b = expect_set(&right_val)?;
                Ok(Value::set(Arc::new(sorted_vec_union(a, b))))
            }
        }
        BinOp::Intersect => {
            let a = expect_set(&left_val)?;
            let b = expect_set(&right_val)?;
            Ok(Value::set(Arc::new(sorted_vec_intersect(a, b))))
        }
        BinOp::Diff => {
            let a = expect_set(&left_val)?;
            let b = expect_set(&right_val)?;
            Ok(Value::set(Arc::new(sorted_vec_diff(a, b))))
        }
        BinOp::SubsetOf => {
            let a = expect_set(&left_val)?;
            let b = expect_set(&right_val)?;
            Ok(Value::bool(sorted_vec_is_subset(a, b)))
        }

        BinOp::Concat => {
            if left_val.is_seq() && right_val.is_seq() {
                let mut a = left_val.into_seq_arc();
                let b = right_val.into_seq_arc();
                Arc::make_mut(&mut a).extend(b.iter().cloned());
                Ok(Value::from_seq_arc(a))
            } else if left_val.is_string() && right_val.is_string() {
                let mut a = left_val.into_string_arc();
                let b = right_val.into_string_arc();
                Arc::make_mut(&mut a).push_str(&b);
                Ok(Value::from_string_arc(a))
            } else {
                Err(EvalError::TypeMismatch {
                    expected: "Seq or String".to_string(),
                    actual: format!("{} and {}", type_name(&left_val), type_name(&right_val)),
                })
            }
        }
    }
}

fn eval_unary(op: UnaryOp, operand: &CompiledExpr, ctx: &mut EvalContext) -> EvalResult<Value> {
    let val = eval(operand, ctx)?;

    match op {
        UnaryOp::Not => {
            let b = expect_bool(&val)?;
            Ok(Value::bool(!b))
        }
        UnaryOp::Neg => {
            let n = expect_int(&val)?;
            Ok(Value::int(-n))
        }
    }
}

#[inline(always)]
pub fn expect_bool(val: &Value) -> EvalResult<bool> {
    val.as_bool().ok_or_else(|| type_mismatch("Bool", val))
}

#[inline(always)]
pub fn expect_int(val: &Value) -> EvalResult<i64> {
    val.as_int().ok_or_else(|| type_mismatch("Int", val))
}

#[inline(always)]
pub fn expect_set(val: &Value) -> EvalResult<&[Value]> {
    val.as_set().ok_or_else(|| type_mismatch("Set", val))
}

/// Extract elements for domain iteration: Set elements, Dict/Fn keys, or IntMap indices.
/// Use this for quantifier/comprehension domains where iterating over a Dict yields its keys.
fn extract_domain_elements(val: &Value) -> EvalResult<Vec<Value>> {
    match val.kind() {
        VK::Set(s) => Ok(s.to_vec()),
        VK::Fn(m) => Ok(m.iter().map(|(k, _)| k.clone()).collect()),
        VK::IntMap(arr) => Ok((0..arr.len() as i64).map(Value::int).collect()),
        _ => Err(type_mismatch("Set or Dict", val)),
    }
}

/// Merge-based union of two sorted, deduplicated Vecs.
pub(crate) fn sorted_vec_union(a: &[Value], b: &[Value]) -> Vec<Value> {
    let mut result = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Less => {
                result.push(a[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                result.push(b[j].clone());
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                result.push(a[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    while i < a.len() {
        result.push(a[i].clone());
        i += 1;
    }
    while j < b.len() {
        result.push(b[j].clone());
        j += 1;
    }
    result
}

/// Merge-based intersection of two sorted, deduplicated Vecs.
fn sorted_vec_intersect(a: &[Value], b: &[Value]) -> Vec<Value> {
    let mut result = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                result.push(a[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    result
}

/// Merge-based difference of two sorted, deduplicated Vecs.
pub(crate) fn sorted_vec_diff(a: &[Value], b: &[Value]) -> Vec<Value> {
    let mut result = Vec::with_capacity(a.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Less => {
                result.push(a[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
        }
    }
    while i < a.len() {
        result.push(a[i].clone());
        i += 1;
    }
    result
}

/// Check if sorted Vec a is a subset of sorted Vec b.
fn sorted_vec_is_subset(a: &[Value], b: &[Value]) -> bool {
    let mut j = 0;
    for item in a {
        while j < b.len() && b[j] < *item {
            j += 1;
        }
        if j >= b.len() || b[j] != *item {
            return false;
        }
        j += 1;
    }
    true
}

pub(crate) fn type_mismatch(expected: &str, actual: &Value) -> EvalError {
    EvalError::TypeMismatch {
        expected: expected.to_string(),
        actual: type_name(actual),
    }
}

fn type_name(val: &Value) -> String {
    val.type_name().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval_simple(expr: &CompiledExpr) -> EvalResult<Value> {
        let mut ctx = EvalContext::new(&[], &[], &[], &[]);
        eval(expr, &mut ctx)
    }

    #[test]
    fn test_literals() {
        assert_eq!(
            eval_simple(&CompiledExpr::Bool(true)).unwrap(),
            Value::bool(true)
        );
        assert_eq!(eval_simple(&CompiledExpr::Int(42)).unwrap(), Value::int(42));
        assert_eq!(
            eval_simple(&CompiledExpr::String("hello".to_string())).unwrap(),
            Value::string("hello".to_string())
        );
    }

    #[test]
    fn test_arithmetic() {
        let add = CompiledExpr::Binary {
            op: BinOp::Add,
            left: Box::new(CompiledExpr::Int(2)),
            right: Box::new(CompiledExpr::Int(3)),
        };
        assert_eq!(eval_simple(&add).unwrap(), Value::int(5));

        let mul = CompiledExpr::Binary {
            op: BinOp::Mul,
            left: Box::new(CompiledExpr::Int(4)),
            right: Box::new(CompiledExpr::Int(5)),
        };
        assert_eq!(eval_simple(&mul).unwrap(), Value::int(20));
    }

    #[test]
    fn test_comparison() {
        let lt = CompiledExpr::Binary {
            op: BinOp::Lt,
            left: Box::new(CompiledExpr::Int(2)),
            right: Box::new(CompiledExpr::Int(3)),
        };
        assert_eq!(eval_simple(&lt).unwrap(), Value::bool(true));

        let eq = CompiledExpr::Binary {
            op: BinOp::Eq,
            left: Box::new(CompiledExpr::Int(2)),
            right: Box::new(CompiledExpr::Int(2)),
        };
        assert_eq!(eval_simple(&eq).unwrap(), Value::bool(true));
    }

    #[test]
    fn test_logical() {
        let and = CompiledExpr::Binary {
            op: BinOp::And,
            left: Box::new(CompiledExpr::Bool(true)),
            right: Box::new(CompiledExpr::Bool(false)),
        };
        assert_eq!(eval_simple(&and).unwrap(), Value::bool(false));

        let or = CompiledExpr::Binary {
            op: BinOp::Or,
            left: Box::new(CompiledExpr::Bool(true)),
            right: Box::new(CompiledExpr::Bool(false)),
        };
        assert_eq!(eval_simple(&or).unwrap(), Value::bool(true));
    }

    #[test]
    fn test_set_operations() {
        let set1 = CompiledExpr::SetLit(vec![CompiledExpr::Int(1), CompiledExpr::Int(2)]);
        let set2 = CompiledExpr::SetLit(vec![CompiledExpr::Int(2), CompiledExpr::Int(3)]);

        let union = CompiledExpr::Binary {
            op: BinOp::Union,
            left: Box::new(set1.clone()),
            right: Box::new(set2.clone()),
        };

        let result = eval_simple(&union).unwrap();
        if let VK::Set(s) = result.kind() {
            assert_eq!(s.len(), 3);
        } else {
            panic!("expected set");
        }

        let in_op = CompiledExpr::Binary {
            op: BinOp::In,
            left: Box::new(CompiledExpr::Int(1)),
            right: Box::new(set1),
        };
        assert_eq!(eval_simple(&in_op).unwrap(), Value::bool(true));
    }

    #[test]
    fn test_forall() {
        let domain = CompiledExpr::Range {
            lo: Box::new(CompiledExpr::Int(1)),
            hi: Box::new(CompiledExpr::Int(5)),
        };

        // forall x in 1..5: x > 0
        let forall = CompiledExpr::Forall {
            domain: Box::new(domain.clone()),
            body: Box::new(CompiledExpr::Binary {
                op: BinOp::Gt,
                left: Box::new(CompiledExpr::Local(0)),
                right: Box::new(CompiledExpr::Int(0)),
            }),
        };
        assert_eq!(eval_simple(&forall).unwrap(), Value::bool(true));

        // forall x in 1..5: x > 3
        let forall2 = CompiledExpr::Forall {
            domain: Box::new(domain),
            body: Box::new(CompiledExpr::Binary {
                op: BinOp::Gt,
                left: Box::new(CompiledExpr::Local(0)),
                right: Box::new(CompiledExpr::Int(3)),
            }),
        };
        assert_eq!(eval_simple(&forall2).unwrap(), Value::bool(false));
    }

    #[test]
    fn test_exists() {
        let domain = CompiledExpr::Range {
            lo: Box::new(CompiledExpr::Int(1)),
            hi: Box::new(CompiledExpr::Int(5)),
        };

        // exists x in 1..5: x == 3
        let exists = CompiledExpr::Exists {
            domain: Box::new(domain),
            body: Box::new(CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::Local(0)),
                right: Box::new(CompiledExpr::Int(3)),
            }),
        };
        assert_eq!(eval_simple(&exists).unwrap(), Value::bool(true));
    }

    #[test]
    fn test_let() {
        // let x = 5 in x + 3
        let expr = CompiledExpr::Let {
            value: Box::new(CompiledExpr::Int(5)),
            body: Box::new(CompiledExpr::Binary {
                op: BinOp::Add,
                left: Box::new(CompiledExpr::Local(0)),
                right: Box::new(CompiledExpr::Int(3)),
            }),
        };
        assert_eq!(eval_simple(&expr).unwrap(), Value::int(8));
    }

    #[test]
    fn test_if() {
        let if_true = CompiledExpr::If {
            cond: Box::new(CompiledExpr::Bool(true)),
            then_branch: Box::new(CompiledExpr::Int(1)),
            else_branch: Box::new(CompiledExpr::Int(2)),
        };
        assert_eq!(eval_simple(&if_true).unwrap(), Value::int(1));

        let if_false = CompiledExpr::If {
            cond: Box::new(CompiledExpr::Bool(false)),
            then_branch: Box::new(CompiledExpr::Int(1)),
            else_branch: Box::new(CompiledExpr::Int(2)),
        };
        assert_eq!(eval_simple(&if_false).unwrap(), Value::int(2));
    }

    #[test]
    fn test_state_vars() {
        let vars = vec![Value::int(10), Value::int(20)];
        let next_vars = vec![Value::int(15), Value::int(25)];
        let mut ctx = EvalContext::new(&vars, &next_vars, &[], &[]);

        // Read current state
        assert_eq!(
            eval(&CompiledExpr::Var(0), &mut ctx).unwrap(),
            Value::int(10)
        );
        assert_eq!(
            eval(&CompiledExpr::Var(1), &mut ctx).unwrap(),
            Value::int(20)
        );

        // Read next state
        assert_eq!(
            eval(&CompiledExpr::PrimedVar(0), &mut ctx).unwrap(),
            Value::int(15)
        );
        assert_eq!(
            eval(&CompiledExpr::PrimedVar(1), &mut ctx).unwrap(),
            Value::int(25)
        );
    }

    #[test]
    fn test_unchanged() {
        let vars = vec![Value::int(10), Value::int(20)];
        let next_vars = vec![Value::int(10), Value::int(25)]; // 0 unchanged, 1 changed
        let mut ctx = EvalContext::new(&vars, &next_vars, &[], &[]);

        assert_eq!(
            eval(&CompiledExpr::Unchanged(0), &mut ctx).unwrap(),
            Value::bool(true)
        );
        assert_eq!(
            eval(&CompiledExpr::Unchanged(1), &mut ctx).unwrap(),
            Value::bool(false)
        );
    }

    #[test]
    fn test_set_comprehension() {
        // {x * 2 for x in 1..3}
        let comp = CompiledExpr::SetComprehension {
            element: Box::new(CompiledExpr::Binary {
                op: BinOp::Mul,
                left: Box::new(CompiledExpr::Local(0)),
                right: Box::new(CompiledExpr::Int(2)),
            }),
            domain: Box::new(CompiledExpr::Range {
                lo: Box::new(CompiledExpr::Int(1)),
                hi: Box::new(CompiledExpr::Int(3)),
            }),
            filter: None,
        };

        let result = eval_simple(&comp).unwrap();
        if let VK::Set(s) = result.kind() {
            assert!(Value::set_contains(s, &Value::int(2)));
            assert!(Value::set_contains(s, &Value::int(4)));
            assert!(Value::set_contains(s, &Value::int(6)));
        } else {
            panic!("expected set");
        }
    }
}
