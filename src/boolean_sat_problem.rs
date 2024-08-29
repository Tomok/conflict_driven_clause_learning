use std::collections::HashMap;

pub mod simple_impl;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SatStatus {
    Sat,
    Unsat,
    Unknown,
}

/// an AND combined list of [Clause]s
pub trait ConjunctiveNormalForm<V, C>
where
    V: PartialEq + std::hash::Hash + Eq + Clone,
    C: Clause<V>,
{
    fn new(clauses: &[C]) -> Self;
    fn clauses<'s>(&'s self) -> impl Iterator<Item = &'s C>
    where
        C: 's;

    fn evaluate(&self, known_values: &HashMap<V, bool>) -> SatStatus
    where
        V: Eq + std::hash::Hash,
    {
        for clause in self.clauses() {
            match clause.evaluate(known_values) {
                SatStatus::Unsat => return SatStatus::Unsat,
                SatStatus::Unknown => return SatStatus::Unknown,
                SatStatus::Sat => {}
            }
        }
        SatStatus::Sat
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnitClauseCheckResult<V> {
    Sat,
    Unknown,
    PropagatedUnit(Literal<V>),
}

/// an OR combined list of [Literal]s
pub trait Clause<V>
where
    V: PartialEq + Eq + std::hash::Hash + Clone,
{
    fn new(literals: &[Literal<V>]) -> Self;
    fn literals<'s>(&'s self) -> impl Iterator<Item = &'s Literal<V>>
    where
        V: 's;

    fn evaluate(&self, known_values: &HashMap<V, bool>) -> SatStatus
    where
        V: Eq + std::hash::Hash,
    {
        let mut all_literals_found = true;
        for literal in self.literals() {
            if let Some(expected) = known_values.get(literal.variable()) {
                if *expected == literal.is_plain() {
                    return SatStatus::Sat;
                }
            } else {
                all_literals_found = false;
            }
        }
        if all_literals_found {
            SatStatus::Unsat
        } else {
            SatStatus::Unknown
        }
    }

    fn unit_clause_check(&self, known_values: &HashMap<V, bool>) -> UnitClauseCheckResult<V> {
        let mut unsolved_literal = None;
        let mut potential_unsat = false;
        for literal in self.literals() {
            match known_values.get(literal.variable()) {
                None => {
                    if unsolved_literal.is_none() {
                        unsolved_literal = Some(literal);
                    } else {
                        potential_unsat = true;
                    }
                }
                Some(expected) => {
                    if *expected == literal.is_plain() {
                        return UnitClauseCheckResult::Sat;
                    }
                }
            }
        }
        if potential_unsat {
            UnitClauseCheckResult::Unknown
        } else if let Some(lit) = unsolved_literal {
            UnitClauseCheckResult::PropagatedUnit((*lit).clone())
        } else {
            UnitClauseCheckResult::Sat
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Literal<V> {
    /// the value of the variable itself
    Plain(V),
    /// the negation of the value of the variable
    Negated(V),
}

impl<V> Literal<V> {
    pub fn variable(&self) -> &V {
        match self {
            Literal::Plain(v) => v,
            Literal::Negated(v) => v,
        }
    }

    pub fn is_plain(&self) -> bool {
        match self {
            Literal::Plain(_) => true,
            Literal::Negated(_) => false,
        }
    }

    pub fn is_negated(&self) -> bool {
        match self {
            Literal::Plain(_) => false,
            Literal::Negated(_) => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clause_evaluate() {
        let clause = simple_impl::Clause::new(&[
            Literal::Plain('a'),
            Literal::Negated('b'),
            Literal::Negated('c'),
        ]);

        assert_eq!(clause.evaluate(&HashMap::new()), SatStatus::Unknown);
        assert_eq!(
            clause.evaluate(&HashMap::from([('a', true)])),
            SatStatus::Sat
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('a', false)])),
            SatStatus::Unknown
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('b', true)])),
            SatStatus::Unknown
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('b', false)])),
            SatStatus::Sat
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('c', true)])),
            SatStatus::Unknown
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('c', false)])),
            SatStatus::Sat
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('a', false), ('b', false), ('c', false)])),
            SatStatus::Sat
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('a', false), ('b', true), ('c', true)])),
            SatStatus::Unsat
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('d', true)])),
            SatStatus::Unknown
        );
        assert_eq!(
            clause.evaluate(&HashMap::from([('d', false)])),
            SatStatus::Unknown
        );
    }

    #[test]
    fn clause_unit_clause_check() {
        let clause = simple_impl::Clause::new(&[Literal::Plain('a'), Literal::Negated('b')]);

        assert_eq!(
            clause.unit_clause_check(&HashMap::new()),
            UnitClauseCheckResult::Unknown
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('a', true)])),
            UnitClauseCheckResult::Sat
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('a', false)])),
            UnitClauseCheckResult::PropagatedUnit(Literal::Negated('b'))
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('b', true)])),
            UnitClauseCheckResult::PropagatedUnit(Literal::Plain('a'))
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('b', false)])),
            UnitClauseCheckResult::Sat
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('c', true)])),
            UnitClauseCheckResult::Unknown
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('c', false)])),
            UnitClauseCheckResult::Unknown
        );
    }

    #[test]
    fn empty_clause_unit_clause_check() {
        let clause = simple_impl::Clause::new(&[]);
        assert_eq!(
            clause.unit_clause_check(&HashMap::new()),
            UnitClauseCheckResult::Sat
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('a', true)])),
            UnitClauseCheckResult::Sat
        );
        assert_eq!(
            clause.unit_clause_check(&HashMap::from([('a', false)])),
            UnitClauseCheckResult::Sat
        );
    }

    #[test]
    fn cnf_evaluate() {
        let cnf = simple_impl::ConjunctiveNormalForm::new(&[
            simple_impl::Clause::new(&[Literal::Plain('a')]),
            simple_impl::Clause::new(&[Literal::Negated('b'), Literal::Negated('c')]),
            simple_impl::Clause::new(&[Literal::Negated('c')]),
        ]);
        assert_eq!(cnf.evaluate(&HashMap::new()), SatStatus::Unknown);
        assert_eq!(
            cnf.evaluate(&HashMap::from([('a', true)])),
            SatStatus::Unknown
        );
        assert_eq!(
            cnf.evaluate(&HashMap::from([('b', false)])),
            SatStatus::Unknown
        );
        assert_eq!(
            cnf.evaluate(&HashMap::from([('a', false), ('b', true), ('c', true)])),
            SatStatus::Unsat
        );
        assert_eq!(
            cnf.evaluate(&HashMap::from([('a', true), ('b', false), ('c', false)])),
            SatStatus::Sat
        );
        assert_eq!(
            cnf.evaluate(&HashMap::from([('a', true), ('c', false)])),
            SatStatus::Sat
        );
    }
}
