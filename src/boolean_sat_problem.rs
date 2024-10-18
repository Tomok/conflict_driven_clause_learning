use std::collections::HashMap;
use std::fmt::Display;

pub mod simple_impl;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SatStatus {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, Clone, Eq)]
pub enum UnitClauseChecksResult<V, C>
where
    V: PartialEq + std::hash::Hash + Eq + Clone,
    C: Clause<V>,
{
    /// a conflict was detected, contains the learned resulting clause
    Conflict(Vec<C>),
    LiteralsDerived(Vec<Literal<V>>),
    /// it is known, that no matter the other variables set, this will never be SAT
    Unsat,
}

fn elements_equal_order_independent<T: PartialEq>(a: &[T], b: &[T]) -> bool {
    a.len() == b.len() && a.iter().all(|x| b.contains(x))
}

impl<V, C> PartialEq for UnitClauseChecksResult<V, C>
where
    V: PartialEq + std::hash::Hash + Eq + Clone,
    C: Clause<V> + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Conflict(l0), Self::Conflict(r0)) => elements_equal_order_independent(l0, r0),
            (Self::LiteralsDerived(l0), Self::LiteralsDerived(r0)) => {
                elements_equal_order_independent(l0, r0)
            }
            (Self::Unsat, Self::Unsat) => true,
            _ => false,
        }
    }
}

/// an AND combined list of [Clause]s
pub trait ConjunctiveNormalForm<V, C>
where
    V: Clone,
    C: Clause<V>,
{
    fn new(clauses: &[C]) -> Self;
    fn clauses<'s>(&'s self) -> impl Iterator<Item = &'s C>
    where
        C: 's;

    fn add_clause(&mut self, clause: C);

    ///add multiple clauses
    ///
    ///where applicable overwrite this in trait implementations for efficiency,
    ///e.g. to pre-allocate memory
    fn add_clauses(&mut self, clauses: impl IntoIterator<Item = C>) {
        for clause in clauses {
            self.add_clause(clause);
        }
    }

    fn check_sat(&mut self) -> SatStatus
    where
        V: PartialEq + Eq + std::hash::Hash,
    {
        let known_values = HashMap::new();
        self._pick_literal_and_check(&known_values)
    }

    /// picks a literal and checks the resulting sat status, if necessary for
    /// both the picked literal and its negation
    fn _pick_literal_and_check(&mut self, known_values: &HashMap<V, bool>) -> SatStatus
    where
        V: PartialEq + Eq + std::hash::Hash,
    {
        let literal = self.pick_literal(known_values);
        let Some(literal) = literal else {
            return SatStatus::Sat;
        };
        let mut new_known_values = known_values.clone();
        new_known_values.insert(literal.variable().clone(), literal.is_plain());
        match self._check_sat(&mut new_known_values) {
            SatStatus::Unsat => {
                // invert chosen literal
                let previous_literal =
                    new_known_values.insert(literal.variable().clone(), !literal.is_plain());
                debug_assert!(previous_literal.is_some());
                self._check_sat(&mut new_known_values)
            }
            sat_status => sat_status,
        }
    }

    fn _check_sat(&mut self, known_values: &mut HashMap<V, bool>) -> SatStatus
    where
        V: PartialEq + Eq + std::hash::Hash,
    {
        match self.unit_clause_checks(known_values) {
            UnitClauseChecksResult::Conflict(c) => {
                self.add_clauses(c);
                SatStatus::Unsat
            }
            UnitClauseChecksResult::LiteralsDerived(ld) => {
                for literal in ld {
                    known_values.insert(literal.variable().clone(), literal.is_plain());
                }
                self._pick_literal_and_check(known_values)
            }
            UnitClauseChecksResult::Unsat => SatStatus::Unsat,
        }
    }

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

    /// returns a [Literal] the Variable of which is not yet known to be defined
    fn pick_literal(&self, already_picked: &HashMap<V, bool>) -> Option<Literal<V>>
    where
        V: Eq + std::hash::Hash,
    {
        for clause in self.clauses() {
            for literal in clause.literals() {
                if !already_picked.contains_key(literal.variable()) {
                    // intentionally inverting the found literal here, that way there is a chance
                    // of the unit clause check deriving a value using this clause
                    return Some(literal.invert());
                }
            }
        }
        None
    }

    fn unit_clause_checks(&self, known_values: &HashMap<V, bool>) -> UnitClauseChecksResult<V, C>
    where
        V: Eq + std::hash::Hash,
    {
        let mut derived_values = HashMap::new();
        for clause in self.clauses() {
            match clause.unit_clause_check(known_values) {
                UnitClauseCheckResult::Sat | UnitClauseCheckResult::Unknown => {}
                UnitClauseCheckResult::Unsat => {
                    return UnitClauseChecksResult::Unsat;
                }
                UnitClauseCheckResult::PropagatedUnit(lit) => {
                    //TODO: should multiple clauses causing a variable state be saved?
                    // it allows to derive more than one clause if a conflict is found,
                    // but it also requires heap allocations and increases the difficulty of
                    // backtracking
                    let v = derived_values
                        .entry(lit.variable().clone())
                        .or_insert((vec![], vec![]));
                    if lit.is_plain() {
                        v.0.push(clause);
                    } else {
                        v.1.push(clause);
                    }
                    //TODO: should conflicts be deteced here(faster), or rather later, to gain more
                    //learnings?
                    if (!v.0.is_empty()) && (!v.1.is_empty()) {
                        //conflict found
                        let mut learned_clauses =
                            Vec::with_capacity(usize::max(v.0.len(), v.1.len()));
                        for clause_assuming_v_true in &v.0 {
                            for clause_assuming_v_false in &v.1 {
                                let learned_clause = C::from_conflict(
                                    lit.variable(),
                                    clause_assuming_v_true,
                                    clause_assuming_v_false,
                                );
                                // only push learned_clauses that are not empty
                                if learned_clause.literals().next().is_some() {
                                    learned_clauses.push(learned_clause);
                                }
                            }
                        }
                        return UnitClauseChecksResult::Conflict(learned_clauses);
                    }
                }
            }
        }
        UnitClauseChecksResult::LiteralsDerived(
            derived_values
                .into_iter()
                .map(|(v, (plain_clauses, negated_clauses))| {
                    debug_assert!(
                        !plain_clauses.is_empty() || !negated_clauses.is_empty(),
                        "since a variable was in the map, it should have a clause that caused it to be");
                    debug_assert!(
                        plain_clauses.is_empty() || negated_clauses.is_empty(),
                        "conflict checks were run above, yet conflict was reported here");
                    if plain_clauses.is_empty() {
                        Literal::Negated(v)
                    } else {
                        Literal::Plain(v)
                    }
                })
                .collect(),
        )
    }

    fn fmt_unicode(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    where
        V: Display,
    {
        let mut any_element_written = false;
        for clause in self.clauses() {
            if any_element_written {
                write!(f, " ∧ ")?;
            } else {
                any_element_written = true;
            }
            f.write_str("(")?;
            clause.fmt_unicode(f)?;
            f.write_str(")")?;
        }
        if !any_element_written {
            write!(f, "()")?;
        }
        Ok(())
    }

    fn fmt_unicode_multiline(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    where
        V: Display,
    {
        let mut any_element_written = false;
        for clause in self.clauses() {
            if any_element_written {
                write!(f, " ∧ ")?;
            } else {
                write!(f, "  ")?; //to achive same indentation
                any_element_written = true;
            }
            f.write_str("(")?;
            clause.fmt_unicode(f)?;
            f.write_str(")")?;
        }
        if !any_element_written {
            write!(f, "()")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnitClauseCheckResult<V> {
    Sat,
    Unknown,
    PropagatedUnit(Literal<V>),
    Unsat,
}

/// an OR combined list of [Literal]s
pub trait Clause<V> {
    fn new(literals: &[Literal<V>]) -> Self;

    ///generates a new clause from two clauses causing v to have a conflicting value
    ///the conflict is that all other [Literal]s in both clauses evaluate to false
    ///and one clause hence forcing v to be true, and the other causing v to be false
    ///WARNING: v needs to be the only conflict in these clauses,
    ///i.e. no other variable may be in both clauses with differing values,
    ///for debug builds this is asserted, for release builds this is not checked
    fn from_conflict(v: &V, clause_assuming_v_true: &Self, clause_assuming_v_false: &Self) -> Self
    where
        V: PartialEq + Eq + Clone,
        Self: Sized,
    {
        // known:  (clause_assuming_v_true ∧ clause_assuming_v_false) == false
        // with
        //   clause_assuming_v_true = t1 ∨ t2 ∨ t3 ... ∨ v
        //   clause_assuming_v_false = f1 ∨ f2 ∨ f3 ... ∨ v
        // we know, that t1 ∨ t2 ∨ ... ∨ f1 ∨ f2 ∨ ... == true
        // to resolve the conflict for v
        let mut derived_clause_literals = Vec::with_capacity(
            clause_assuming_v_true.literals().size_hint().0
                + clause_assuming_v_false.literals().size_hint().0
                - 2, /* removal of conflicting variable in each clause */
        );
        for clause in [clause_assuming_v_true, clause_assuming_v_false] {
            for literal in clause.literals() {
                if literal.variable() != v && !derived_clause_literals.contains(literal) {
                    debug_assert!(!derived_clause_literals.contains(literal));
                    derived_clause_literals.push((*literal).clone());
                }
            }
        }
        Self::new(&derived_clause_literals)
    }

    fn literals<'s>(&'s self) -> impl Iterator<Item = &'s Literal<V>>
    where
        V: 's;

    fn evaluate(&self, known_values: &HashMap<V, bool>) -> SatStatus
    where
        V: Clone + PartialEq + Eq + std::hash::Hash,
    {
        match self.unit_clause_check(known_values) {
            UnitClauseCheckResult::Sat => SatStatus::Sat,
            UnitClauseCheckResult::Unknown => SatStatus::Unknown,
            UnitClauseCheckResult::PropagatedUnit(_) => SatStatus::Unknown,
            UnitClauseCheckResult::Unsat => SatStatus::Unsat,
        }
    }

    fn unit_clause_check(&self, known_values: &HashMap<V, bool>) -> UnitClauseCheckResult<V>
    where
        V: Clone + PartialEq + Eq + std::hash::Hash, //TODO rework so that cloning is not required
    {
        let mut unsolved_literal = None;
        let mut unknown = false;
        let mut any_literal_found = false;
        for literal in self.literals() {
            any_literal_found = true;
            match known_values.get(literal.variable()) {
                None => {
                    if unsolved_literal.is_none() {
                        unsolved_literal = Some(literal);
                    } else {
                        unknown = true;
                    }
                }
                Some(expected) => {
                    if *expected == literal.is_plain() {
                        return UnitClauseCheckResult::Sat;
                    }
                }
            }
        }
        match (unknown, unsolved_literal, any_literal_found) {
            (true, _, _) => UnitClauseCheckResult::Unknown,
            (false, Some(lit), _) => UnitClauseCheckResult::PropagatedUnit((*lit).clone()),
            (false, None, true) => UnitClauseCheckResult::Unsat,
            (false, None, false) => UnitClauseCheckResult::Sat,
        }
    }

    /// pretty prints the clause using the given formatter
    ///
    /// can also be called in implementations to implement the [Display] trait
    // (a general implementation of the [Display] trait for [Clause]s is prevented by Rusts orphan
    // rules)
    fn fmt_unicode(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    where
        V: Display,
    {
        let mut any_element_written = false;
        for literal in self.literals() {
            if any_element_written {
                write!(f, " ∨ ")?;
            } else {
                any_element_written = true;
            }
            literal.fmt(f)?;
        }
        if !any_element_written {
            write!(f, "()")?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
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

    pub fn invert(&self) -> Literal<V>
    where
        V: Clone,
    {
        match self {
            Literal::Plain(v) => Literal::Negated((*v).clone()),
            Literal::Negated(v) => Literal::Plain((*v).clone()),
        }
    }
}

impl<V> Display for Literal<V>
where
    V: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_negated() {
            write!(f, "¬")?;
        }
        self.variable().fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet};

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
            clause.evaluate(&HashMap::from([('a', false), ('b', true)])),
            SatStatus::Unknown
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
    fn clause_from_conflict() {
        //two clauses, with conflict in variable 'v'
        let clause1 = simple_impl::Clause::new(&[Literal::Plain('a'), Literal::Plain('v')]);
        let clause2 = simple_impl::Clause::new(&[Literal::Negated('b'), Literal::Negated('v')]);
        let expected = simple_impl::Clause::new(&[Literal::Plain('a'), Literal::Negated('b')]);
        let result = Clause::from_conflict(&'v', &clause1, &clause2);
        assert_eq!(result, expected);
    }

    #[test]
    fn clause_from_conflict_and_overlap() {
        //two clauses, with conflict in variable 'v' and both using 'a'
        let clause1 = simple_impl::Clause::new(&[Literal::Plain('a'), Literal::Plain('v')]);
        let clause2 = simple_impl::Clause::new(&[
            Literal::Plain('a'),
            Literal::Negated('b'),
            Literal::Negated('v'),
        ]);
        let expected = simple_impl::Clause::new(&[Literal::Plain('a'), Literal::Negated('b')]);
        let result = Clause::from_conflict(&'v', &clause1, &clause2);
        assert_eq!(result, expected);
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
            cnf.evaluate(&HashMap::from([('a', false)])),
            SatStatus::Unsat
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

    #[test]
    fn cnf_pick_literal() {
        let cnf = simple_impl::ConjunctiveNormalForm::new(&[
            simple_impl::Clause::new(&[Literal::Plain('a')]),
            simple_impl::Clause::new(&[Literal::Negated('b'), Literal::Negated('c')]),
            simple_impl::Clause::new(&[Literal::Negated('c')]),
        ]);
        let mut literals_picked = HashMap::new();
        let all_vars = HashSet::from(['a', 'b', 'c']);

        loop {
            let literal = cnf.pick_literal(&literals_picked);
            let literal = match literal {
                None => break,
                Some(v) => v,
            };
            assert!(all_vars.contains(literal.variable()));
            assert!(!literals_picked.contains_key(literal.variable()));
            literals_picked.insert(*literal.variable(), literal.is_plain());
        }
        assert_eq!(
            literals_picked.len(),
            3,
            "all variables should have been picked, but only these literals wre returned {:#?}",
            literals_picked
        );
    }

    #[test]
    fn cnf_unit_clause_checks() {
        let cnf = simple_impl::ConjunctiveNormalForm::new(&[
            simple_impl::Clause::new(&[Literal::Plain('a')]),
            simple_impl::Clause::new(&[Literal::Negated('b'), Literal::Plain('c')]),
            simple_impl::Clause::new(&[Literal::Negated('c')]),
        ]);
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::new()),
            UnitClauseChecksResult::LiteralsDerived(vec![
                Literal::Plain('a'),
                Literal::Negated('c')
            ])
        );
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::from([('a', true), ('c', false)])),
            UnitClauseChecksResult::LiteralsDerived(vec![Literal::Negated('b')])
        );
    }
    #[test]
    fn cnf_unit_clause_checks_a_and_not_a() {
        let cnf = simple_impl::ConjunctiveNormalForm::new(&[
            simple_impl::Clause::new(&[Literal::Plain('a')]),
            simple_impl::Clause::new(&[Literal::Negated('a')]),
        ]);
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::new()),
            UnitClauseChecksResult::Conflict(vec![])
        );
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::from([('a', false)])),
            UnitClauseChecksResult::Unsat
        );
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::from([('a', true)])),
            UnitClauseChecksResult::Unsat
        );
    }

    #[test]
    fn cnf_unit_clause_checks_with_simple_conflict() {
        let cnf = simple_impl::ConjunctiveNormalForm::new(&[
            simple_impl::Clause::new(&[Literal::Plain('a'), Literal::Plain('b')]),
            simple_impl::Clause::new(&[Literal::Plain('a'), Literal::Negated('b')]),
        ]);
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::new()),
            UnitClauseChecksResult::LiteralsDerived(vec![])
        );
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::from([('a', false)])),
            UnitClauseChecksResult::Conflict(vec![Clause::new(&[Literal::Plain('a')])])
        );
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::from([('a', true)])),
            UnitClauseChecksResult::LiteralsDerived(vec![])
        );
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::from([('b', false)])),
            UnitClauseChecksResult::LiteralsDerived(vec![Literal::Plain('a')])
        );
        assert_eq!(
            cnf.unit_clause_checks(&HashMap::from([('b', true)])),
            UnitClauseChecksResult::LiteralsDerived(vec![Literal::Plain('a')])
        );
    }

    #[test]
    fn cnf_check_sat_a() {
        let clauses = [simple_impl::Clause::new(&[Literal::Plain('a')])];
        let mut cnf = simple_impl::ConjunctiveNormalForm::new(&clauses);
        assert_eq!(cnf.check_sat(), SatStatus::Sat);
        let clauses_after_check = cnf.clauses().collect::<Vec<_>>();
        assert_eq!(clauses_after_check.len(), 1);
        assert_eq!(clauses_after_check[0], &clauses[0]);
    }

    #[test]
    fn cnf_check_sat_empty() {
        let clauses: [simple_impl::Clause<char>; 0] = [];
        let mut cnf = simple_impl::ConjunctiveNormalForm::new(&clauses);
        assert_eq!(cnf.check_sat(), SatStatus::Sat);
        let clauses_after_check = cnf.clauses().collect::<Vec<_>>();
        assert_eq!(clauses_after_check.len(), 0);
    }

    #[test]
    fn cnf_check_sat_not_a() {
        let clauses = [simple_impl::Clause::new(&[Literal::Negated('a')])];
        let mut cnf = simple_impl::ConjunctiveNormalForm::new(&clauses);
        assert_eq!(cnf.check_sat(), SatStatus::Sat);
        let clauses_after_check = cnf.clauses().collect::<Vec<_>>();
        assert_eq!(clauses_after_check.len(), 1);
        assert_eq!(clauses_after_check[0], &clauses[0]);
    }

    #[test]
    fn cnf_check_sat_a_and_not_a() {
        let clauses = [
            simple_impl::Clause::new(&[Literal::Plain('a')]),
            simple_impl::Clause::new(&[Literal::Negated('a')]),
        ];
        let mut cnf = simple_impl::ConjunctiveNormalForm::new(&clauses);
        assert_eq!(cnf.check_sat(), SatStatus::Unsat);
        let clauses_after_check = cnf.clauses().collect::<Vec<_>>();
        assert_eq!(clauses_after_check.len(), 2);
        assert_eq!(clauses_after_check[0], &clauses[0]);
        assert_eq!(clauses_after_check[1], &clauses[1]);
    }
}
