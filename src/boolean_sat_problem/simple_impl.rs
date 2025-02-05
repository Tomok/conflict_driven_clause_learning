use std::{fmt::Display, hash::Hash};

use super::Literal;

pub struct ConjunctiveNormalForm<V> {
    clauses: Vec<Clause<V>>,
}

impl<V> super::ConjunctiveNormalForm<V, Clause<V>> for ConjunctiveNormalForm<V>
where
    V: Clone,
{
    fn new(clauses: &[Clause<V>]) -> Self {
        Self {
            clauses: clauses.to_vec(),
        }
    }

    fn clauses<'s>(&'s self) -> impl Iterator<Item = &'s Clause<V>>
    where
        V: 's,
    {
        self.clauses.iter()
    }

    fn add_clause(&mut self, clause: Clause<V>) {
        self.clauses.push(clause);
    }

    fn add_clauses(&mut self, clauses: impl IntoIterator<Item = Clause<V>>) {
        // this should be more efficient than the default implementation in the trait,
        // as [Vec::extend] can check [Iter::size_hint] to resize before adding elements
        // and as such avoid multiple reallocations
        self.clauses.extend(clauses);
    }
}

impl<V> Display for ConjunctiveNormalForm<V>
where
    V: Eq + Clone + std::hash::Hash + Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        super::ConjunctiveNormalForm::fmt_unicode(self, f)
    }
}

#[derive(Clone, Debug)]
pub struct Clause<V> {
    literals: Vec<Literal<V>>,
}

impl<V> Display for Clause<V>
where
    V: Display + Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        super::Clause::fmt_unicode(self, f)
    }
}

impl<V> PartialEq for Clause<V>
where
    V: PartialEq + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.literals.len() != other.literals.len() {
            return false;
        }
        for literal in &self.literals {
            if !other.literals.contains(literal) {
                return false;
            }
        }
        true
    }
}

impl<V> Hash for Clause<V>
where
    V: Hash + PartialOrd + Ord,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // sort the literals before hashing to avoid the order being relevant
        // there might be better way to do this
        let mut literals = self.literals.iter().collect::<Vec<_>>();
        literals.sort();
        literals.hash(state);
    }
}

impl<V> Eq for Clause<V> where V: PartialEq + Eq {}

impl<V> super::Clause<V> for Clause<V>
where
    V: Clone,
{
    fn new(literals: &[Literal<V>]) -> Self {
        Self {
            literals: literals.to_vec(),
        }
    }

    fn literals<'s>(&'s self) -> impl Iterator<Item = &'s Literal<V>>
    where
        V: 's,
    {
        self.literals.iter()
    }
}
