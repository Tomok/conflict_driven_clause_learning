use super::Literal;

pub struct ConjunctiveNormalForm<V> {
    clauses: Vec<Clause<V>>,
}

impl<V> super::ConjunctiveNormalForm<V, Clause<V>> for ConjunctiveNormalForm<V>
where
    V: Eq + Clone + std::hash::Hash,
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
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Clause<V> {
    literals: Vec<Literal<V>>,
}

impl<V> super::Clause<V> for Clause<V>
where
    V: PartialEq + Eq + Clone + std::hash::Hash,
{
    fn new(literals: &[Literal<V>]) -> Self {
        Self {
            literals: literals.to_vec(),
        }
    }

    fn literals<'s>(&'s self) -> impl ExactSizeIterator<Item = &'s Literal<V>>
    where
        V: 's,
    {
        self.literals.iter()
    }
}
