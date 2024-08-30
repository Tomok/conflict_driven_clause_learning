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

#[derive(Clone, Debug)]
pub struct Clause<V> {
    literals: Vec<Literal<V>>,
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

impl<V> Eq for Clause<V> where V: PartialEq + Eq {}

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
