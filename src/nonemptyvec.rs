/*!
 * A collection that is guaranteed to be non-empty.
 */

/// A collection that is guaranteed to never be empty.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NonEmptyVec<T> {
    elem: Box<T>,
    rest: Vec<T>,
}

impl<T> NonEmptyVec<T> {
    /// The current length of the collection.
    pub fn len(&self) -> usize {
        self.rest.len() + 1
    }

    /// Creates a new collection with a single element.
    pub fn new(elem: T) -> NonEmptyVec<T> {
        NonEmptyVec {
            elem: Box::new(elem),
            rest: Vec::new(),
        }
    }

    /// Adds another element to the collection.
    pub fn push(&mut self, elem: T) {
        self.rest.push(elem)
    }

    /// Iterator over references.
    pub fn iter(&self) -> Iter<T> {
        self.into_iter()
    }

    /// Consumes the collection and returns the first and remaining parts separately.
    pub fn into_parts(self) -> (T, std::vec::IntoIter<T>) {
        (*self.elem, self.rest.into_iter())
    }

    /// Access the first and remaining parts separately.
    pub fn parts(&self) -> (&T, std::slice::Iter<T>) {
        (&self.elem, self.rest.iter())
    }

    /// Transforms elements using a given function and return a new
    /// collection.
    pub fn map<U, F: Fn(&T) -> U>(&self, f: F) -> NonEmptyVec<U> {
        let (e, es) = self.parts();
        let mut res = NonEmptyVec::new(f(e));
        res.extend(es.map(f));

        res
    }

    /// Zips two collections, creating a third one whose elements are
    /// pairs created element-wise.
    pub fn zip<U>(self, other: NonEmptyVec<U>) -> NonEmptyVec<(T, U)> {
        let (t, ts) = self.into_parts();
        let (u, us) = other.into_parts();
        let mut res = NonEmptyVec::new((t, u));
        res.extend(ts.zip(us));

        res
    }

    /// Convers this collection into a standard vector.
    pub fn to_vec(self) -> Vec<T> {
        let mut res = vec![*self.elem];
        res.extend(self.rest.into_iter());

        res
    }
}

impl<T> IntoIterator for NonEmptyVec<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.to_vec().into_iter()
    }
}

enum IterState {
    Elem,
    Rest,
}

/// Iterator over the elements of the non-empty collection.
pub struct Iter<'a, T: 'a> {
    state: IterState,
    elem: &'a T,
    rest: std::slice::Iter<'a, T>,
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match self.state {
            IterState::Elem => {
                self.state = IterState::Rest;
                Some(&self.elem)
            },
            IterState::Rest => self.rest.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, ou) = self.rest.size_hint();
        (1, ou.map(|u| u + 1))
    }
}

impl<'a, T: 'a> IntoIterator for &'a NonEmptyVec<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        Iter {
            state: IterState::Elem,
            elem: &self.elem,
            rest: self.rest.iter(),
        }
    }
}

impl<T> Extend<T> for NonEmptyVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for i in iter {
            self.push(i)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_into() {
        let mut coll = NonEmptyVec::new(3);
        coll.push(2);
        coll.push(5);
        coll.push(9);
        coll.push(1);

        let mut iter = coll.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), Some(9));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter() {
        let mut coll = NonEmptyVec::new('g');
        coll.push('a');
        coll.push('l');
        coll.push('h');
        coll.push('b');

        let mut iter = coll.iter();
        assert_eq!(iter.next(), Some(&'g'));
        assert_eq!(iter.next(), Some(&'a'));
        assert_eq!(iter.next(), Some(&'l'));
        assert_eq!(iter.next(), Some(&'h'));
        assert_eq!(iter.next(), Some(&'b'));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_extend() {
        let mut coll = NonEmptyVec::new("the");
        let other = vec!["book", "is", "on", "the", "table"];
        coll.extend(other.into_iter());

        let mut iter = coll.into_iter();
        assert_eq!(iter.next(), Some("the"));
        assert_eq!(iter.next(), Some("book"));
        assert_eq!(iter.next(), Some("is"));
        assert_eq!(iter.next(), Some("on"));
        assert_eq!(iter.next(), Some("the"));
        assert_eq!(iter.next(), Some("table"));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_map() {
        let mut coll = NonEmptyVec::new("the");
        let other = vec!["book", "is", "on", "the", "table"];
        coll.extend(other.into_iter());

        let coll_ = coll.map(|s| s.len());
        let mut iter = coll_.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_zip() {
        let mut coll1 = NonEmptyVec::new('x');
        let other1 = vec!['y', 'z', 'u', 'v', 'w'];
        coll1.extend(other1.into_iter());

        let mut coll2 = NonEmptyVec::new(9);
        let other2 = vec![0, 14, 9, 3, 16];
        coll2.extend(other2.into_iter());

        let coll_ = coll1.zip(coll2);
        let mut iter = coll_.into_iter();
        assert_eq!(iter.next(), Some(('x', 9)));
        assert_eq!(iter.next(), Some(('y', 0)));
        assert_eq!(iter.next(), Some(('z', 14)));
        assert_eq!(iter.next(), Some(('u', 9)));
        assert_eq!(iter.next(), Some(('v', 3)));
        assert_eq!(iter.next(), Some(('w', 16)));
        assert_eq!(iter.next(), None);
    }
}
