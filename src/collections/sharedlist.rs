/*!
 * Linked list with reference-counted tail.
 *
 * Sharing the tail of the list means that more elements can be added
 * to it without invalidating previous references to the old list.
 */

use std::iter::FromIterator;
use std::rc::Rc;

/// A linked list with a shareable tail.
#[derive(Debug, Eq, PartialEq)]
pub enum SharedList<T> {
    Nil,
    Cons(Rc<T>, Rc<SharedList<T>>),
}

impl<T> SharedList<T> {
    /// Constructs a new empty list.
    pub fn nil() -> SharedList<T> {
        SharedList::<T>::Nil
    }

    /// Constructs a new list with one more element.
    ///
    /// The old list was not mutated in any way and it's still
    /// accessible. When this new list is dropped, the old one will
    /// remain as long as there are remaining references to it.
    pub fn cons(&self, t: T) -> SharedList<T> {
        SharedList::<T>::Cons(Rc::new(t), Rc::new(self.clone()))
    }

    pub fn extend<I: IntoIterator<Item = T>>(&self, iter: I) -> Self {
        let mut res = self.clone();
        for t in iter {
            res = res.cons(t);
        }

        res
    }

    /// Returns an iterator that can produce elements of the list.
    pub fn iter(&self) -> SharedListIterator<T> {
        SharedListIterator {
            cursor: Rc::new(self.clone()),
        }
    }
}

impl<T> Clone for SharedList<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Nil => Self::Nil,
            Self::Cons(head, tail) => Self::Cons(Rc::clone(head), Rc::clone(tail)),
        }
    }
}

impl<T> Default for SharedList<T> {
    fn default() -> Self {
        Self::nil()
    }
}

/// Iterator over the list contents.
pub struct SharedListIterator<T> {
    cursor: Rc<SharedList<T>>,
}

impl<T> Iterator for SharedListIterator<T> {
    type Item = Rc<T>;

    // iteration over a shared list starts with the last added
    // element, LIFO-style
    fn next(&mut self) -> Option<Self::Item> {
        let cursor = std::mem::take(&mut self.cursor);
        match cursor.as_ref() {
            SharedList::<T>::Nil => None,
            SharedList::<T>::Cons(head, tail) => {
                self.cursor = Rc::clone(tail);
                Some(Rc::clone(head))
            }
        }
    }
}

impl<T> FromIterator<T> for SharedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::nil();

        for i in iter {
            list = list.cons(i);
        }

        list
    }
}
