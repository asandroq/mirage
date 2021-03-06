/*!
 * Linked list with reference-counted tail.
 *
 * Sharing the tail of the list means that more elements can be added
 * to it without invalidating previous references to the old list.
 */

use std::iter::FromIterator;
use std::rc::Rc;

/// Private type for the actual shared list implementation.
///
/// By hiding this private type we ensure that the list is always
/// accessed via the reference-counted type.
enum SharedListP<T> {
    Nil,
    Cons(T, SharedList<T>)
}

/// A linked list with a shareable tail.
pub struct SharedList<T>(Rc<SharedListP<T>>);

impl<T> SharedList<T> {
    /// Constructs a new empty list.
    pub fn nil() -> SharedList<T> {
	SharedList(Rc::new(SharedListP::<T>::Nil))
    }

    /// Constructs a new list with one more element.
    ///
    /// The old list was not mutated in any way and it's still
    /// accessible. When this new list is dropped, the old one will
    /// remain as long as there are remaining references to it.
    pub fn cons(&self, t: T) -> SharedList<T> {
	SharedList(
            Rc::new(
                SharedListP::<T>::Cons(
                    t,
                    SharedList(self.0.clone())
                )
            )
        )
    }

    /// Returns an iterator that can produce elements of the list.
    pub fn iter(&self) -> SharedListIterator<T> {
        SharedListIterator { cursor: SharedList(self.0.clone()) }
    }
}

pub struct SharedListIterator<T> {
    cursor: SharedList<T>,
}

impl<T: Clone> Iterator for SharedListIterator<T> {

    type Item = T;

    // iteration over a shared list starts with the last added
    // element, LIFO-style
    fn next(&mut self) -> Option<T> {
        let inner = std::mem::replace(&mut self.cursor, SharedList::<T>::nil());
        match inner.0.as_ref() {
            SharedListP::<T>::Nil => None,
            SharedListP::<T>::Cons(head, tail) => {
                self.cursor = SharedList(tail.0.clone());
                Some(head.clone())
            }
        }
    }
}

impl<T> FromIterator<T> for SharedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::nil();

        for i in iter {
            list = list.cons(i)
        }

        list
    }
}
