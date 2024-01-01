#![cfg_attr(not(test), no_std)]
//! A leaky, concurrent, lock-free, singly-linked list. Only supports prepending items, and will
//! leak an allocation for each new element!
//!
//! This type of list can be useful for setting up a chain of objects that only need to be
//! initialized once and will live for the duration of the program.

extern crate alloc;

use alloc::boxed::Box;
use core::fmt::{self, Debug};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::sync::atomic::{AtomicPtr, Ordering};

/// A node of a [`LeakList`].
pub struct Node<T: 'static> {
    /// Note: this can't be `Option<&'static Node<T>>` because the pointee isn't valid until after
    /// the successful compare-exchange operation (which uses an `AcqRel` fence).
    next: *const Node<T>,
    val: T,
    phantom: PhantomData<&'static T>,
}

// SAFETY: the `next` field blocks the `Sync` impl, since it's of type `*const T`, but it really
// behaves more like `&'static T` which implements `Sync` iff `T: Sync`.
// Note: we could also probably implement `Send` for `Node<T>` where `T: Send + Sync`, but I don't
// think this would be helpful since users are never given access to a `Node<T>` directly.
unsafe impl<T: Sync> Sync for Node<T> {}

impl<T> Node<T> {
    /// Returns a reference to the next node, or `None` if it this is the last node.
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// let node = list.push_front(123);
    /// assert!(node.next().is_none());
    /// ```
    pub fn next(&self) -> Option<&'static Node<T>> {
        // SAFETY: all public functions only return a node once `next` is valid.
        unsafe { self.next.as_ref() }
    }

    /// Gets a reference to the value contained in this node.
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// let node = list.push_front(123);
    /// assert_eq!(*node.val(), 123);
    /// ```
    pub fn val(&self) -> &T {
        &self.val
    }
}

impl<T: Debug> Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("val", self.val())
            .field("next", &self.next())
            .finish()
    }
}

/// A leaky, concurrent, lock-free, singly-linked list.
#[derive(Default)]
pub struct LeakList<T: 'static> {
    head: AtomicPtr<Node<T>>,
    phantom: PhantomData<&'static Node<T>>,
}

impl<T: Debug> Debug for LeakList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LeakList")
            .field("head", &self.head())
            .finish()
    }
}

impl<T: Default> LeakList<T> {
    /// Creates a new, empty `LeakList<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T> LeakList<T> {
    /// Pushes a new node to the head of the list. Returns a reference to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// let node = list.push_front(123);
    /// assert_eq!(*node.val(), 123);
    /// ```
    pub fn push_front(&self, val: T) -> &'static Node<T> {
        let node_ptr = Box::into_raw(Box::new(Node {
            next: core::ptr::null(),
            val,
            phantom: PhantomData,
        }));

        loop {
            let cur_head = self.head.load(Ordering::Relaxed);

            // SAFETY: we still have unique ownership of the node for now, so this write is safe and
            // race-free.
            unsafe { (*node_ptr).next = cur_head };

            if self
                .head
                .compare_exchange_weak(cur_head, node_ptr, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                // SAFETY: the compare-exchange succeeded, so the pointee and all following nodes
                // are valid and visible to this thread.
                return unsafe { &*node_ptr };
            }
        }
    }

    /// Returns the frontmost node of the list (ie. the most-recently added node).
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// assert!(list.head().is_none());
    /// list.push_front(123);
    /// assert_eq!(list.head().map(|h| *h.val()), Some(123));
    /// ```
    pub fn head(&self) -> Option<&'static Node<T>> {
        // SAFETY: the acquire fence ensures that the pointee and all following nodes are valid and
        // visible to this thread.
        unsafe { self.head.load(Ordering::Acquire).as_ref() }
    }

    /// Returns the frontmost value of the list (ie. the most-recently added value).
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// assert_eq!(list.front(), None);
    /// list.push_front(123);
    /// assert_eq!(list.front().copied(), Some(123));
    /// ```
    pub fn front(&self) -> Option<&'static T> {
        self.head().map(|node| node.val())
    }

    /// Returns whether the list is currently empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// assert!(list.is_empty());
    /// list.push_front(123);
    /// assert!(!list.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.head().is_none()
    }

    /// Returns an iterator over the list from front to back, starting with the current head.
    ///
    /// /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// list.push_front(456);
    /// list.push_front(123);
    /// let vec: Vec<u32> = list.iter().copied().collect();
    /// assert_eq!(vec, [123, 456]);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter { node: self.head() }
    }

    // Note: future methods could include `pop_front()`, `extend()`, implementing `FromIterator`,
    // and methods that let you more directly handle `Node<T>` instances. Other features like
    // `len()` could be added as well, but this would make `Node<T>` more heavyweight.
}

/// An iterator over the items of a [`LeakList`].
#[derive(Clone, Debug)]
pub struct Iter<T: 'static> {
    node: Option<&'static Node<T>>,
}

impl<T> Iterator for Iter<T> {
    type Item = &'static T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.node?;
        self.node = node.next();
        Some(node.val())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.node.is_some() {
            (1, None)
        } else {
            (0, Some(0))
        }
    }
}

impl<T> FusedIterator for Iter<T> {}

impl<T> IntoIterator for &LeakList<T> {
    type Item = &'static T;
    type IntoIter = Iter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_threaded() {
        for _ in 0..100 {
            let list: LeakList<u32> = LeakList::new();
            let node1 = list.push_front(1);
            let node2 = list.push_front(2);
            println!("node1: {:?}", node1);
            println!("node2: {:?}", node2);

            std::thread::scope(|s| {
                s.spawn(|| {
                    let node3 = list.push_front(3);
                    println!("node3: {:?}", node3);
                });
                s.spawn(|| {
                    let node4 = list.push_front(4);
                    println!("node4: {:?}", node4);
                });
            });

            let vals: Vec<u32> = list.iter().copied().collect();
            if vals != [4, 3, 2, 1] && vals != [3, 4, 2, 1] {
                panic!(
                    "incorrect result: got {:?}, expected either [4, 3, 2, 1] or [3, 4, 2, 1]",
                    vals,
                );
            }
        }
    }
}
