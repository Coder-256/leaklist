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
use core::ptr::NonNull;
use core::sync::atomic::{AtomicPtr, Ordering};

/// A node of a [`LeakList`].
pub struct Node<T> {
    val: T,
    /// Note: this can't be `Option<&'a Node<T>>` because the pointee isn't valid until after
    /// the successful compare-exchange operation (which uses an `AcqRel` fence to synchronize with
    /// other calls to `push_front`).
    next: Option<NonNull<Node<T>>>,
}

// SAFETY: the `next` pointer blocks the `Sync` impl, since it's of type `*mut T`, but it really
// behaves more like `&'a T` which implements `Sync` iff `T: Sync`.
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
    pub fn next(&self) -> Option<&Node<T>> {
        // SAFETY: public functions only return a node once `next` is valid.
        unsafe { self.next.map(|p| p.as_ref()) }
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
    /// assert_eq!(*node.get(), 123);
    /// ```
    pub fn get(&self) -> &T {
        &self.val
    }
}

impl<T: Debug> Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("val", self.get())
            .field("next", &self.next())
            .finish()
    }
}

/// A leaky, concurrent, lock-free, singly-linked list.
pub struct LeakList<T> {
    head: AtomicPtr<Node<T>>,
    phantom: PhantomData<Box<Node<T>>>,
}

unsafe impl<T: Send> Send for LeakList<T> {}
unsafe impl<T: Sync> Sync for LeakList<T> {}

impl<T: Debug> Debug for LeakList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LeakList")
            .field("head", &self.head())
            .finish()
    }
}

impl<T> Default for LeakList<T> {
    fn default() -> Self {
        Self {
            head: AtomicPtr::default(),
            phantom: PhantomData,
        }
    }
}

impl<T> LeakList<T> {
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

    /// Pushes a new node to the head of the list. Returns a reference to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let list: LeakList<u32> = LeakList::new();
    /// let node = list.push_front(123);
    /// assert_eq!(*node.get(), 123);
    /// ```
    pub fn push_front(&self, val: T) -> &Node<T> {
        let node_ptr = Box::into_raw(Box::new(Node { next: None, val }));

        loop {
            let cur_head = self.head.load(Ordering::Relaxed);

            // SAFETY: we still have unique ownership of the node for now, so this write is safe and
            // race-free.
            unsafe { (*node_ptr).next = NonNull::new(cur_head) };

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
    /// assert_eq!(list.head().map(|h| *h.get()), Some(123));
    /// ```
    pub fn head(&self) -> Option<&Node<T>> {
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
    pub fn front(&self) -> Option<&T> {
        self.head().map(|node| node.get())
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
    /// # Examples
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

    /// Removes and returns the frontmost element of the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use leaklist::LeakList;
    ///
    /// let mut list: LeakList<u32> = LeakList::new();
    /// assert_eq!(list.pop_front(), None);
    /// list.push_front(456);
    /// list.push_front(123);
    /// assert_eq!(list.pop_front(), Some(123));
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        let head = *self.head.get_mut();
        if head.is_null() {
            return None;
        }
        // SAFETY: the head pointer is valid if it is non-null, and we replace it with `head.next`
        // so the inner value cannot be used again.
        let head_box = unsafe { Box::from_raw(head) };
        *self.head.get_mut() = head_box.next.map_or(core::ptr::null_mut(), |p| p.as_ptr());
        Some(head_box.val)
    }

    // Note: future methods could include `extend()` and cursor-like methods that let you more
    // directly handle `Node<T>` instances. Other features like `len()` could be added as well, but
    // this would make list operations more heavyweight.
}

impl<T> Drop for LeakList<T> {
    fn drop(&mut self) {
        let mut into_iter = IntoIter {
            node: NonNull::new(*self.head.get_mut()),
            phantom: PhantomData,
        };
        while into_iter.next().is_some() {}
    }
}

/// An iterator over the items of a [`LeakList`].
#[derive(Clone, Debug)]
pub struct Iter<'a, T> {
    node: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.node?;
        self.node = node.next();
        Some(node.get())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.node.is_some() {
            (1, None)
        } else {
            (0, Some(0))
        }
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

impl<'a, T> IntoIterator for &'a LeakList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator that moves out of the items of a [`LeakList`].
#[derive(Debug)]
pub struct IntoIter<T> {
    node: Option<NonNull<Node<T>>>,
    phantom: PhantomData<Box<Node<T>>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: we have unique access to the node
        let Node { val, next } = unsafe { *Box::from_raw(self.node?.as_ptr()) };
        self.node = next;
        Some(val)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.node.is_some() {
            (1, None)
        } else {
            (0, Some(0))
        }
    }
}

impl<T> FusedIterator for IntoIter<T> {}

impl<T> IntoIterator for LeakList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(mut self) -> Self::IntoIter {
        IntoIter {
            node: NonNull::new(core::mem::replace(
                self.head.get_mut(),
                core::ptr::null_mut(),
            )),
            phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_threaded() {
        for _ in 0..100 {
            let mut list: LeakList<u32> = LeakList::new();
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

            let removed = list.pop_front();
            println!("removed: {:?}", removed);
            assert!(removed == Some(3) || removed == Some(4));

            let vals: Vec<u32> = list.iter().copied().collect();
            if vals != [3, 2, 1] && vals != [4, 2, 1] {
                panic!(
                    "incorrect result: got {:?}, expected either [3, 2, 1] or [4, 2, 1]",
                    vals,
                );
            }
        }
    }

    #[test]
    fn test_threaded_many() {
        let list: LeakList<u32> = LeakList::new();

        std::thread::scope(|s| {
            let list_ref = &list;
            for i in 1..=1000 {
                s.spawn(move || list_ref.push_front(i));
            }
        });

        println!("list: {:?}", list.iter().copied().collect::<Vec<u32>>());
    }
}
