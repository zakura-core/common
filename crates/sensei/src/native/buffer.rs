//! Initialized polynomial storage leased from one proof's workspace.

use alloc::{collections::BTreeMap, sync::Arc, vec, vec::Vec};
use core::{
    fmt,
    ops::{Deref, DerefMut},
};
use std::sync::Mutex;

pub(crate) struct BufferPool<T>(Arc<Mutex<Store<T>>>);

/// Cumulative allocations, idle buffer count, and idle capacity in bytes.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BufferInventory {
    pub(super) allocations: usize,
    pub(super) buffers: usize,
    pub(super) bytes: usize,
}

struct Store<T> {
    idle: BTreeMap<usize, Vec<Vec<T>>>,
    #[cfg(test)]
    allocations: usize,
}
impl<T> Default for BufferPool<T> {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(Store {
            idle: BTreeMap::new(),
            #[cfg(test)]
            allocations: 0,
        })))
    }
}
impl<T> Clone for BufferPool<T> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}
impl<T: Clone> BufferPool<T> {
    /// Reserve initialized, idle buffers before admitting a bounded task graph.
    /// Existing leases are excluded; call between uses of the graph's pool.
    #[cfg(feature = "prover")]
    pub(crate) fn provision(&self, len: usize, count: usize, value: T) {
        if len == 0 {
            return;
        }
        let capacity = len.next_power_of_two();
        let mut store = self.0.lock().unwrap_or_else(|error| error.into_inner());
        let buffers = store.idle.entry(capacity).or_default();
        let added = count.saturating_sub(buffers.len());
        buffers.extend((0..added).map(|_| vec![value.clone(); capacity]));
        #[cfg(test)]
        {
            store.allocations += added;
        }
    }

    /// All storage is initialized, including when the caller will overwrite it.
    /// `clear` is required for sparse writes and accumulators.
    pub(crate) fn take(&self, len: usize, value: T, clear: bool) -> Buffer<T> {
        if len == 0 {
            return Buffer::default();
        }
        let capacity = len.next_power_of_two();
        let mut store = self.0.lock().unwrap_or_else(|error| error.into_inner());
        let reused = store.idle.get_mut(&capacity).and_then(Vec::pop);
        #[cfg(test)]
        if reused.is_none() {
            store.allocations += 1;
        }
        drop(store);
        let needs_clear = clear && reused.is_some();
        let mut values = reused.unwrap_or_else(|| vec![value.clone(); capacity]);
        values.resize(len, value.clone());
        if needs_clear {
            values.fill(value);
        }
        Buffer {
            values,
            pool: Some(self.clone()),
        }
    }
}
impl<T> BufferPool<T> {
    #[cfg(test)]
    pub(crate) fn inventory(&self) -> BufferInventory {
        let store = self.0.lock().unwrap();
        BufferInventory {
            allocations: store.allocations,
            buffers: store.idle.values().map(Vec::len).sum(),
            bytes: store
                .idle
                .values()
                .flatten()
                .map(|values| values.capacity() * size_of::<T>())
                .sum(),
        }
    }
    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn dirty(&self, value: T)
    where
        T: Clone,
    {
        for buffer in self.0.lock().unwrap().idle.values_mut().flatten() {
            buffer.fill(value.clone());
        }
    }
}

/// Owned initialized values with an optional workspace-pool lease.
///
/// The lease follows stage ownership; an Arc of a lease returns on its last drop.
/// Dereferencing exposes an ordinary initialized Vec for existing arithmetic.
pub(crate) struct Buffer<T> {
    values: Vec<T>,
    pool: Option<BufferPool<T>>,
}
impl<T> Default for Buffer<T> {
    fn default() -> Self {
        Vec::new().into()
    }
}
impl<T> From<Vec<T>> for Buffer<T> {
    fn from(values: Vec<T>) -> Self {
        Self { values, pool: None }
    }
}
impl<T> Drop for Buffer<T> {
    fn drop(&mut self) {
        if let Some(pool) = &self.pool
            && self.values.capacity() != 0
        {
            pool.0
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .idle
                .entry(self.values.capacity())
                .or_default()
                .push(core::mem::take(&mut self.values));
        }
    }
}
impl<T> Deref for Buffer<T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Vec<T> {
        &self.values
    }
}
impl<T> DerefMut for Buffer<T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        &mut self.values
    }
}
impl<T: Clone> Clone for Buffer<T> {
    /// Clones all elements into separate storage, unlike [`super::storage::Column::clone`].
    ///
    /// A nonempty pooled buffer leases storage from the same pool, potentially
    /// reusing an idle allocation. Empty or unpooled buffers produce unpooled clones.
    fn clone(&self) -> Self {
        match (&self.pool, self.first()) {
            (Some(pool), Some(value)) => {
                let mut result = pool.take(self.len(), value.clone(), false);
                result.clone_from_slice(self);
                result
            }
            _ => self.values.clone().into(),
        }
    }
}
impl<T: fmt::Debug> fmt::Debug for Buffer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.values.fmt(f)
    }
}
impl<T: PartialEq> PartialEq for Buffer<T> {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}
impl<T: PartialEq> PartialEq<Vec<T>> for Buffer<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        self.values == *other
    }
}
impl<T> AsRef<[T]> for Buffer<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}
impl<'a, T> IntoIterator for &'a Buffer<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a, T> IntoIterator for &'a mut Buffer<T> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
// Arithmetic fields are Copy. Keep the lease alive until iteration finishes,
// instead of transferring its allocation to Vec::IntoIter and losing reuse.
pub(crate) struct IntoIter<T> {
    buffer: Buffer<T>,
    range: core::ops::Range<usize>,
}
impl<T: Copy> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.range.next().map(|index| self.buffer[index])
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}
impl<T: Copy> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.range.next_back().map(|index| self.buffer[index])
    }
}
impl<T: Copy> ExactSizeIterator for IntoIter<T> {}
impl<T: Copy> IntoIterator for Buffer<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        let range = 0..self.len();
        IntoIter {
            buffer: self,
            range,
        }
    }
}

impl<T> FromIterator<T> for Buffer<T> {
    fn from_iter<I: IntoIterator<Item = T>>(values: I) -> Self {
        values.into_iter().collect::<Vec<_>>().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native::storage::Column;

    #[test]
    fn last_reader_returns_initialized_storage() {
        let pool = BufferPool::default();
        let mut buffer = pool.take(128, 0u64, true);
        assert!(buffer.iter().all(|&value| value == 0));
        buffer.fill(17);
        let column = Column::new(buffer);
        let reader = column.clone();
        drop(column);
        assert_eq!(pool.inventory().buffers, 0);
        drop(reader);
        assert_eq!(
            pool.inventory(),
            BufferInventory {
                allocations: 1,
                buffers: 1,
                bytes: 1024,
            }
        );
        let buffer = pool.take(128, 0, false);
        assert!(buffer.iter().all(|&value| value == 17));
        drop(buffer);
        let buffer = pool.take(128, 0, true);
        assert!(buffer.iter().all(|&value| value == 0));
        assert_eq!(pool.inventory().allocations, 1);
    }

    #[test]
    fn errors_and_unwinding_release_leases() {
        let pool = BufferPool::default();
        let result = std::panic::catch_unwind(|| {
            let _buffer = pool.take(8, 0u64, true);
            panic!("failed job");
        });
        assert!(result.is_err());
        assert_eq!(
            pool.inventory(),
            BufferInventory {
                allocations: 1,
                buffers: 1,
                bytes: 64,
            }
        );
        let mut buffer = pool.take(8, 0, false);
        buffer.fill(17);
        buffer.truncate(3);
        drop(buffer);
        let buffer = pool.take(8, 5, true);
        assert_eq!(&*buffer, &[5; 8]);
        assert_eq!(pool.inventory().allocations, 1);
        let fresh = BufferPool::default().take(4, 7u64, true);
        assert_eq!(&*fresh, &[7; 4]);
    }
}
