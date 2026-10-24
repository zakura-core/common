//! Polynomial columns backed by embedded data or shared stage storage.
use super::buffer::Buffer;
use alloc::{sync::Arc, vec::Vec};
use core::{fmt, ops::Deref};

/// Read-only values whose clones share their backing storage.
pub(crate) enum Column<T: 'static> {
    Static(&'static [T]),
    Owned(Arc<Buffer<T>>),
    Shared(Arc<Vec<T>>),
}
impl<T> Column<T> {
    pub(crate) fn new(values: impl Into<Buffer<T>>) -> Self {
        Self::Owned(Arc::new(values.into()))
    }
    #[cfg(all(test, feature = "prover"))]
    pub(crate) fn as_slice(&self) -> &[T] {
        self
    }
    /// Consumes this handle to recover mutable storage without copying elements.
    ///
    /// [`Self::Static`] always returns `None`. Arc-backed storage is recovered
    /// only when this handle is the sole strong owner. On failure, the consumed
    /// handle is dropped and is not returned.
    ///
    /// [`Self::Owned`] returns its original [`Buffer`], including any pool lease;
    /// [`Self::Shared`] moves its [`Vec`] into an unpooled buffer.
    #[cfg(feature = "prover")]
    pub(crate) fn into_unique(self) -> Option<Buffer<T>> {
        match self {
            Self::Static(_) => None,
            Self::Owned(v) => Arc::try_unwrap(v).ok(),
            Self::Shared(v) => Arc::try_unwrap(v).ok().map(Buffer::from),
        }
    }
}
impl<T> Clone for Column<T> {
    /// Shares the static slice or clones the Arc handle without copying elements.
    /// See [`Buffer::clone`] for an element copy into separate storage.
    fn clone(&self) -> Self {
        match self {
            Self::Static(v) => Self::Static(v),
            Self::Owned(v) => Self::Owned(Arc::clone(v)),
            Self::Shared(v) => Self::Shared(Arc::clone(v)),
        }
    }
}
impl<T> Default for Column<T> {
    fn default() -> Self {
        Self::Static(&[])
    }
}
impl<T> Deref for Column<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            Self::Static(v) => v,
            Self::Owned(v) => v,
            Self::Shared(v) => v,
        }
    }
}
impl<T> AsRef<[T]> for Column<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}
impl<'a, T> IntoIterator for &'a Column<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<T> From<Vec<T>> for Column<T> {
    fn from(v: Vec<T>) -> Self {
        Self::new(v)
    }
}
impl<T> From<Arc<Vec<T>>> for Column<T> {
    fn from(v: Arc<Vec<T>>) -> Self {
        Self::Shared(v)
    }
}
impl<T> From<Arc<Buffer<T>>> for Column<T> {
    fn from(v: Arc<Buffer<T>>) -> Self {
        Self::Owned(v)
    }
}
impl<T> From<&'static [T]> for Column<T> {
    fn from(v: &'static [T]) -> Self {
        Self::Static(v)
    }
}
impl<T: PartialEq> PartialEq for Column<T> {
    fn eq(&self, r: &Self) -> bool {
        **self == **r
    }
}
impl<T: Eq> Eq for Column<T> {}
impl<T: PartialEq> PartialEq<Vec<T>> for Column<T> {
    fn eq(&self, r: &Vec<T>) -> bool {
        **self == **r
    }
}
impl<T: PartialEq> PartialEq<[T]> for Column<T> {
    fn eq(&self, r: &[T]) -> bool {
        **self == *r
    }
}
impl<T: fmt::Debug> fmt::Debug for Column<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}
