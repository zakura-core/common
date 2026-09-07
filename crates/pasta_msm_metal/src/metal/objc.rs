//! A minimal, dependency-free bridge to the Objective-C runtime and the
//! handful of Metal and Foundation calls the backend needs.
//!
//! The crate deliberately links the system frameworks directly instead of
//! pulling in binding crates: the supply-chain policy of this workspace
//! audits every dependency, and the backend uses about twenty selectors.
//! Every call goes through `objc_msgSend` cast to the exact C signature of
//! the method, which is the documented calling convention on Apple
//! AArch64 (no `_stret`/`_fpret` variants exist there — this module is
//! compiled only for `aarch64`, see `lib.rs`).
//!
//! Memory management follows manual retain/release: objects returned by
//! `new…`/`Create…` calls are owned and released by [`Object`]'s `Drop`;
//! objects returned by other methods are autoreleased, so every sequence
//! of such calls runs inside an [`AutoreleasePool`].

use std::ffi::{CStr, c_char, c_void};
use std::mem::transmute;

/// An Objective-C object pointer (`id`).
pub type Id = *mut c_void;
/// A selector (`SEL`).
pub type Sel = *const c_void;

/// `MTLSize`: a three-dimensional extent of `NSUInteger`s.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct MtlSize {
    /// Width.
    pub width: usize,
    /// Height.
    pub height: usize,
    /// Depth.
    pub depth: usize,
}

impl MtlSize {
    /// A one-dimensional extent.
    pub fn linear(width: usize) -> Self {
        MtlSize {
            width,
            height: 1,
            depth: 1,
        }
    }
}

/// `MTLResourceStorageModeShared | MTLResourceCPUCacheModeDefaultCache`:
/// unified memory visible to the CPU and the GPU.
pub const RESOURCE_OPTIONS_SHARED: usize = 0;
/// `MTLCommandBufferStatusCompleted`.
pub const COMMAND_BUFFER_STATUS_COMPLETED: usize = 4;

#[link(name = "objc", kind = "dylib")]
unsafe extern "C" {
    fn objc_getClass(name: *const c_char) -> Id;
    fn sel_registerName(name: *const c_char) -> Sel;
    fn objc_msgSend();
    fn objc_autoreleasePoolPush() -> *mut c_void;
    fn objc_autoreleasePoolPop(pool: *mut c_void);
}

// Foundation supplies NSString; CoreGraphics must be linked for
// `MTLCreateSystemDefaultDevice` to find a device on macOS.
#[link(name = "Foundation", kind = "framework")]
unsafe extern "C" {}

#[link(name = "CoreGraphics", kind = "framework")]
unsafe extern "C" {}

#[link(name = "Metal", kind = "framework")]
unsafe extern "C" {
    fn MTLCreateSystemDefaultDevice() -> Id;
}

/// Registers (or looks up) a selector.
pub fn sel(name: &CStr) -> Sel {
    // SAFETY: `name` is a valid NUL-terminated string; the runtime copies it.
    unsafe { sel_registerName(name.as_ptr()) }
}

/// Looks up a class by name; null if it does not exist.
pub fn class(name: &CStr) -> Id {
    // SAFETY: as for `sel`.
    unsafe { objc_getClass(name.as_ptr()) }
}

/// The system default Metal device, owned (+1), or null.
pub fn create_system_default_device() -> Id {
    // SAFETY: a plain C function with no preconditions.
    unsafe { MTLCreateSystemDefaultDevice() }
}

macro_rules! msg_send {
    ($name:ident, ($($arg:ident : $ty:ty),*) -> $ret:ty) => {
        /// Sends a message with this argument and return signature.
        ///
        /// # Safety
        ///
        /// `receiver` must be a live object (or null, which returns a zero
        /// value), and `selector` must name a method with exactly this C
        /// signature.
        pub unsafe fn $name(receiver: Id, selector: Sel $(, $arg: $ty)*) -> $ret {
            // SAFETY: the caller guarantees the signature matches the
            // method; `objc_msgSend` is a trampoline that forwards its
            // registers to the implementation, so calling it through a
            // pointer of the method's own type is the supported convention.
            unsafe {
                let send: unsafe extern "C" fn(Id, Sel $(, $ty)*) -> $ret =
                    transmute(objc_msgSend as unsafe extern "C" fn());
                send(receiver, selector $(, $arg)*)
            }
        }
    };
}

msg_send!(send_id, () -> Id);
msg_send!(send_void, () -> ());
msg_send!(send_usize, () -> usize);
msg_send!(send_cstr, () -> *const c_char);
msg_send!(send_id_id, (a: Id) -> Id);
msg_send!(send_void_id, (a: Id) -> ());
msg_send!(send_library, (source: Id, options: Id, error: *mut Id) -> Id);
msg_send!(send_pipeline, (function: Id, error: *mut Id) -> Id);
msg_send!(send_buffer_bytes, (bytes: *const c_void, length: usize, options: usize) -> Id);
msg_send!(send_buffer_length, (length: usize, options: usize) -> Id);
msg_send!(send_set_buffer, (buffer: Id, offset: usize, index: usize) -> ());
msg_send!(send_dispatch, (threads: MtlSize, per_threadgroup: MtlSize) -> ());

/// An owned (+1) Objective-C object, released on drop.
#[derive(Debug)]
pub struct Object(Id);

impl Object {
    /// Takes ownership of a +1 reference; `None` if `id` is null.
    pub fn owned(id: Id) -> Option<Object> {
        (!id.is_null()).then_some(Object(id))
    }

    /// The raw pointer, for message sends.
    pub fn id(&self) -> Id {
        self.0
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        // SAFETY: we hold a +1 reference and give it up exactly once.
        unsafe { send_void(self.0, sel(c"release")) }
    }
}

/// An autorelease pool scope.
#[derive(Debug)]
pub struct AutoreleasePool(*mut c_void);

impl AutoreleasePool {
    /// Pushes a pool; popped on drop.
    pub fn push() -> Self {
        // SAFETY: push/pop are balanced by `Drop`.
        AutoreleasePool(unsafe { objc_autoreleasePoolPush() })
    }
}

impl Drop for AutoreleasePool {
    fn drop(&mut self) {
        // SAFETY: the token came from `objc_autoreleasePoolPush`.
        unsafe { objc_autoreleasePoolPop(self.0) }
    }
}

/// An autoreleased `NSString` for `text` (valid inside the current pool).
pub fn nsstring(text: &CStr) -> Id {
    let class = class(c"NSString");
    // SAFETY: `stringWithUTF8String:` takes a `const char*` and returns an
    // autoreleased `NSString*` (or nil).
    unsafe { send_id_id(class, sel(c"stringWithUTF8String:"), text.as_ptr() as Id) }
}

/// The UTF-8 contents of an `NSString`, or a placeholder if null.
pub fn string_contents(nsstring: Id) -> String {
    if nsstring.is_null() {
        return String::from("<null>");
    }
    // SAFETY: `UTF8String` returns a pointer valid for the string's
    // lifetime within the current autorelease pool; copied immediately.
    unsafe {
        let pointer = send_cstr(nsstring, sel(c"UTF8String"));
        if pointer.is_null() {
            String::from("<null>")
        } else {
            CStr::from_ptr(pointer).to_string_lossy().into_owned()
        }
    }
}

/// `[error localizedDescription]` as a `String`.
pub fn error_description(error: Id) -> String {
    if error.is_null() {
        return String::from("unknown error");
    }
    // SAFETY: `localizedDescription` returns an autoreleased NSString.
    let description = unsafe { send_id(error, sel(c"localizedDescription")) };
    string_contents(description)
}
